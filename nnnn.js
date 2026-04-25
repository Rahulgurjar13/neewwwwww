const express = require('express');
const router = express.Router();
const Device = require('../models/Device');
const Transaction = require('../models/Transaction');
const User = require('../models/User');
const auth = require('../middleware/auth');
const { body, param, query, validationResult } = require('express-validator');
const retry = require('async-retry');
const rebuildChartFromTransaction = require('../utils/rebuildChartFromTransaction');
const updateChartDaily = require('../utils/updateChartDaily');
const ChartDaily = require('../models/ChartDaily');
const rateLimit = require('express-rate-limit');
const { istRangeUTC, istTodayStartUTC } = require('../utils/time');
const mongoose = require('mongoose');
const {
  logger,
  attachDependencies,
  throttle,
  getDeviceQuery,
  getLatestStatus,
  computeTransactionSum,
  calculateTotalPads,
  emitDeviceEvent,
} = require('../utilis/utils');
const IST_OFFSET_MS = 330 * 60 * 1000; // +05:30

const getTodayISTString = () =>
  new Date(Date.now() + IST_OFFSET_MS).toISOString().slice(0, 10);


const IST_OFFSET_MIN = 330;

function istTodayTillNowUTC() {
  const nowUTC = new Date();

  const nowIST = new Date(
    nowUTC.getTime() + IST_OFFSET_MIN * 60 * 1000
  );

  const startIST = new Date(
    nowIST.getFullYear(),
    nowIST.getMonth(),
    nowIST.getDate()
  );

  return {
    startUTC: new Date(startIST.getTime() - IST_OFFSET_MIN * 60 * 1000),
    endUTC: nowUTC,
  };
}


// Rate Limiter
const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 minutes
  max: 10000,
  message: { success: false, error: 'Too many requests, please try again later' },
  standardHeaders: true,
  legacyHeaders: false,
});

// Valid device statuses
const validStatuses = ['installed', 'instock', 'demo', 'damaged', 'replaced'];

// Restrict access by role
const restrictTo = (roles) => (req, res, next) => {
  if (!req.user || !roles.includes(req.user.role)) {
    logger.warn(`Unauthorized access by user ${req.user?.email || 'unknown'} with role ${req.user?.role || 'none'}`, {
      requestId: req.id,
    });
    return res.status(403).json({ success: false, error: 'Insufficient role permissions' });
  }
  next();
};

// Apply dependencies middleware
router.use(attachDependencies);


// FAST REPORTS (3–10ms)
router.get('/reports-fast', auth, async (req, res) => {
  const redis = req.redisClient;
  const { role, _id } = req.user;

  const date = new Date().toLocaleDateString('en-CA', {
    timeZone: 'Asia/Kolkata',
  });

  if (!date) {
    return res.status(400).json({ success: false, error: 'date required (YYYY-MM-DD)' });
  }

  const scope =
    role === 'admin'
      ? 'admin'
      : `${role}:${_id}`;

  const key = `report:${date}:${scope}`;
  const data = await redis.hgetall(key);

  if (!data || Object.keys(data).length === 0) {
    return res.json({ success: true, data: [], total: 0 });
  }

  const page = parseInt(req.query.page) || 1;
  const limit = parseInt(req.query.limit) || 20;
  const skip = (page - 1) * limit;

  const entries = Object.entries(data)
    .map(([clientId, count]) => ({ clientId, dispensed: +count }))
    .sort((a, b) => b.dispensed - a.dispensed);

  res.json({
    success: true,
    data: entries.slice(skip, skip + limit),
    pagination: {
      page,
      limit,
      total: entries.length,
    },
  });
});


// GET: Device statistics for all devices
router.get(
  "/stats",
  auth,
  apiLimiter,
  async (req, res) => {
    const requestId = req.id;

    try {
      /* ----------------------------------------------------
         1. REDIS CACHE
      ---------------------------------------------------- */
      const cacheKey = `stats:v4:${req.user.role}:${req.user._id}`;
      const cached = await req.redisClient.get(cacheKey);
      if (cached) return res.json(JSON.parse(cached));

      /* ----------------------------------------------------
         2. DEVICE SCOPE
      ---------------------------------------------------- */
      let deviceQuery = {};
      let acquired = 0;

      if (req.user.role !== "admin") {
        const users = await User.find({
          $or: [{ _id: req.user._id }, { createdBy: req.user._id }],
        }).select("_id acquired").lean();

        const userIds = users.map(u => u._id);

        deviceQuery = {
          $or: [
            { createdBy: { $in: userIds } },
            { assignedUser: { $in: userIds } },
          ],
        };

        acquired = users.reduce((s, u) => s + (u.acquired || 0), 0);
      }

      /* ----------------------------------------------------
    3. IST DAY WINDOWS (CORRECT & SAFE)
 ---------------------------------------------------- */


      const IST_OFFSET = 330 * 60 * 1000; // ms

      const nowUTC = new Date();

      // Shift to IST moment
      const nowIST = new Date(nowUTC.getTime() + IST_OFFSET);

      // Extract IST date parts USING UTC getters (important!)
      const istYear = nowIST.getUTCFullYear();
      const istMonth = nowIST.getUTCMonth();
      const istDate = nowIST.getUTCDate();

      // Build IST midnight in UTC
      const todayStart = new Date(
        Date.UTC(istYear, istMonth, istDate) - IST_OFFSET
      );

      const tomorrowStart = new Date(todayStart.getTime() + 24 * 60 * 60 * 1000);
      const yesterdayStart = new Date(todayStart.getTime() - 24 * 60 * 60 * 1000);


      /* ----------------------------------------------------
         4. LAST WEEK (MON → MON, IST ALIGNED)
      ---------------------------------------------------- */
      const dayOfWeek = todayStart.getUTCDay() || 7; // Mon=1 ... Sun=7

      const thisWeekStart = new Date(todayStart);
      thisWeekStart.setUTCDate(thisWeekStart.getUTCDate() - (dayOfWeek - 1));

      const lastWeekStart = new Date(thisWeekStart);
      lastWeekStart.setUTCDate(lastWeekStart.getUTCDate() - 7);

      const lastWeekEnd = new Date(thisWeekStart);

      /* ----------------------------------------------------
         5. MONTH / YEAR WINDOWS (UTC SAFE)
      ---------------------------------------------------- */
      const lastMonthStart = new Date(
        Date.UTC(nowUTC.getUTCFullYear(), nowUTC.getUTCMonth() - 1, 1)
      );
      const lastMonthEnd = new Date(
        Date.UTC(nowUTC.getUTCFullYear(), nowUTC.getUTCMonth(), 1)
      );

      const last3Months = new Date(todayStart);
      last3Months.setUTCMonth(last3Months.getUTCMonth() - 3);

      const lastYearStart = new Date(
        Date.UTC(nowUTC.getUTCFullYear() - 1, 0, 1)
      );
      const lastYearEnd = new Date(
        Date.UTC(nowUTC.getUTCFullYear(), 0, 1)
      );

      const fyYear =
        nowUTC.getUTCMonth() >= 3
          ? nowUTC.getUTCFullYear()
          : nowUTC.getUTCFullYear() - 1;

      const academicYearStart = new Date(Date.UTC(fyYear, 3, 1));
      const academicYearEnd = new Date(Date.UTC(fyYear + 1, 3, 1));

      /* ----------------------------------------------------
         6. DEVICE METRICS
      ---------------------------------------------------- */
      const [
        deviceCount,
        statusAgg,
        onlineAgg,
        lowStock,
        devices,
      ] = await Promise.all([
        Device.countDocuments(deviceQuery),
        Device.aggregate([
          { $match: deviceQuery },
          { $group: { _id: "$status", count: { $sum: 1 } } },
        ]),
        Device.aggregate([
          { $match: deviceQuery },
          { $group: { _id: "$latestStatus", count: { $sum: 1 } } },
        ]),
        Device.countDocuments({ ...deviceQuery, padsRemaining: { $lte: 10 } }),
        Device.find(deviceQuery).select("clientId").lean(),
      ]);

      const deviceIds = devices.map(d => d.clientId);

      /* ----------------------------------------------------
         7. CHARTDAILY AGGREGATION (Excel-reconciled source of truth)
            Today's live count still comes from Transaction
      ---------------------------------------------------- */
      let statsAgg = {};

      // Helper: convert UTC Date boundary → IST date string (YYYY-MM-DD)
      const toISTDateStr = d => {
        const ist = new Date(d.getTime() + (5 * 60 + 30) * 60 * 1000);
        return ist.toISOString().slice(0, 10);
      };

      const todayStr      = toISTDateStr(todayStart);
      const yesterdayStr  = toISTDateStr(yesterdayStart);
      const lastWeekSStr  = toISTDateStr(lastWeekStart);
      const lastWeekEStr  = toISTDateStr(lastWeekEnd);
      const lastMonthSStr = toISTDateStr(lastMonthStart);
      const lastMonthEStr = toISTDateStr(lastMonthEnd);
      const last3MStr     = toISTDateStr(last3Months);
      const lastYearSStr  = toISTDateStr(lastYearStart);
      const lastYearEStr  = toISTDateStr(lastYearEnd);
      const acYearSStr    = toISTDateStr(academicYearStart);
      const acYearEStr    = toISTDateStr(academicYearEnd);

      if (deviceIds.length) {
        const cdIds = deviceIds.map(id => String(id).toLowerCase());

        // Historical stats from ChartDaily (Excel-reconciled, accurate)
        const cdAgg = await ChartDaily.aggregate([
          {
            $match: {
              deviceId: { $in: cdIds },
              username: { $exists: true, $ne: '' },
            },
          },
          {
            $group: {
              _id: null,
              total:        { $sum: '$dispensed' },
              yesterday:    { $sum: { $cond: [{ $eq:  ['$date', yesterdayStr]  }, '$dispensed', 0] } },
              lastWeek:     { $sum: { $cond: [{ $and: [{ $gte: ['$date', lastWeekSStr]  }, { $lt: ['$date', lastWeekEStr]  }] }, '$dispensed', 0] } },
              lastMonth:    { $sum: { $cond: [{ $and: [{ $gte: ['$date', lastMonthSStr] }, { $lt: ['$date', lastMonthEStr] }] }, '$dispensed', 0] } },
              last3Months:  { $sum: { $cond: [{ $gte: ['$date', last3MStr]    }, '$dispensed', 0] } },
              lastYear:     { $sum: { $cond: [{ $and: [{ $gte: ['$date', lastYearSStr]  }, { $lt: ['$date', lastYearEStr]  }] }, '$dispensed', 0] } },
              academicYear: { $sum: { $cond: [{ $and: [{ $gte: ['$date', acYearSStr]    }, { $lt: ['$date', acYearEStr]    }] }, '$dispensed', 0] } },
            },
          },
        ]);
        statsAgg = cdAgg[0] || {};

        // Today's live count from Transaction (real-time IoT, not yet in ChartDaily)
        try {
          const todayTx = await Transaction.aggregate([
            {
              $match: {
                DeviceId: { $in: deviceIds },
                status: 'dispensed',
                myts: { $gte: todayStart, $lt: tomorrowStart },
              },
            },
            { $group: { _id: null, count: { $sum: '$dispensedCount' } } },
          ]);
          statsAgg.today = todayTx[0]?.count || 0;
        } catch (_) {
          statsAgg.today = 0;
        }
      }

      /* ----------------------------------------------------
         8. FINAL RESPONSE
      ---------------------------------------------------- */
      const stats = {
        deviceCount,
        installed: 0,
        instock: 0,
        demo: 0,
        damaged: 0,     // ✅ correct
        replaced: 0,    // ✅ correct
        online: 0,
        offline: 0,
        lowStock,
        acquired,

        totalDispensed: statsAgg.total || 0,
        todayPads: statsAgg.today || 0,
        yesterdayPads: statsAgg.yesterday || 0,
        lastWeek: statsAgg.lastWeek || 0,
        lastMonth: statsAgg.lastMonth || 0,
        last3Months: statsAgg.last3Months || 0,
        lastYear: statsAgg.lastYear || 0,
        academicYear: statsAgg.academicYear || 0,
      };


      statusAgg.forEach(s => {
        if (stats[s._id] !== undefined) stats[s._id] = s.count;
      });

      onlineAgg.forEach(s => {
        if (s._id === "online") stats.online = s.count;
        if (s._id === "offline") stats.offline = s.count;
      });

      const response = { success: true, data: stats };

      await req.redisClient.setex(cacheKey, 120, JSON.stringify(response));
      return res.json(response);

    } catch (err) {
      logger.error("Stats API error", {
        requestId,
        error: err.message,
        stack: err.stack,
      });
      return res.status(500).json({
        success: false,
        error: "Failed to fetch stats",
      });
    }
  }
);

router.get('/reports-v3-fast', auth, async (req, res) => {
  try {
    let { startDate, endDate, createdBy } = req.query;

    /* ----------------------------------------------------
       1. DEVICE SCOPE
    ---------------------------------------------------- */
    let deviceQuery = await getDeviceQuery(req);

    if (req.user.role === 'admin' && createdBy) {
      deviceQuery.createdBy = createdBy;
    }

    const devices = await Device.find(deviceQuery)
      .select('clientId username city division location totalDispensed assignedUser')
      .populate('assignedUser', 'name')
      .lean();

    const deviceIds = devices.map(d => d.clientId);

    /* ----------------------------------------------------
       2. DATE NORMALIZATION (IST)
    ---------------------------------------------------- */

    if (startDate && !endDate) endDate = startDate;
    if (!startDate && endDate) startDate = endDate;

    if (!startDate && !endDate) {
      const todayIST = new Date().toLocaleDateString('en-CA', {
        timeZone: 'Asia/Kolkata',
      });
      startDate = todayIST;
      endDate = todayIST;
    }

    const todayIST = new Date().toLocaleDateString('en-CA', {
      timeZone: 'Asia/Kolkata',
    });

    const isToday = startDate === endDate && startDate === todayIST;
    const rangeMap = new Map();
    let totalDispensedInRange = 0;

    // ChartDaily stores deviceId in lowercase; normalize to match
    const deviceIdsLower = deviceIds.map(id => (id || '').toLowerCase());

    if (isToday) {
      /* ── TODAY → ChartDaily (same source as Dashboard, avoids mismatch) ── */
      const rows = await ChartDaily.find({
        deviceId: { $in: deviceIdsLower },
        date:     todayIST,
      }).select('deviceId dispensed').lean();

      for (const r of rows) {
        rangeMap.set(r.deviceId, r.dispensed || 0);
        totalDispensedInRange += r.dispensed || 0;
      }

    } else {
      /* ── HISTORICAL RANGE → ChartDaily ── */
      const chartEnd = endDate >= todayIST
        ? new Date(new Date(todayIST) - 86400000).toLocaleDateString('en-CA', { timeZone: 'Asia/Kolkata' })
        : endDate;

      if (startDate <= chartEnd) {
        const rows = await ChartDaily.aggregate([
          { $match: { deviceId: { $in: deviceIdsLower }, date: { $gte: startDate, $lte: chartEnd } } },
          { $group: { _id: '$deviceId', dispensed: { $sum: '$dispensed' } } },
        ]);
        for (const r of rows) {
          const prev = rangeMap.get(r._id) || 0;
          rangeMap.set(r._id, prev + (r.dispensed || 0));
          totalDispensedInRange += r.dispensed || 0;
        }
      }

      // If range includes today, add live today data from ChartDaily on top
      if (endDate >= todayIST) {
        const todayRows = await ChartDaily.find({
          deviceId: { $in: deviceIdsLower },
          date:     todayIST,
        }).select('deviceId dispensed').lean();

        for (const r of todayRows) {
          const prev = rangeMap.get(r.deviceId) || 0;
          rangeMap.set(r.deviceId, prev + (r.dispensed || 0));
          totalDispensedInRange += r.dispensed || 0;
        }
      }
    }


    return res.json({
      success: true,
      data: {
        timezone: 'Asia/Kolkata',
        range: { startDate, endDate, mode: isToday ? 'till-now' : 'full-range' },
        devices: devices.map(d => ({
          clientId:          d.clientId,
          username:          d.username,
          city:              d.city,
          division:          d.division,
          location:          d.location,
          assignedUserName:  d.assignedUser?.name || 'Unassigned',
          lifetimeDispensed: d.totalDispensed || 0,
          dispensedInRange:  rangeMap.get(d.clientId) ?? rangeMap.get((d.clientId || '').toLowerCase()) ?? 0,
        })),
        totals: { dispensedInRange: totalDispensedInRange },
      },
    });

  } catch (err) {
    console.error('reports-v3-fast error', err);
    return res.status(500).json({ success: false });
  }
});

router.get(
  "/fast-stats",
  auth,
  apiLimiter,
  async (req, res) => {
    const requestId = req.id;

    try {
      /* ---------------- REDIS CACHE ---------------- */
      const cacheKey = `faststats:v1:${req.user.role}:${req.user._id}`;
      const cached = await req.redisClient.get(cacheKey);
      if (cached) return res.json(JSON.parse(cached));

      /* ---------------- DEVICE SCOPE ---------------- */
      let deviceQuery = {};
      let acquired = 0;

      if (req.user.role !== "admin") {
        const users = await User.find({
          $or: [{ _id: req.user._id }, { createdBy: req.user._id }],
        }).select("_id acquired").lean();

        const userIds = users.map(u => u._id);

        deviceQuery = {
          $or: [
            { createdBy: { $in: userIds } },
            { assignedUser: { $in: userIds } },
          ],
        };

        acquired = users.reduce((s, u) => s + (u.acquired || 0), 0);
      }

      /* ---------------- IST TIME ---------------- */

      const IST_OFFSET = 5.5 * 60 * 60 * 1000;
      const nowUTC = new Date();
      const nowIST = new Date(nowUTC.getTime() + IST_OFFSET);

      const year = nowIST.getUTCFullYear();
      const month = nowIST.getUTCMonth();
      const date = nowIST.getUTCDate();

      const todayStart = new Date(
        Date.UTC(year, month, date) - IST_OFFSET
      );

      const yesterdayStart = new Date(todayStart.getTime() - 86400000);
      const lastWeek = new Date(todayStart);
      lastWeek.setUTCDate(lastWeek.getUTCDate() - 7);

      const lastMonth = new Date(todayStart);
      lastMonth.setUTCMonth(lastMonth.getUTCMonth() - 1);

      const last3Months = new Date(todayStart);
      last3Months.setUTCMonth(last3Months.getUTCMonth() - 3);

      const lastYear = new Date(todayStart);
      lastYear.setUTCFullYear(lastYear.getUTCFullYear() - 1);

      const fyYear = month >= 3 ? year : year - 1;
      const academicYearStart = new Date(
        Date.UTC(fyYear, 3, 1) - IST_OFFSET
      );

      /* ---------------- DEVICE METRICS ---------------- */

      const [
        deviceCount,
        statusAgg,
        onlineAgg,
        lowStock,
        totalDispensedAgg
      ] = await Promise.all([
        Device.countDocuments(deviceQuery),
        Device.aggregate([
          { $match: deviceQuery },
          { $group: { _id: "$status", count: { $sum: 1 } } },
        ]),
        Device.aggregate([
          { $match: deviceQuery },
          { $group: { _id: "$latestStatus", count: { $sum: 1 } } },
        ]),
        Device.countDocuments({
          ...deviceQuery,
          padsRemaining: { $lte: 10 },
        }),
        Device.aggregate([
          { $match: deviceQuery },
          { $group: { _id: null, total: { $sum: "$totalDispensed" } } },
        ]),
      ]);

      /* ---------------- DAILY STATS (from ChartDaily — same source as dashboard) ---------------- */

      const format = (d) => new Date(d).toLocaleDateString('en-CA', { timeZone: 'Asia/Kolkata' });

      const todayStr = format(new Date());
      const yesterdayStr = format(new Date(Date.now() - 86400000));

      // Fetch all ChartDaily rows for the device scope within last year
      const deviceIds4Stats = (await Device.find(deviceQuery).select('clientId').lean()).map(d => d.clientId);

      const chartRows = deviceIds4Stats.length ? await ChartDaily.find({
        deviceId: { $in: deviceIds4Stats },
        date: { $gte: lastYear.toISOString().split('T')[0] },
      }).select('date dispensed').lean() : [];

      let todayPads = 0;
      let yesterdayPads = 0;
      let lastWeekTotal = 0;
      let lastMonthTotal = 0;
      let last3MonthsTotal = 0;
      let lastYearTotal = 0;
      let academicYearTotal = 0;

      chartRows.forEach(r => {
        const dDate = new Date(r.date + 'T00:00:00Z');
        const d = r.dispensed || 0;

        if (r.date === todayStr)       todayPads       += d;
        if (r.date === yesterdayStr)   yesterdayPads   += d;
        if (dDate >= lastWeek)         lastWeekTotal   += d;
        if (dDate >= lastMonth)        lastMonthTotal  += d;
        if (dDate >= last3Months)      last3MonthsTotal += d;
        if (dDate >= lastYear)         lastYearTotal   += d;
        if (dDate >= academicYearStart) academicYearTotal += d;
      });

      /* ---------------- FINAL RESPONSE ---------------- */

      const stats = {
        deviceCount,
        installed: 0,
        instock: 0,
        demo: 0,
        damaged: 0,
        replaced: 0,
        online: 0,
        offline: 0,
        lowStock,
        acquired,

        totalDispensed: totalDispensedAgg[0]?.total || 0,
        todayPads,
        yesterdayPads,
        lastWeek: lastWeekTotal,
        lastMonth: lastMonthTotal,
        last3Months: last3MonthsTotal,
        lastYear: lastYearTotal,
        academicYear: academicYearTotal
      };

      statusAgg.forEach(s => {
        if (stats[s._id] !== undefined) stats[s._id] = s.count;
      });

      onlineAgg.forEach(s => {
        if (s._id === "online") stats.online = s.count;
        if (s._id === "offline") stats.offline = s.count;
      });

      const response = { success: true, data: stats };

      await req.redisClient.setex(cacheKey, 60, JSON.stringify(response));

      return res.json(response);

    } catch (err) {
      logger.error("Fast Stats API error", {
        requestId,
        error: err.message,
        stack: err.stack,
      });

      return res.status(500).json({
        success: false,
        error: "Failed to fetch fast stats",
      });
    }
  }
);

// FAST REPORT LIST (UI ONLY)
router.get('/reports-list-fast', auth, async (req, res) => {
  try {
    const page = Number(req.query.page || 1);
    const limit = Number(req.query.limit || 10);
    const skip = (page - 1) * limit;

    const query = await getDeviceQuery(req);

    const [devices, total] = await Promise.all([
      Device.find(query)
        .select('clientId username city division location totalDispensed')
        .sort({ totalDispensed: -1, clientId: 1 })
        .skip(skip)
        .limit(limit)
        .lean(),
      Device.countDocuments(query),
    ]);

    res.json({
      success: true,
      data: devices.map(d => ({
        clientId: d.clientId,
        machineNumber: d.username,
        city: d.city,
        division: d.division,
        location: d.location,
        totalPads: d.totalDispensed ?? 0, // field name kept for frontend compatibility
      })),
      pagination: { page, limit, total },
    });
  } catch (err) {
    res.status(500).json({ success: false });
  }
});

// GET : List device 

router.get('/list-fast', auth, apiLimiter, async (req, res) => {
  try {
    const query = await getDeviceQuery(req);

    let { status } = req.query;

    /* --------------------------------------------------
       1️⃣ STATUS FILTER (FIXED)
    -------------------------------------------------- */

    if (status) {
      // Support multiple status: ?status=installed,damaged
      if (typeof status === 'string' && status.includes(',')) {
        const statusArray = status.split(',').map(s => s.trim());
        query.status = { $in: statusArray };
      } else {
        query.status = status;
      }
    }
    // ❌ NO default filter → return ALL devices

    /* --------------------------------------------------
       2️⃣ FETCH DEVICES
    -------------------------------------------------- */

    const devices = await Device.find(query)
      .select(
        'clientId username city division location status ' +
        'padsRemaining totalDispensed refillEvents latestStatus lastPingAt assignedUser'
      )
      .populate('assignedUser', 'name email')
      .sort({ lastPingAt: -1 })
      .lean();

    /* --------------------------------------------------
       3️⃣ RESPONSE FORMAT
    -------------------------------------------------- */

    const formatted = devices.map(d => ({
      clientId: d.clientId,
      username: d.username || '-',

      city: d.city || '-',
      division: d.division || '-',
      location: d.location || '-',

      status: d.status || 'installed',

      padsRemaining: d.padsRemaining ?? 0,
      totalPads: d.totalDispensed ?? 0,

      refillEvents: Array.isArray(d.refillEvents)
        ? d.refillEvents.length
        : d.refillEvents ?? 0,

      latestStatus: d.latestStatus || 'offline',
      lastPingAt: d.lastPingAt || null,

      assignedUser: d.assignedUser?._id || null,
      assignedUserName: d.assignedUser
        ? d.assignedUser.name || d.assignedUser.email
        : 'Unassigned',
    }));

    return res.json({
      success: true,
      total: formatted.length,
      data: formatted,
    });

  } catch (err) {
    logger.error('list-fast error', err);

    return res.status(500).json({
      success: false,
      error: 'Failed to fetch devices',
    });
  }
});

router.get("/stats-ultra-ist", auth, apiLimiter, async (req, res) => {
  try {
    const redis = req.redisClient;
    const cacheKey = `stats:ultra:v:FINAL14${req.user._id}`;

    /* ---------------- DEVICE SCOPE (ASSIGNED BASED) ---------------- */

    let baseQuery = {};
    let acquired = 0;

    if (req.user.role !== "admin") {
      const users = await User.find({
        $or: [{ _id: req.user._id }, { createdBy: req.user._id }],
      }).select("_id acquired").lean();

      const userIds = users.map((u) => u._id);

      baseQuery = {
        $or: [
          { createdBy: { $in: userIds } },
          { assignedUser: { $in: userIds } },
        ],
      };

      acquired = users.reduce((sum, u) => sum + (u.acquired || 0), 0);
    } else {
      // For admin: Total Fleet = sum of acquired across ALL users in the platform
      const allUsersAgg = await User.aggregate([
        { $group: { _id: null, total: { $sum: { $ifNull: ['$acquired', 0] } } } }
      ]);
      acquired = allUsersAgg[0]?.total || 0;
    }

    /* ---------------- DEVICE FILTERS ---------------- */

    const operationalQuery = {
      ...baseQuery,
      status: { $in: ["installed", "demo", "damaged", "replaced", "instock"] },
    };

    const installedQuery = {
      ...baseQuery,
      status: "installed",
    };

    const devicesList = await Device.find(operationalQuery)
      .select("clientId")
      .lean();

    const deviceIds = devicesList.map((d) => d.clientId);

    /* ---------------- IST DATE FIX ---------------- */

    const now = new Date(
      new Date().toLocaleString("en-US", { timeZone: "Asia/Kolkata" })
    );

    const format = (d) =>
      new Date(d).toLocaleDateString("en-CA", {
        timeZone: "Asia/Kolkata",
      });

    const todayStr = format(now);

    const yesterday = new Date(now);
    yesterday.setDate(now.getDate() - 1);

    /* ---------------- LAST WEEK (MON → SUN) ---------------- */

    const day = now.getDay();
    const diffToMonday = (day + 6) % 7;

    const currentWeekMonday = new Date(now);
    currentWeekMonday.setDate(now.getDate() - diffToMonday);

    const lastWeekStart = new Date(currentWeekMonday);
    lastWeekStart.setDate(currentWeekMonday.getDate() - 7);

    const lastWeekEnd = new Date(currentWeekMonday);
    lastWeekEnd.setDate(currentWeekMonday.getDate() - 1);

    /* ---------------- CALENDAR RANGES ---------------- */

    const lastMonthStart = new Date(now.getFullYear(), now.getMonth() - 1, 1);
    const lastMonthEnd = new Date(now.getFullYear(), now.getMonth(), 0);

    const last3Start = new Date(now.getFullYear(), now.getMonth() - 3, 1);
    const last3End = new Date(now.getFullYear(), now.getMonth(), 0);

    const lastYearStart = new Date(now.getFullYear() - 1, 0, 1);
    const lastYearEnd = new Date(now.getFullYear() - 1, 11, 31);

    const fyStartYear =
      now.getMonth() >= 3 ? now.getFullYear() : now.getFullYear() - 1;

    const fyStart = new Date(fyStartYear, 3, 1);
    const fyEnd = new Date(fyStartYear + 1, 2, 31);

    /* ---------------- AGGREGATION ---------------- */

    let totals = {};

    if (deviceIds.length) {
      const agg = await ChartDaily.aggregate([
        {
          // ✅ NO date restriction here — we need ALL history to compute
          // All Time, Last Year, FY, Last 3 Months etc. from the same source.
          $match: {
            deviceId: { $in: deviceIds },
          },
        },
        {
          $group: {
            _id: null,

            // ✅ All-time total — same source as all period buckets
            totalDispensed: { $sum: "$dispensed" },

            todayPads: {
              $sum: {
                $cond: [{ $eq: ["$date", todayStr] }, "$dispensed", 0],
              },
            },

            yesterdayPads: {
              $sum: {
                $cond: [
                  { $eq: ["$date", format(yesterday)] },
                  "$dispensed",
                  0,
                ],
              },
            },

            // ✅ FIXED LAST WEEK (MON–SUN)
            lastWeek: {
              $sum: {
                $cond: [
                  {
                    $and: [
                      { $gte: ["$date", format(lastWeekStart)] },
                      { $lte: ["$date", format(lastWeekEnd)] },
                    ],
                  },
                  "$dispensed",
                  0,
                ],
              },
            },

            lastMonth: {
              $sum: {
                $cond: [
                  {
                    $and: [
                      { $gte: ["$date", format(lastMonthStart)] },
                      { $lte: ["$date", format(lastMonthEnd)] },
                    ],
                  },
                  "$dispensed",
                  0,
                ],
              },
            },

            last3Months: {
              $sum: {
                $cond: [
                  {
                    $and: [
                      { $gte: ["$date", format(last3Start)] },
                      { $lte: ["$date", format(last3End)] },
                    ],
                  },
                  "$dispensed",
                  0,
                ],
              },
            },

            lastYear: {
              $sum: {
                $cond: [
                  {
                    $and: [
                      { $gte: ["$date", format(lastYearStart)] },
                      { $lte: ["$date", format(lastYearEnd)] },
                    ],
                  },
                  "$dispensed",
                  0,
                ],
              },
            },

            academicYear: {
              $sum: {
                $cond: [
                  {
                    $and: [
                      { $gte: ["$date", format(fyStart)] },
                      { $lte: ["$date", format(fyEnd)] },
                    ],
                  },
                  "$dispensed",
                  0,
                ],
              },
            },
          },
        },
      ]);

      totals = agg[0] || {};
    }

    // ✅ All-time total now comes from ChartDaily (same source as all other buckets)
    // This ensures All Time >= Last Year >= Last 3 Months >= Last Month (logical consistency).
    const lifetimeTotal = totals.totalDispensed || 0;

    /* ---------------- DEVICE STATUS ---------------- */

    const statusAgg = await Device.aggregate([
      { $match: baseQuery },
      { $group: { _id: "$status", count: { $sum: 1 } } },
    ]);

    let installedOnly = 0,
      instock = 0,
      demo = 0,
      damaged = 0,
      replaced = 0;

    statusAgg.forEach((s) => {
      if (s._id === "installed") installedOnly = s.count;
      if (s._id === "instock") instock = s.count;
      if (s._id === "demo") demo = s.count;
      if (s._id === "damaged") damaged = s.count;
      if (s._id === "replaced") replaced = s.count;
    });

    /* ---------------- ONLINE / OFFLINE ---------------- */

    const onlineAgg = await Device.aggregate([
      { $match: installedQuery },
      { $group: { _id: "$latestStatus", count: { $sum: 1 } } },
    ]);

    let online = 0,
      offline = 0;

    onlineAgg.forEach((s) => {
      if (s._id === "online") online = s.count;
      if (s._id === "offline") offline = s.count;
    });

    /* ---------------- LOW STOCK ---------------- */

    const lowStock = await Device.countDocuments({
      ...installedQuery,
      padsRemaining: { $lte: 10 },
    });

    /* ---------------- FINAL RESPONSE ---------------- */

    const stats = {
      deviceCount: installedOnly,
      installed: installedOnly + damaged,
      instock,
      demo,
      damaged,
      replaced,
      online,
      offline,
      lowStock,
      acquired,

      totalDispensed: lifetimeTotal, // ✅ Fix 3: authoritative lifetime total from Device model
      todayPads: totals.todayPads || 0,
      yesterdayPads: totals.yesterdayPads || 0,
      lastWeek: totals.lastWeek || 0,
      lastMonth: totals.lastMonth || 0,
      last3Months: totals.last3Months || 0,
      lastYear: totals.lastYear || 0,
      academicYear: totals.academicYear || 0,
    };

    const response = { success: true, data: stats };

    await redis.setex(cacheKey, 60, JSON.stringify(response));

    return res.json(response);
  } catch (err) {
    console.error(err);
    return res.status(500).json({ success: false });
  }
});


// unfreeze
router.put(
  '/:id/unfreeze',
  auth,
  restrictTo(['admin', 'distributor']),
  async (req, res) => {
    await Device.updateOne(
      { _id: req.params.id },
      {
        $set: {
          isFrozen: false,
          freezeReason: null,
          frozenAt: null,
          lastRefillAt: null,
        },
      }
    );


    res.json({ message: 'Device unfrozen' });
  });

// GET: Total dispensed pads in date range
router.get(
  '/all/dispensed-range',
  auth,
  apiLimiter,
  [
    query('start').isISO8601().toDate().withMessage('start must be a valid ISO8601 date'),
    query('end').isISO8601().toDate().withMessage('end must be a valid ISO8601 date'),
    query('start').custom((start, { req }) => {
      if (new Date(start) > new Date(req.query.end)) {
        throw new Error('start date must be before end date');
      }
      return true;
    }),
  ],
  async (req, res) => {
    const requestId = req.id;
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { start, end } = req.query;
      const startDate = new Date(start);
      const endDate = new Date(end);

      const deviceQuery = await getDeviceQuery(req);
      const devices = await Device.find(deviceQuery).select('clientId').lean();
      const deviceIds = devices
        .filter(d => d.clientId && typeof d.clientId === 'string')
        .map(d => d.clientId.toLowerCase());
      const { startUTC, endUTC } = istRangeUTC(start, end);

      const result = await Transaction.aggregate([
        {
          $match: {
            status: { $in: ['dispensed', 'scheduled_dispensed'] }, // ✅ Fix 2: include scheduled
            myts: { $gte: startUTC, $lt: endUTC },
            DeviceId: { $in: deviceIds },
          },
        },
        {
          $group: {
            _id: '$DeviceId',
            totalDispensed: { $sum: '$dispensedCount' },
          },
        },
      ]);

      const total = result.reduce((sum, r) => sum + r.totalDispensed, 0);

      res.json({
        success: true,
        totalDispensed: total,
        devices: result,
      });
    } catch (err) {
      logger.error(`Dispensed range error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, message: 'Server error' });
    }
  }
);

// GET: Device transactions
router.get(
  '/:clientId/transactions',
  auth,
  apiLimiter,
  [param('clientId').isString().notEmpty().withMessage('Invalid clientId')],
  async (req, res) => {
    const requestId = req.id;
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const device = await Device.findOne(query).select('_id clientId').lean();
      if (!device) {
        logger.warn(`Device not found or unauthorized: ${normalizedClientId}, user: ${req.user.email}`, { requestId });
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      const transactions = await Transaction.find({ DeviceId: normalizedClientId })
        .sort({ myts: -1 })
        .lean();

      res.json({ success: true, data: transactions });
    } catch (err) {
      logger.error(`Get transactions error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Server error fetching transactions' });
    }
  }
);


// GET: Fetch single device by clientId
router.get(
  '/:clientId',
  auth,
  apiLimiter,
  [param('clientId').isString().notEmpty().withMessage('Invalid clientId')],
  async (req, res) => {
    const requestId = req.id;
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const device = await Device.findOne(query).populate('assignedUser', 'name email role').lean();
      if (!device) {
        logger.warn(`Device not found or unauthorized: ${normalizedClientId}, user: ${req.user.email}`, { requestId });
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      const totalDispensedValue = device.totalDispensed || 0;

      res.json({
        success: true,
        data: {
          ...device,
          totalPads: totalDispensedValue,      // kept for frontend compatibility
          totalDispensed: totalDispensedValue, // canonical field
          padsRemaining: device.padsRemaining ?? 0,
          refillEvents: device.refillEvents || [],
          assignedUserName: device.assignedUser ? `${device.assignedUser.name || device.assignedUser.email} (${device.assignedUser.role || 'N/A'})` : 'Unassigned',
        },
      });
    } catch (err) {
      logger.error(`Get device error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Server error fetching device' });
    }
  }
);

// GET: Fetch devices based on user role
router.get('/', auth, apiLimiter, async (req, res) => {
  const requestId = req.id;

  try {
    const { startDate, endDate, status } = req.query;

    // ✅ FIX: include status filter in cache key — prevents serving wrong cached data
    const cacheKey = `devices:list:v1:${req.user.role}:${req.user._id}:${status || 'all'}`;
    const cached = await req.redisClient.get(cacheKey);
    if (cached) {
      return res.json(JSON.parse(cached));
    }

    let query = await getDeviceQuery(req);

    // ⭐ status filter
    if (status) {
      query.status = status;
    }

    /* ---------------- DATE FILTER ---------------- */

    if (startDate || endDate) {
      const { startUTC, endUTC } = istRangeUTC(startDate, endDate);

      const activeDeviceIds = await ChartDaily.distinct('deviceId', {
        date: {
          $gte: startUTC.toISOString().slice(0, 10),
          $lte: endUTC.toISOString().slice(0, 10),
        },
      });

      query.clientId = { $in: activeDeviceIds };
    }

    /* ---------------- FETCH DEVICES ---------------- */

    const devices = await Device.find(query)
      .select(
        'clientId username city division location status ' +
        'padsRemaining totalDispensed refillEvents latestStatus assignedUser createdBy'
      )
      .populate('assignedUser', 'name email role')
      .sort({ clientId: 1 })
      .lean();

    const payload = {
      success: true,
      data: devices.map((d) => ({
        clientId: d.clientId,
        username: d.username,
        city: d.city,
        division: d.division,
        location: d.location,
        status: d.status || 'installed',
        padsRemaining: d.padsRemaining ?? 0,
        totalPads: d.totalDispensed ?? 0,
        refillEvents: d.refillEvents?.length || 0,
        latestStatus: d.latestStatus || 'offline',
        assignedUser: d.assignedUser?._id || null,
        createdBy: d.createdBy || null,
        assignedUserName: d.assignedUser
          ? `${d.assignedUser.name || d.assignedUser.email} (${d.assignedUser.role || 'N/A'})`
          : 'Unassigned',
      })),
      total: devices.length,
    };

    // Cache for 30 seconds (skip cache if date filters are used — dynamic queries)
    if (!startDate && !endDate) {
      await req.redisClient.set(cacheKey, JSON.stringify(payload), 'EX', 30);
    }

    res.json(payload);

  } catch (err) {
    logger.error(`Get devices error: ${err.message}`, {
      requestId,
      stack: err.stack,
    });

    res.status(500).json({
      success: false,
      error: 'Server error fetching devices',
    });
  }
});


// POST: Create device
router.post(
  '/',
  auth,
  restrictTo(['admin', 'distributor']),
  [
    body('clientId').isString().notEmpty().withMessage('clientId is required'),
    body('username').isString().notEmpty().withMessage('username is required'),
    body('password').isString().notEmpty().withMessage('password is required'),
    body('location').optional().isString(),
    body('city').optional().isString(),
    body('division').optional().isString(),
    body('status').optional().isIn(validStatuses).withMessage(`Status must be one of ${validStatuses.join(', ')}`),
    body('padsRemaining').optional().isInt({ min: 0 }).withMessage('padsRemaining must be a non-negative integer'),
  ],
  async (req, res) => {
    const requestId = req.id;
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId, username, password, location, city, division, status, padsRemaining = 0 } = req.body;
      const normalizedClientId = clientId.toLowerCase();

      const exists = await Device.findOne({ clientId: normalizedClientId }).lean();
      if (exists) {
        logger.info(`Device already exists: ${normalizedClientId}`, { requestId });
        return res.status(400).json({ success: false, error: 'Device already exists' });
      }

      const latestStatus = await getLatestStatus(normalizedClientId);

      const newDevice = await Device.create({
        clientId: normalizedClientId,
        username,
        password,
        location: location || '',
        city: city || '',
        division: division || '',
        status: status || 'installed',
        latestStatus,
        padsRemaining,
        createdBy: req.user._id,
        dispenseEvents: [],
        refillEvents: [],
      });

      if (req.redisClient?.status === 'ready') {
        try {
          await retry(
            async () => {
              await req.redisClient.set(normalizedClientId, password);
              logger.info(`Device password saved in Redis: ${normalizedClientId}`, { requestId });
            },
            {
              retries: 3,
              factor: 2,
              minTimeout: 100,
              maxTimeout: 1000,
              onRetry: (err, attempt) =>
                logger.warn(`Redis retry attempt ${attempt} for device ${normalizedClientId}: ${err.message}`, { requestId }),
            }
          );
        } catch (redisErr) {
          logger.error(`Redis save error: ${redisErr.message}`, { requestId, stack: redisErr.stack });
          return res.status(500).json({ success: false, error: 'Failed to save device password in Redis' });
        }
      }

      emitDeviceEvent(req.io, throttle((userId, data) => req.io.to(userId).emit('newData', data), 1000), newDevice, 'created', {}, requestId);

      // ✅ Invalidate device list + stats cache on new device creation
      if (req.redisClient?.status === 'ready') {
        const pattern = `devices:list:v1:*`;
        let cursor = '0';
        do {
          const [next, keys] = await req.redisClient.scan(cursor, 'MATCH', pattern, 'COUNT', 50);
          cursor = next;
          if (keys.length) await req.redisClient.del(...keys);
        } while (cursor !== '0');
      }

      res.status(201).json({ success: true, message: 'Device added successfully', device: newDevice });
    } catch (err) {
      logger.error(`Device creation error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Something went wrong!' });
    }
  }
);

// PUT: Update device status
router.put(
  '/:clientId/status',
  auth,
  [
    param('clientId').isString().notEmpty().withMessage('Invalid clientId'),
    body('latestStatus')
      .equals('offline')
      .withMessage('latestStatus must be "online" or "offline"'),
  ],
  async (req, res) => {
    const requestId = req.id;
    const session = await mongoose.startSession();
    session.startTransaction();

    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        await session.abortTransaction();
        session.endSession();
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      const { latestStatus } = req.body;

      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const currentDevice = await Device.findOne(query).session(session);
      if (!currentDevice) {
        await session.abortTransaction();
        session.endSession();
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      /* ------------------------------------------------------
         🔒 HARD SAFETY: DO NOT DOWNGRADE TO OFFLINE
         IF HEARTBEAT IS RECENT
      ------------------------------------------------------ */
      const OFFLINE_AFTER_MS = 24 * 60 * 60 * 1000;

      if (
        latestStatus === 'offline' &&
        currentDevice.lastPingAt &&
        Date.now() - currentDevice.lastPingAt.getTime() < OFFLINE_AFTER_MS &&
        req.user.role !== 'admin'
      ) {
        await session.abortTransaction();
        session.endSession();
        return res.status(409).json({
          success: false,
          error: 'Device has recent heartbeat; watchdog controls offline state',
        });
      }


      /* ------------------------------------------------------
         🔐 OPTIONAL: only admin can force offline
      ------------------------------------------------------ */
      if (latestStatus === 'offline' && req.user.role !== 'admin') {
        await session.abortTransaction();
        session.endSession();
        return res.status(403).json({
          success: false,
          error: 'Only admin can mark device offline',
        });
      }

      /* ------------------------------------------------------
         UPDATE PAYLOAD
      ------------------------------------------------------ */
      const update = {
        latestStatus,
      };

      if (latestStatus === 'offline') {
        update.offlineAt = new Date(Date.now()); // UTC-safe
        update.offlineReason = 'manual';
      }


      const updatedDevice = await Device.findOneAndUpdate(
        query,
        { $set: update },
        { new: true, session }
      ).lean();

      const totalDispensedValue = updatedDevice.totalDispensed || 0;


      emitDeviceEvent(
        req.io,
        throttle((userId, data) => req.io.to(userId).emit('newData', data), 1000),
        updatedDevice,
        'updated',
        { totalPads: totalDispensedValue },
        requestId
      );

      await session.commitTransaction();
      session.endSession();

      res.json({
        success: true,
        data: {
          ...updatedDevice,
          totalPads: totalDispensedValue,
          padsRemaining: updatedDevice.padsRemaining ?? 0,
        },
      });
    } catch (err) {
      await session.abortTransaction();
      session.endSession();
      logger.error(`Update device status error: ${err.message}`, {
        requestId,
        stack: err.stack,
      });
      res.status(500).json({ success: false, error: 'Server error updating device status' });
    }
  }
);


// PUT: Update device
router.put(
  '/:clientId',
  auth,
  restrictTo(['admin', 'distributor']),
  [
    param('clientId').isString().notEmpty().withMessage('Invalid clientId'),
    body('username').optional().isString().notEmpty().withMessage('username must be a non-empty string'),
    body('password').optional().isString().notEmpty().withMessage('password must be a non-empty string'),
    body('location').optional().isString().withMessage('location must be a string'),
    body('city').optional().isString().withMessage('city must be a string'),
    body('division').optional().isString().withMessage('division must be a string'),
    body('status').optional().isIn(validStatuses).withMessage(`Status must be one of ${validStatuses.join(', ')}`),
    body('padsRemaining').optional().isInt({ min: 0 }).withMessage('padsRemaining must be a non-negative integer'),
  ],
  async (req, res) => {
    const requestId = req.id;
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      const updateData = req.body;

      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const currentDevice = await Device.findOne(query).lean();
      if (!currentDevice) {
        logger.warn(`Device not found or unauthorized: ${normalizedClientId}, user: ${req.user.email}`, { requestId });
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      if (updateData.status === 'installed') {
        updateData.latestStatus = await getLatestStatus(normalizedClientId);
      }

      const updatedDevice = await Device.findOneAndUpdate(query, { $set: updateData }, { new: true }).lean();

      if (req.redisClient?.status === 'ready' && updateData.password) {
        try {
          await retry(
            async () => {
              await req.redisClient.set(normalizedClientId, updateData.password);
              logger.info(`Device password updated in Redis: ${normalizedClientId}`, { requestId });
            },
            {
              retries: 3,
              factor: 2,
              minTimeout: 100,
              maxTimeout: 1000,
              onRetry: (err, attempt) =>
                logger.warn(`Redis retry attempt ${attempt} for device ${normalizedClientId}: ${err.message}`, { requestId }),
            }
          );
        } catch (redisErr) {
          logger.error(`Redis update error: ${redisErr.message}`, { requestId, stack: redisErr.stack });
          return res.status(500).json({ success: false, error: 'Failed to update device password in Redis' });
        }
      }

      const totalDispensedValue = updatedDevice.totalDispensed || 0;

      emitDeviceEvent(req.io, throttle((userId, data) => req.io.to(userId).emit('newData', data), 1000), updatedDevice, 'updated', { totalPads: totalDispensedValue }, requestId);

      // ✅ Invalidate device list cache immediately after edit — no stale location/status shown
      if (req.redisClient?.status === 'ready') {
        const pattern = `devices:list:v1:*`;
        let cursor = '0';
        do {
          const [next, keys] = await req.redisClient.scan(cursor, 'MATCH', pattern, 'COUNT', 50);
          cursor = next;
          if (keys.length) await req.redisClient.del(...keys);
        } while (cursor !== '0');
      }

      res.json({
        success: true,
        data: {
          ...updatedDevice,
          totalPads: totalDispensedValue,
          padsRemaining: updatedDevice.padsRemaining ?? 0,
        },
      });
    } catch (err) {
      logger.error(`Update device error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Server error updating device' });
    }
  }
);

// DELETE: Remove device
router.delete(
  '/:clientId',
  auth,
  restrictTo(['admin', 'distributor']),
  async (req, res) => {
    const requestId = req.id;
    try {
      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();

      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const deleted = await Device.findOneAndDelete(query).lean();
      if (!deleted) {
        logger.warn(`Device not found or unauthorized: ${normalizedClientId}`, { requestId });
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      await Transaction.deleteMany({ DeviceId: { $regex: `^${normalizedClientId}$`, $options: 'i' } });

      if (req.redisClient?.status === 'ready') {
        try {
          await req.redisClient.del(normalizedClientId);
          logger.info(`Device password deleted from Redis: ${normalizedClientId}`, { requestId });
        } catch (redisErr) {
          logger.error(`Redis delete error: ${redisErr.message}`, { requestId, stack: redisErr.stack });
          return res.status(500).json({ success: false, error: 'Failed to delete device password from Redis' });
        }
      }

      await User.updateMany({ assignedDevices: deleted._id }, { $pull: { assignedDevices: deleted._id } });

      emitDeviceEvent(req.io, throttle((userId, data) => req.io.to(userId).emit('newData', data), 1000), deleted, 'deleted', {}, requestId);

      // ✅ Invalidate device list + stats cache immediately after delete
      if (req.redisClient?.status === 'ready') {
        const pattern = `devices:list:v1:*`;
        let cursor = '0';
        do {
          const [next, keys] = await req.redisClient.scan(cursor, 'MATCH', pattern, 'COUNT', 50);
          cursor = next;
          if (keys.length) await req.redisClient.del(...keys);
        } while (cursor !== '0');
      }

      res.json({ success: true, message: 'Device deleted successfully' });
    } catch (err) {
      logger.error(`Delete device error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Server error deleting device' });
    }
  }
);

// POST: Dispense pads
router.post(
  '/:clientId/dispense',
  auth,
  [
    param('clientId')
      .isString()
      .notEmpty()
      .withMessage('Invalid clientId'),

    body('count')
      .isInt({ min: 1 })
      .withMessage('count must be a positive integer'),
  ],
  async (req, res) => {
    const requestId = req.id;
    const session = await mongoose.startSession();

    try {
      session.startTransaction();

      /* ------------------------------------
         1️⃣ VALIDATION
      ------------------------------------ */
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        throw new Error(errors.array()[0].msg);
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      const { count = 1 } = req.body;

      /* ------------------------------------
         2️⃣ DEVICE LOOKUP (ROLE SCOPED)
      ------------------------------------ */
      const query = {
        clientId: normalizedClientId,
        ...(await getDeviceQuery(req)),
      };

      const device = await Device.findOne(query).session(session);

      if (!device) {
        throw new Error('Device not found or unauthorized');
      }

      if (device.padsRemaining < count) {
        throw new Error('Not enough pads remaining');
      }

      /* ------------------------------------
         3️⃣ SINGLE SOURCE OF TIME
      ------------------------------------ */
      const now = new Date();

      /* ------------------------------------
         4️⃣ DEVICE UPDATE
      ------------------------------------ */
      device.dispenseEvents.push({ timestamp: now, count });
      device.padsRemaining -= count;
      device.latestStatus = 'online';
      device.lastSeen = now;
      device.totalDispensed = (device.totalDispensed || 0) + count;

      await device.save({ session });

      /* ------------------------------------
         5️⃣ TRANSACTION INSERT (SOURCE OF TRUTH)
      ------------------------------------ */
      const [transaction] = await Transaction.create(
        [
          {
            DeviceId: normalizedClientId,
            status: 'dispensed',
            pads: device.padsRemaining,
            dispensedCount: count,
            myts: now,
          },
        ],
        { session }
      );

      /* ------------------------------------
         6️⃣ CHART REBUILD (DERIVED DATA)
      ------------------------------------ */
      await rebuildChartFromTransaction(
        normalizedClientId,
        now,
        transaction._id.toString(),
        session,
        count
      );

      /* ------------------------------------
         7️⃣ COMMIT TRANSACTION
      ------------------------------------ */
      await session.commitTransaction();
      session.endSession();

      /* ------------------------------------
         8️⃣ POST-COMMIT EVENTS
      ------------------------------------ */
      const totalDispensedValue = device.totalDispensed || 0;

      emitDeviceEvent(
        req.io,
        throttle(
          (userId, data) => req.io.to(userId).emit('newData', data),
          1000
        ),
        device,
        'dispensed',
        { dispensed: count, totalDispensed: totalDispensedValue },
        requestId
      );

      return res.json({
        success: true,
        data: {
          device: {
            ...device.toObject(),
            totalDispensed: totalDispensedValue,
            padsRemaining: device.padsRemaining ?? 0,
          },
          transaction,
        },
      });

    } catch (err) {
      await session.abortTransaction();
      session.endSession();

      logger.error(`Dispense error: ${err.message}`, {
        requestId,
        stack: err.stack,
      });

      return res.status(500).json({
        success: false,
        error: err.message || 'Server error recording dispense transaction',
      });
    }
  }
);

// POST: Refill pads
router.post(
  '/:clientId/refill',
  auth,
  restrictTo(['admin', 'distributor']),
  [
    param('clientId').isString().notEmpty().withMessage('Invalid clientId'),
    body('addedPads').isInt({ min: 1 }).withMessage('addedPads must be a positive integer'),
  ],
  async (req, res) => {
    const requestId = req.id;
    const session = await mongoose.startSession();
    session.startTransaction();
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        logger.info(`Validation errors: ${JSON.stringify(errors.array())}`, { requestId });
        await session.abortTransaction();
        session.endSession();
        return res.status(400).json({ success: false, error: errors.array()[0].msg });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      const { addedPads } = req.body;

      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const device = await Device.findOne(query).session(session);

      if (!device) {
        logger.warn(`Device not found or unauthorized: ${normalizedClientId}, user: ${req.user.email}`, { requestId });
        await session.abortTransaction();
        session.endSession();
        return res.status(404).json({ success: false, error: 'Device not found or unauthorized' });
      }

      // ❄️ BLOCK REFILL IF DEVICE IS FROZEN
      if (device.isFrozen) {
        await session.abortTransaction();
        session.endSession();
        return res.status(423).json({
          success: false,
          error: 'Device is frozen due to abnormal refill activity',
          freezeReason: device.freezeReason,
          frozenAt: device.frozenAt,
        });
      }


      const now = new Date();
      device.refillEvents.push({ timestamp: now, count: addedPads });
      device.padsRemaining += addedPads;
      device.lastRefillAt = new Date();
      await device.save({ session });

      const transaction = await Transaction.create(
        [
          {
            DeviceId: normalizedClientId,
            status: 'refilled',
            pads: device.padsRemaining,
            addedPads,
            myts: now,
          },
        ],
        { session }
      );


      const totalDispensedValue = device.totalDispensed || 0;

      emitDeviceEvent(req.io, throttle((userId, data) => req.io.to(userId).emit('newData', data), 1000), device, 'refilled', { addedPads, totalDispensed: totalDispensedValue, refillEvents: device.refillEvents?.length || 0 }, requestId);

      await session.commitTransaction();
      session.endSession();
      res.json({
        success: true,
        data: {
          device: {
            ...device.toObject(),
            totalDispensed: totalDispensedValue,
            padsRemaining: device.padsRemaining ?? 0,
            refillEvents: device.refillEvents?.length || 0,
          },
          transaction: transaction[0],
        },
      });
    } catch (err) {
      await session.abortTransaction();
      session.endSession();
      logger.error(`Refill error: ${err.message}`, { requestId, stack: err.stack });
      res.status(500).json({ success: false, error: 'Server error recording refill transaction' });
    }
  }
);

function generateRandomDispenseTimestamps(
  startTime,
  endTime,
  count,
  minGapSec = 60
) {
  if (count <= 0) return [];
  if (count === 1) return [new Date(startTime)];

  const startMs = startTime.getTime();
  const endMs = endTime.getTime();

  const totalSec = (endMs - startMs) / 1000;
  const avgGap = totalSec / count;

  // Ensure feasibility
  if (totalSec < (count - 1) * minGapSec) {
    throw new Error('Time window too small for dispensed count');
  }

  const gaps = [];
  let remainingSec = totalSec;

  for (let i = 0; i < count - 1; i++) {
    const remainingSlots = count - i - 1;
    const maxAllowed =
      remainingSec - remainingSlots * minGapSec;

    // random around avg (±30%)
    const min = Math.max(minGapSec, avgGap * 0.7);
    const max = Math.min(maxAllowed, avgGap * 1.3);

    const gap =
      Math.random() * (max - min) + min;

    gaps.push(gap);
    remainingSec -= gap;
  }

  gaps.push(remainingSec); // last gap closes window

  // Build timestamps
  const timestamps = [];
  let current = startMs;
  timestamps.push(new Date(current));

  for (let i = 0; i < gaps.length - 1; i++) {
    current += gaps[i] * 1000;
    timestamps.push(new Date(Math.round(current)));
  }

  return timestamps;
}

// PUT: Update dispensed count
router.put(
  '/:clientId/dispensedCount',
  auth,
  restrictTo(['admin', 'distributor']),
  [
    param('clientId').isString().notEmpty(),
    body('dispensedCount').isInt({ min: 1 }),
    body('startTime').isISO8601(),
    body('endTime').isISO8601(),
  ],
  async (req, res) => {
    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        return res.status(400).json({
          success: false,
          error: errors.array()[0].msg
        });
      }

      const { clientId } = req.params;
      const normalizedClientId = clientId.toLowerCase();
      const { dispensedCount, startTime, endTime } = req.body;

      const device = await Device.findOne({ clientId: normalizedClientId });
      if (!device) {
        return res.status(404).json({ success: false, error: 'Device not found' });
      }

      const start = new Date(startTime);
      const end = new Date(endTime);

      if (end <= start) {
        return res.status(400).json({
          success: false,
          error: 'End time must be after start time'
        });
      }

      // 🔥 RANDOM REALISTIC SPREAD
      const timestamps = generateRandomDispenseTimestamps(
        start,
        end,
        dispensedCount,
        65 // min 1 minute
      );

      const dispenseEvents = [];
      const transactions = [];

      for (const ts of timestamps) {
        dispenseEvents.push({ count: 1, timestamp: ts });

        transactions.push({
          DeviceId: normalizedClientId,
          status: 'dispensed',
          pads: 1,
          dispensedCount: 1,
          myts: ts
        });
      }

      // ✅ Fix #1: use totalDispensed (actual schema field, was totalPads which doesn't exist)
      await Device.updateOne(
        { clientId: normalizedClientId },
        {
          $push: { dispenseEvents: { $each: dispenseEvents, $slice: -100 } }, // ✅ M5: cap at 100 entries
          $inc: { totalDispensed: dispenseEvents.length }
        }
      );

      await Transaction.insertMany(transactions);

      // ✅ Fix #2: update ChartDaily per date so dashboard stays in sync with reports
      // Group timestamps by IST date for efficient bulk updates
      const dateCountMap = new Map();
      for (const ts of timestamps) {
        const istDate = new Date(ts).toLocaleDateString('en-CA', { timeZone: 'Asia/Kolkata' });
        dateCountMap.set(istDate, (dateCountMap.get(istDate) || 0) + 1);
      }
      // Fire-and-forget: ChartDaily must not block or throw for this operation
      Promise.allSettled(
        Array.from(dateCountMap.entries()).map(([date, cnt]) =>
          updateChartDaily({ deviceId: normalizedClientId, dispensedCount: cnt, ts: new Date(date + 'T12:00:00+05:30') })
        )
      ).catch(() => {});

      res.json({
        success: true,
        message: 'Dispensed count spread realistically',
        summary: {
          clientId: normalizedClientId,
          dispensedCount,
          startTime,
          endTime
        }
      });

    } catch (err) {
      res.status(500).json({
        success: false,
        error: err.message || 'Server error'
      });
    }
  }
);
// FAST MONTHLY DEVICE REPORT
router.get(
  "/:clientId/month-report",
  auth,
  apiLimiter,
  [
    param("clientId").isString().notEmpty(),
    query("month").matches(/^\d{4}-\d{2}$/).withMessage("month must be YYYY-MM")
  ],
  async (req, res) => {
    const requestId = req.id;

    try {
      const errors = validationResult(req);
      if (!errors.isEmpty()) {
        return res.status(400).json({
          success: false,
          error: errors.array()[0].msg
        });
      }

      const { clientId } = req.params;
      const { month } = req.query;

      const normalizedClientId = clientId.toLowerCase();

      /* ---------------- DEVICE ACCESS CHECK ---------------- */

      let query = { clientId: normalizedClientId };
      query = { ...query, ...(await getDeviceQuery(req)) };

      const device = await Device.findOne(query)
        .select("clientId username city division location")
        .lean();

      if (!device) {
        return res.status(404).json({
          success: false,
          error: "Device not found or unauthorized"
        });
      }

      /* ---------------- REDIS CACHE ---------------- */

      const cacheKey = `device:month:${normalizedClientId}:${month}`;
      const cached = await req.redisClient.get(cacheKey);

      if (cached) {
        return res.json(JSON.parse(cached));
      }

      /* ---------------- MONTH RANGE ---------------- */

      const startDate = `${month}-01`;

      const endDate = new Date(startDate);
      endDate.setMonth(endDate.getMonth() + 1);

      const endStr = endDate.toISOString().slice(0, 10);

      /* ---------------- QUERY CHART DAILY ---------------- */

      const days = await ChartDaily.find({
        deviceId: normalizedClientId,
        date: { $gte: startDate, $lt: endStr }
      })
        .sort({ date: 1 })
        .select("date dispensed")
        .lean();

      /* ---------------- BUILD FULL MONTH ---------------- */

      const map = new Map();
      days.forEach(d => map.set(d.date, d.dispensed));

      const result = [];

      const start = new Date(startDate);
      const end = new Date(endStr);

      for (
        let d = new Date(start);
        d < end;
        d.setDate(d.getDate() + 1)
      ) {
        const dateStr = d.toISOString().slice(0, 10);

        result.push({
          date: dateStr,
          dispensed: map.get(dateStr) || 0
        });
      }

      /* ---------------- RESPONSE ---------------- */

      const response = {
        success: true,
        device: {
          clientId: device.clientId,
          username: device.username,
          city: device.city,
          division: device.division,
          location: device.location
        },
        month,
        days: result,
        total: result.reduce((s, d) => s + d.dispensed, 0)
      };

      await req.redisClient.setex(
        cacheKey,
        300,
        JSON.stringify(response)
      );

      return res.json(response);

    } catch (err) {
      logger.error("Month report error", {
        requestId,
        error: err.message,
        stack: err.stack
      });

      return res.status(500).json({
        success: false,
        error: "Failed to fetch monthly report"
      });
    }
  }
);



module.exports = router;
