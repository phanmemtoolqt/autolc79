import fetch from "node-fetch";
import * as readline from "node:readline";
import crypto from "node:crypto";

const C = {
    reset: "\x1b[0m",
    red: "\x1b[31m",
    green: "\x1b[32m",
    yellow: "\x1b[33m",
    blue: "\x1b[34m",
    magenta: "\x1b[35m",
    cyan: "\x1b[36m",
    white: "\x1b[37m",
    bold: "\x1b[1m",
    dim: "\x1b[2m",
    redBg: "\x1b[41m",
    greenBg: "\x1b[42m",
    yellowBg: "\x1b[43m",
    blueBg: "\x1b[44m",
};

function extractFeatures(history) {
    const tx = history.map(h => h.tx === 'T' ? 't' : 'x');
    const totals = history.map(h => h.total);
    const freq = {};
    for (const v of tx) freq[v] = (freq[v] || 0) + 1;
    let runs = [], cur = tx[0], len = 1;
    for (let i = 1; i < tx.length; i++) {
        if (tx[i] === cur) len++;
        else { runs.push({ val: cur, len }); cur = tx[i]; len = 1; }
    }
    if (tx.length) runs.push({ val: cur, len });
    return { tx, totals, freq, runs, maxRun: runs.reduce((m, r) => Math.max(m, r.len), 0) };
}

function detectPatternType(runs) {
    if (runs.length < 3) return null;
    const lastRuns = runs.slice(-6);
    const lengths = lastRuns.map(r => r.len);
    const values = lastRuns.map(r => r.val);
    if (lastRuns.length >= 3) {
        if (lengths.every(l => l === 1) && values.every((v, i) => i === 0 || v !== values[i-1])) return '1_1_pattern';
        if (lengths.every(l => l === 2) && values.every((v, i) => i === 0 || v !== values[i-1])) return '2_2_pattern';
        if (lengths.every(l => l === 3) && values.every((v, i) => i === 0 || v !== values[i-1])) return '3_3_pattern';
        if (lengths.length >= 5 && lengths[0]===2 && lengths[1]===1 && lengths[2]===2 && lengths[3]===1 && lengths[4]===2) return '2_1_2_pattern';
        if (lengths.length >= 5 && lengths[0]===1 && lengths[1]===2 && lengths[2]===1 && lengths[3]===2 && lengths[4]===1) return '1_2_1_pattern';
        if (lengths.length >= 5 && lengths[0]===3 && lengths[1]===2 && lengths[2]===3 && lengths[3]===2 && lengths[4]===3) return '3_2_3_pattern';
        if (lengths.length >= 5 && lengths[0]===4 && lengths[1]===2 && lengths[2]===4 && lengths[3]===2 && lengths[4]===4) return '4_2_4_pattern';
        if (lengths.length >= 5 && lengths[0]===2 && lengths[1]===2 && lengths[2]===1 && lengths[3]===2 && lengths[4]===2) return '2_2_1_pattern';
        if (lengths.length >= 5 && lengths[0]===1 && lengths[1]===3 && lengths[2]===1 && lengths[3]===3 && lengths[4]===1) return '1_3_1_pattern';
        if (lengths.length >= 5 && lengths[0]===3 && lengths[1]===1 && lengths[2]===3 && lengths[3]===1 && lengths[4]===3) return '3_1_3_pattern';
    }
    const lastRun = lastRuns[lastRuns.length - 1];
    if (lastRun && lastRun.len >= 5) return 'long_run_pattern';
    return null;
}

function predictFromPattern(patternType, runs, lastTx) {
    if (!patternType) return null;
    const lastRun = runs[runs.length - 1];
    switch (patternType) {
        case '1_1_pattern': return lastTx === 't' ? 'x' : 't';
        case '2_2_pattern': return lastRun.len === 2 ? (lastRun.val === 't' ? 'x' : 't') : lastRun.val;
        case '3_3_pattern': return lastRun.len === 3 ? (lastRun.val === 't' ? 'x' : 't') : lastRun.val;
        case '2_1_2_pattern':
            if (lastRun.len === 2) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 1) return lastRun.val;
            return null;
        case '1_2_1_pattern':
            if (lastRun.len === 1) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 2) return lastRun.val;
            return null;
        case '3_2_3_pattern':
        case '4_2_4_pattern':
            if (lastRun.len >= 3) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 2) return lastRun.val;
            return null;
        case '2_2_1_pattern':
            if (lastRun.len === 2) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 1) return lastRun.val === 't' ? 'x' : 't';
            return null;
        case '1_3_1_pattern':
            if (lastRun.len === 1) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 3) return lastRun.val;
            return null;
        case '3_1_3_pattern':
            if (lastRun.len === 3) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len === 1) return lastRun.val;
            return null;
        case 'long_run_pattern':
            if (lastRun.len > 7) return lastRun.val === 't' ? 'x' : 't';
            if (lastRun.len >= 4) return lastRun.val;
            return null;
        default: return null;
    }
}

const API_URL = "https://wtxmd52.tele68.com/v1/txmd5";

let username = "";
let password = "";
let md5Password = "";
let balance = 0;
let isLoggedIn = false;
let token = null;
let jwtToken = null;
let txHistory = [];
let currentSessionId = null;
let historyLoaded = false;
let nextSessionId = null;
let bettingActive = false;
let betInterval = null;
let betAmount = 5000;
let initialBalance = 0;
let targetProfit = 0;
let lastBetSession = null;
let lastBetSide = null;
let lastProcessedSession = null;
let totalBets = 0;
let wins = 0;
let losses = 0;

const rl = readline.createInterface({ input: process.stdin, output: process.stdout });

function question(query) {
    return new Promise(resolve => rl.question(query, resolve));
}

function parseLines(data) {
    if (!data || !Array.isArray(data.list)) return [];
    const sortedList = data.list.sort((a, b) => b.id - a.id);
    const arr = sortedList.map(item => ({
        session: item.id,
        dice: item.dices,
        total: item.point,
        result: item.resultTruyenThong,
        tx: item.point >= 11 ? 'T' : 'X'
    }));
    return arr.sort((a, b) => a.session - b.session);
}

function formatMoney(n) {
    return n.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ".");
}

const PATTERN_DB = {
  'tttt':     { t: 73, x: 27 }, 'xxxx':     { t: 27, x: 73 },
  'tttttt':   { t: 83, x: 17 }, 'xxxxxx':   { t: 17, x: 83 },
  'ttttx':    { t: 40, x: 60 }, 'xxxxt':    { t: 60, x: 40 },
  'ttttttx':  { t: 30, x: 70 }, 'xxxxxxt':  { t: 70, x: 30 },
  'ttxx':     { t: 62, x: 38 }, 'xxtt':     { t: 38, x: 62 },
  'txx':      { t: 60, x: 40 }, 'xtt':      { t: 40, x: 60 },
  'ttx':      { t: 65, x: 35 }, 'xxt':      { t: 35, x: 65 },
  'txt':      { t: 58, x: 42 }, 'xtx':      { t: 42, x: 58 },
  'tttx':     { t: 70, x: 30 }, 'xxxt':     { t: 30, x: 70 },
  'ttxt':     { t: 63, x: 37 }, 'xxtx':     { t: 37, x: 63 },
  'txxx':     { t: 25, x: 75 }, 'xttt':     { t: 75, x: 25 },
  'ttxtx':    { t: 62, x: 38 }, 'xxtxt':    { t: 38, x: 62 },
  'ttxxt':    { t: 55, x: 45 }, 'xxttx':    { t: 45, x: 55 },
  'txtx':     { t: 52, x: 48 }, 'xtxt':     { t: 48, x: 52 },
  'txtxt':    { t: 53, x: 47 }, 'xtxtx':    { t: 47, x: 53 },
  'txtxtxt':  { t: 57, x: 43 }, 'xtxtxtx':  { t: 43, x: 57 },
};

function detectStreak(vals) {
  if (!vals.length) return { streak: 0, current: null, breakProb: 0 };
  let streak = 1;
  const current = vals[vals.length - 1];
  for (let i = vals.length - 2; i >= 0; i--) {
    if (vals[i] === current) streak++;
    else break;
  }
  const last15 = vals.slice(-15);
  let switches = 0;
  for (let i = 1; i < last15.length; i++) {
    if (last15[i] !== last15[i - 1]) switches++;
  }
  const tCount = last15.filter(v => v === 't').length;
  const imbalance = Math.abs(tCount - (last15.length - tCount)) / last15.length;
  let breakProb = 0;
  if (streak >= 8) breakProb = Math.min(0.6 + (switches / 15) + imbalance * 0.15, 0.9);
  else if (streak >= 5) breakProb = Math.min(0.35 + (switches / 10) + imbalance * 0.25, 0.85);
  else if (streak >= 3 && switches >= 7) breakProb = 0.3;
  return { streak, current, breakProb };
}

function ngramPredict(vals) {
  const results = [];
  for (let len = 2; len <= 5; len++) {
    if (vals.length < len + 1) continue;
    const pattern = vals.slice(-len).join('');
    let tCount = 0, xCount = 0, total = 0;
    for (let i = 0; i <= vals.length - len - 1; i++) {
      const seg = vals.slice(i, i + len).join('');
      if (seg === pattern) {
        total++;
        if (vals[i + len] === 't') tCount++;
        else xCount++;
      }
    }
    if (total >= 2) {
      const prob = tCount / total;
      results.push({
        len,
        prediction: prob > 0.5 ? 't' : 'x',
        confidence: Math.abs(prob - 0.5) * 200,
        samples: total,
        ratio: tCount + '/' + xCount
      });
    }
  }
  results.sort(function(a, b) { return (b.len * b.samples) - (a.len * a.samples); });
  return results[0] || null;
}

function weightedTrend(vals) {
  const last15 = vals.slice(-15);
  if (last15.length < 3) return null;
  const weights = last15.map(function(_, i) { return Math.pow(1.15, i); });
  var tW = 0, xW = 0, totalW = 0;
  last15.forEach(function(v, i) {
    totalW += weights[i];
    if (v === 't') tW += weights[i]; else xW += weights[i];
  });
  var ratio = (tW - xW) / totalW;
  return {
    prediction: ratio > 0 ? 't' : 'x',
    confidence: Math.abs(ratio) * 100
  };
}

function meanDeviation(vals) {
  var last12 = vals.slice(-12);
  if (last12.length < 3) return null;
  var tCount = last12.filter(function(v) { return v === 't'; }).length;
  var deviation = Math.abs(tCount - (last12.length - tCount)) / last12.length;
  if (deviation < 0.35) {
    return { prediction: last12[last12.length - 1] === 'x' ? 't' : 'x', confidence: 55 + deviation * 30 };
  }
  return { prediction: tCount > last12.length - tCount ? 't' : 'x', confidence: 50 + deviation * 50 };
}

function detectCycle(vals) {
  if (vals.length < 20) return null;
  var values = vals.map(function(v) { return v === 't' ? 1 : -1; });
  var n = values.length;
  var bestPeriod = 0, bestCorrelation = -1;
  for (var period = 2; period <= Math.floor(n / 3); period++) {
    var correlation = 0, count = 0;
    for (var i = 0; i < n - period; i++) {
      correlation += values[i] * values[i + period];
      count++;
    }
    correlation /= count;
    if (correlation > bestCorrelation) {
      bestCorrelation = correlation;
      bestPeriod = period;
    }
  }
  if (bestCorrelation < 0.2) return null;
  var position = vals.length % bestPeriod;
  var cycleResults = [];
  for (var j = position; j < vals.length; j += bestPeriod) {
    cycleResults.push(vals[j]);
  }
  var tCount2 = cycleResults.filter(function(r) { return r === 't'; }).length;
  return {
    period: bestPeriod,
    correlation: bestCorrelation,
    prediction: tCount2 > cycleResults.length / 2 ? 't' : 'x',
    confidence: Math.abs(tCount2 / cycleResults.length - 0.5) * 200
  };
}

function markovPredict(vals) {
  var orders = [3, 2, 1];
  for (var oi = 0; oi < orders.length; oi++) {
    var order = orders[oi];
    if (vals.length <= order) continue;
    var table = {};
    for (var i = 0; i <= vals.length - order - 1; i++) {
      var key = vals.slice(i, i + order).join('\u2192');
      var next = vals[i + order];
      if (!table[key]) table[key] = { t: 0, x: 0 };
      table[key][next]++;
    }
    var state = vals.slice(-order).join('\u2192');
    var cnt = table[state];
    if (!cnt) continue;
    var total = cnt.t + cnt.x;
    if (total < 3) continue;
    return {
      prediction: cnt.t >= cnt.x ? 't' : 'x',
      confidence: Math.round(Math.max(cnt.t, cnt.x) / total * 100),
      order: order,
      samples: total
    };
  }
  return null;
}

function fibonacciMomentum(vals) {
  if (vals.length < 10) return null;
  var fib = [1, 1, 2, 3, 5, 8, 13, 21];
  var tScore = 0, xScore = 0;
  for (var i = 0; i < Math.min(fib.length, vals.length); i++) {
    var idx = vals.length - 1 - i;
    if (vals[idx] === 't') tScore += fib[i];
    else xScore += fib[i];
  }
  var total = tScore + xScore;
  return {
    prediction: tScore > xScore ? 't' : 'x',
    confidence: Math.abs(tScore - xScore) / total * 100
  };
}

function smartBridgeBreak(vals) {
  if (vals.length < 3) return null;
  var si = detectStreak(vals);
  var streak = si.streak, current = si.current, breakProb = si.breakProb;
  if (streak < 3) return null;
  var last20 = vals.slice(-20);
  var pCounts = {};
  for (var i = 0; i <= last20.length - 3; i++) {
    var p = last20.slice(i, i + 3).join(',');
    pCounts[p] = (pCounts[p] || 0) + 1;
  }
  var entries = Object.entries(pCounts).sort(function(a, b) { return b[1] - a[1]; });
  var mc = entries[0];
  var isStable = mc && mc[1] >= 3;
  var breakProbability = breakProb;
  if (streak >= 6) breakProbability = Math.min(breakProbability + 0.15, 0.9);
  else if (streak >= 4) breakProbability = Math.min(breakProbability + 0.1, 0.85);
  else breakProbability = Math.max(breakProbability - 0.15, 0.15);
  var prediction = breakProbability > 0.65
    ? (current === 't' ? 'x' : 't')
    : (current === 't' ? 't' : 'x');
  return { prediction: prediction, confidence: breakProbability * 100, streak: streak, breakProb: breakProbability };
}

function patternDBLookup(vals) {
  if (vals.length < 3) return null;
  var keys = Object.keys(PATTERN_DB).sort(function(a, b) { return b.length - a.length; });
  var currentStr = vals.slice(0, 15).join('');
  for (var i = 0; i < keys.length; i++) {
    var key = keys[i];
    if (currentStr.endsWith(key)) {
      var data = PATTERN_DB[key];
      return { prediction: data.t > data.x ? 't' : 'x', confidence: Math.max(data.t, data.x), pattern: key };
    }
  }
  return null;
}

function detectSpecialPatterns(vals) {
  if (vals.length < 4) return null;
  var last4 = vals.slice(-4);
  if (last4[0] === last4[1] && last4[2] === last4[3] && last4[1] !== last4[2]) {
    return { prediction: last4[3] === 't' ? 't' : 'x', confidence: 62, pattern: 'AABB' };
  }
  if (vals.length >= 6) {
    var alternating = true;
    for (var i = vals.length - 6; i < vals.length; i++) {
      if (i > vals.length - 6 && vals[i] === vals[i - 1]) { alternating = false; break; }
    }
    if (alternating) return { prediction: vals[vals.length - 1] === 't' ? 'x' : 't', confidence: 65, pattern: '1-1' };
  }
  if (vals.length >= 5) {
    var m = vals.slice(-5);
    if (m[0] === m[1] && m[1] !== m[2] && m[3] === m[4] && m[0] === m[3]) {
      return { prediction: m[2], confidence: 62, pattern: '2-1' };
    }
  }
  return null;
}

function predictTaiXiu(history, options) {
  options = options || {};
  var vals = history.map(function(v) {
    if (typeof v === 'string') {
      var lower = v.toLowerCase();
      if (lower === 't' || lower === 't\u00e0i' || lower === 'tai') return 't';
      if (lower === 'x' || lower === 'x\u1ec9u' || lower === 'xiu') return 'x';
      if (lower === 'b' || lower === 'banker') return 't';
      if (lower === 'p' || lower === 'player') return 'x';
    }
    return v === 1 ? 't' : 'x';
  });
  var n = vals.length;
  if (n < 3) return { val: 't', conf: 55, algos: ['Thu th\u1eadp d\u1eef li\u1ec7u'], prob_t: 0.52, prob_x: 0.48, streak: 0, pattern: '' };
  var sT = 0, sX = 0;
  var algos = [];
  var last = vals[n - 1];
  var opp = last === 't' ? 'x' : 't';
  var streakInfo = detectStreak(vals);
  var streak = streakInfo.streak;

  if (streak >= 6) {
    if (opp === 't') sT += 5.0; else sX += 5.0;
    algos.push('B\u1ec7t C\u1ef1c M\u1ea1nh (' + streak + ')');
  } else if (streak >= 4) {
    if (opp === 't') sT += 4.0; else sX += 4.0;
    algos.push('B\u1ec7t M\u1ea1nh (' + streak + ')');
  } else if (streak >= 3) {
    if (opp === 't') sT += 3.0; else sX += 3.0;
    algos.push('B\u1ebb C\u1ea7u (' + streak + ')');
  } else if (streak === 2) {
    if (last === 't') sT += 2.0; else sX += 2.0;
    algos.push('Theo C\u1ea7u (2)');
  } else {
    if (opp === 't') sT += 1.5; else sX += 1.5;
    algos.push('Xen K\u1ebd');
  }

  var ng = ngramPredict(vals);
  if (ng) {
    var w = ng.len * 0.8 + Math.min(ng.samples, 10) * 0.2;
    if (ng.prediction === 't') sT += w; else sX += w;
    algos.push('N-Gram(' + ng.len + ':' + ng.ratio + ')');
  }

  var wt = weightedTrend(vals);
  if (wt) {
    if (wt.prediction === 't') sT += wt.confidence / 30; else sX += wt.confidence / 30;
    algos.push('Trend(' + wt.confidence.toFixed(0) + '%)');
  }

  var md = meanDeviation(vals);
  if (md) {
    if (md.prediction === 't') sT += md.confidence / 40; else sX += md.confidence / 40;
    algos.push('Deviation(' + md.confidence.toFixed(0) + '%)');
  }

  var cycle = detectCycle(vals);
  if (cycle && cycle.correlation > 0.3) {
    if (cycle.prediction === 't') sT += 2.0; else sX += 2.0;
    algos.push('Cycle(' + cycle.period + ':' + cycle.correlation.toFixed(2) + ')');
  }

  var mk = markovPredict(vals);
  if (mk) {
    var mw = mk.confidence / 30;
    if (mk.prediction === 't') sT += mw; else sX += mw;
    algos.push('Markov(B' + mk.order + ':' + mk.confidence + '%)');
  }

  var fm = fibonacciMomentum(vals);
  if (fm) {
    if (fm.prediction === 't') sT += 1.5; else sX += 1.5;
    algos.push('Fibonacci(' + fm.confidence.toFixed(0) + '%)');
  }

  var bb = smartBridgeBreak(vals);
  if (bb && streak >= 3) {
    if (bb.prediction === 't') sT += 2.5; else sX += 2.5;
    algos.push('BridgeBreak(' + (bb.breakProb * 100).toFixed(0) + '%)');
  }

  var pdb = patternDBLookup(vals);
  if (pdb) {
    if (pdb.prediction === 't') sT += 2.0; else sX += 2.0;
    algos.push('PatternDB(' + pdb.pattern + ')');
  }

  var sp = detectSpecialPatterns(vals);
  if (sp) {
    if (sp.prediction === 't') sT += 1.5; else sX += 1.5;
    algos.push('Special(' + sp.pattern + ')');
  }

  var goodRoad = options.goodRoad || '';
  if (goodRoad) {
    var gr = goodRoad.toLowerCase();
    if (gr.includes('t\u00e0i') || gr.includes('c\u00e1i') || gr.includes('banker')) {
      sT += 1.5;
      algos.push('GoodRoad\u2192T\u00e0i');
    } else if (gr.includes('x\u1ec9u') || gr.includes('con') || gr.includes('player')) {
      sX += 1.5;
      algos.push('GoodRoad\u2192X\u1ec9u');
    }
  }

  var last20 = vals.slice(-20);
  var t20 = last20.filter(function(v) { return v === 't'; }).length;
  if (t20 >= 14) sX += 0.5;
  else if (t20 <= 6) sT += 0.5;

  var total = (sT + sX) || 1;
  var val = sT >= sX ? 't' : 'x';
  var winScore = Math.max(sT, sX);
  var conf = Math.min(95, Math.max(55, Math.round((winScore / total) * 100)));

  return {
    val: val,
    conf: conf,
    algos: algos.slice(0, 8),
    prob_t: +(sT / total).toFixed(4),
    prob_x: +(sX / total).toFixed(4),
    streak: streak,
    pattern: streak >= 2 ? ('B\u1ec7t ' + last + ' \u00d7' + streak) : (sp ? sp.pattern : (pdb ? pdb.pattern : ''))
  };
}

function predictNext() {
    if (txHistory.length < 5) return { prediction: "tai", confidence: 50, pattern: '...', algos: [] };

    const vals = txHistory.map(r => r.tx === 'T' ? 't' : 'x');

    const result = predictTaiXiu(vals);

    const features = extractFeatures(txHistory);
    const patternType = detectPatternType(features.runs);
    let patternPred = null;
    if (patternType) {
        const lastTx = features.tx[features.tx.length - 1];
        patternPred = predictFromPattern(patternType, features.runs, lastTx);
    }

    let finalVal = result.val;
    let algos = [...result.algos];
    if (patternPred) {
        const patternName = patternType.replace(/_/g, ' ');
        if (result.val === patternPred) {
            algos.push(`Cầu ${patternName} ✅`);
        } else {
            algos.push(`Cầu ${patternName}`);
            finalVal = patternPred;
        }
    }

    const historyStr = vals.slice(-4).join('');

    return {
        prediction: finalVal === 't' ? 'tai' : 'xiu',
        confidence: result.conf,
        rawPrediction: finalVal.toUpperCase(),
        algos: algos.slice(0, 10),
        pattern: historyStr,
        streak: result.streak || 0
    };
}

async function login(un = username, pw = password) {
    console.log(`${C.blue}⟳ Đang đăng nhập...${C.reset}`);
    try {
        md5Password = crypto.createHash("md5").update(pw).digest("hex");

        const loginRes = await fetch(
            `https://apifo88daigia.tele68.com/api?c=3&un=${encodeURIComponent(un)}&pw=${md5Password}&cp=R&cl=R&pf=web&at=`
        );
        const loginData = await loginRes.json();
        if (!loginData.success) {
            console.log(`${C.red}❌ Login thất bại:${C.reset} Sai tài khoản hoặc mật khẩu`);
            return false;
        }

        token = loginData.accessToken;
        const sessionKey = loginData.sessionKey;

        let nickName = username;
        try {
            const sessionRaw = Buffer.from(sessionKey, "base64").toString();
            const sessionData = JSON.parse(sessionRaw);
            if (sessionData.nickname) nickName = sessionData.nickname;
        } catch (e) {}

        const authRes = await fetch(
            `https://wlb.tele68.com/v1/lobby/auth/login?cp=R&cl=R&pf=web&at=${token}`,
            {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({
                    username: un,
                    password: md5Password,
                    nickName,
                    accessToken: token,
                    sessionKey
                })
            }
        );
        const authData = await authRes.json();
        if (!authData.token) {
            console.log(`${C.red}❌ Xác thực thất bại:${C.reset}`, JSON.stringify(authData));
            return false;
        }

        jwtToken = authData.token;
        balance = authData.remoteLoginResp?.money || 0;
        isLoggedIn = true;
        console.log(`${C.green}✅ Đăng nhập thành công! Số dư: ${formatMoney(balance)}đ${C.reset}`);
        return true;
    } catch (e) {
        console.log(`${C.red}❌ Lỗi đăng nhập:${C.reset}`, e.message);
        return false;
    }
}

async function getBalance() {
    try {
        const res = await fetch(
            `https://gameapi.tele68.com/v1/profile/balance?cp=R&cl=R&pf=web&at=${token}`,
            {
                headers: {
                    "Content-Type": "application/json",
                    "Authorization": `Bearer ${jwtToken}`
                }
            }
        );
        if (res.ok) {
            const data = await res.json();
            balance = data.balance || data.money || data.von || 0;
            return balance;
        }
    } catch (e) {}
    balance = 0;
    return 0;
}

async function fetchHistory() {
    try {
        const res = await fetch(`${API_URL}/sessions?cp=R&cl=R&pf=web&at=${token}`);
        const data = await res.json();
        const parsed = parseLines(data);
        if (parsed.length > 0) {
            txHistory = parsed;
            currentSessionId = parsed[parsed.length - 1].session;
            if (!historyLoaded) {
                historyLoaded = true;
                console.log(`${C.blue}📊 Đã lấy ${parsed.length} phiên lịch sử. Phiên cuối: ${currentSessionId}${C.reset}`);
            }
            return true;
        }
    } catch (e) {
        console.error(`${C.red}❌ Lỗi lấy lịch sử:${C.reset}`, e.message);
    }
    return false;
}

async function placeBet(prediction) {
    if (balance < betAmount) {
        console.log(`⚠️ Het von (${formatMoney(balance)}), dung lai.`);
        stopAutoBet();
        return false;
    }
    const betSide = prediction.rawPrediction;
    const betType = betSide === 'T' ? 'TAI' : 'XIU';

    for (let attempt = 0; attempt < 10; attempt++) {
        const trySession = (nextSessionId || currentSessionId + 1) + attempt;
        if (!trySession) break;

        try {
            const body = {
                username,
                password: md5Password,
                amount: betAmount,
                side: betSide,
                session: trySession,
                type: betType
            };

            const res = await fetch(`https://wtxmd52.tele68.com/v1/txmd5/bet?limit=8&cp=R&cl=R&pf=web&at=${token}`, {
                method: "POST",
                headers: {
                    "Content-Type": "application/json",
                    "Authorization": `Bearer ${jwtToken}`
                },
                body: JSON.stringify(body)
            });

            if (res.ok) {
                const data = await res.json();

                if (data.postBalance !== undefined) {
                    const preBalance = balance;
                    balance = data.postBalance;
                    lastBetSession = trySession;
                    lastBetSide = prediction.rawPrediction;
                    nextSessionId = lastBetSession + 1;
                    lastProcessedSession = trySession;

                    const displayName = prediction.rawPrediction === 'T' ? 'TÀI' : 'XỈU';
                    console.log(`${C.dim}┌──────────────────────────────────────────${C.reset}`);
                    console.log(`${C.dim}│${C.reset} 📌 ${C.bold}${C.cyan}ĐẶT CƯỢC${C.reset} ${displayName} ${C.bold}${formatMoney(betAmount)}đ${C.reset}`);
                    console.log(`${C.dim}│${C.reset} 📊 Tỉ lệ: ${C.yellow}${prediction.confidence}%${C.reset} | Cầu: ${C.dim}${prediction.pattern}${C.reset}`);
                    console.log(`${C.dim}└──────────────────────────────────────────${C.reset}`);
                    const resultKey = data.result || data.ketQua || data.ket_qua || '';
                    let won = null;
                    if (resultKey) {
                        const resultTx = resultKey === 'T' || resultKey === 'TÀI' || resultKey === 'TAI' ? 'T' :
                                         resultKey === 'X' || resultKey === 'XỈU' || resultKey === 'XIU' ? 'X' : null;
                        if (resultTx) won = resultTx === prediction.rawPrediction;
                    }
                    if (won === null) {
                        if (balance > preBalance) won = true;
                        else if (balance < preBalance) won = false;
                    }
                    const netChange = balance - preBalance;
                    totalBets++;
                    if (won === true) { wins++; } else if (won === false) { losses++; }
                    if (won === true) {
                        console.log(`${C.dim}┌──────────────────────────────────────────${C.reset}`);
                        console.log(`${C.dim}│${C.reset} ${C.greenBg}${C.white}${C.bold} ✅ THẮNG ${C.reset} ${C.green}+${formatMoney(betAmount)}đ${C.reset}`);
                        console.log(`${C.dim}│${C.reset} 💰 Số dư: ${C.bold}${formatMoney(balance)}đ${C.reset}`);
                        console.log(`${C.dim}└──────────────────────────────────────────${C.reset}`);
                    } else if (won === false) {
                        console.log(`${C.dim}┌──────────────────────────────────────────${C.reset}`);
                        console.log(`${C.dim}│${C.reset} ${C.redBg}${C.white}${C.bold} ❌ THUA ${C.reset} ${C.red}-${formatMoney(betAmount)}đ${C.reset}`);
                        console.log(`${C.dim}│${C.reset} 💰 Số dư: ${C.bold}${formatMoney(balance)}đ${C.reset}`);
                        console.log(`${C.dim}└──────────────────────────────────────────${C.reset}`);
                    }
                    const profit = balance - initialBalance;
                    if (targetProfit > 0 && profit >= targetProfit) {
                        console.log(`\n${C.greenBg}${C.white}${C.bold} 🎯 ĐẠT MỤC TIÊU LÃI ${formatMoney(targetProfit)}đ! DỪNG BOT. ${C.reset}`);
                        stopAutoBet();
                        return false;
                    }
                    if (balance < betAmount) {
                        console.log(`\n${C.redBg}${C.white}${C.bold} ⚠️ HẾT VỐN! DỪNG BOT. ${C.reset}`);
                        stopAutoBet();
                        return false;
                    }
                    return true;
                }
                if (data.message === "out_of_time") continue;
                console.log(`${C.red}❌ Đặt cược thất bại:${C.reset} ${JSON.stringify(data)}`);
                return false;
            } else {
                const errText = await res.text();
                let errData;
                try { errData = JSON.parse(errText); } catch (e) { errData = { message: errText }; }
                if (errData.message === "out_of_time") continue;
                console.log(`${C.red}❌ Đặt cược thất bại:${C.reset} ${errText}`);
                return false;
            }
        } catch (e) {
            console.error(`${C.red}❌ Lỗi đặt cược:${C.reset}`, e.message);
            return false;
        }
    }
    nextSessionId = currentSessionId + 1;
    return false;
}

function startAutoBet() {
    if (bettingActive) return;
    if (balance < betAmount) {
        console.log(`${C.red}⚠️ Không đủ vốn để bắt đầu (cần >= ${formatMoney(betAmount)}đ)${C.reset}`);
        return;
    }

    bettingActive = true;
    console.log(`\n${C.greenBg}${C.white}${C.bold} 🚀 BẮT ĐẦU AUTO BET ${C.reset}`);
    console.log(`${C.cyan}💰 Vốn:${C.reset} ${C.bold}${formatMoney(balance)}đ${C.reset} | ${C.cyan}Mỗi tay:${C.reset} ${C.bold}${formatMoney(betAmount)}đ${C.reset} | ${C.cyan}Mục tiêu:${C.reset} ${C.bold}${C.green}${targetProfit > 0 ? formatMoney(targetProfit) + 'đ' : 'Không giới hạn'}${C.reset}`);
    console.log(`${C.dim}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${C.reset}\n`);

    betLoop();
}

async function betLoop() {
    if (!bettingActive || !isLoggedIn) { betInterval = setTimeout(betLoop, 2000); return; }

    const oldLen = txHistory.length;
    await fetchHistory();

    if (txHistory.length >= 3) {
        if (lastBetSession !== null && txHistory.length > oldLen) {
            if (lastProcessedSession === null || lastProcessedSession < lastBetSession) {
                for (let i = oldLen; i < txHistory.length; i++) {
                    if (txHistory[i].session === lastBetSession) {
                        const won = txHistory[i].tx === lastBetSide;
                        if (won) balance += betAmount * 2;
                        totalBets++;
                        lastProcessedSession = txHistory[i].session;
                        lastBetSession = txHistory[i].session;
                        if (won) {
                            wins++;
                            console.log(`${C.dim}┌──────────────────────────────────────────${C.reset}`);
                            console.log(`${C.dim}│${C.reset} ${C.greenBg}${C.white}${C.bold} ✅ THẮNG ${C.reset} ${C.green}+${formatMoney(betAmount)}đ${C.reset}`);
                            console.log(`${C.dim}│${C.reset} 💰 Số dư: ${C.bold}${formatMoney(balance)}đ${C.reset}`);
                            console.log(`${C.dim}└──────────────────────────────────────────${C.reset}`);
                        } else {
                            losses++;
                            console.log(`${C.dim}┌──────────────────────────────────────────${C.reset}`);
                            console.log(`${C.dim}│${C.reset} ${C.redBg}${C.white}${C.bold} ❌ THUA ${C.reset} ${C.red}-${formatMoney(betAmount)}đ${C.reset}`);
                            console.log(`${C.dim}│${C.reset} 💰 Số dư: ${C.bold}${formatMoney(balance)}đ${C.reset}`);
                            console.log(`${C.dim}└──────────────────────────────────────────${C.reset}`);
                        }
                        const profit = balance - initialBalance;
                        if (targetProfit > 0 && profit >= targetProfit) {
                            console.log(`\n${C.greenBg}${C.white}${C.bold} 🎯 ĐẠT MỤC TIÊU LÃI ${formatMoney(targetProfit)}đ! DỪNG BOT. ${C.reset}`);
                            stopAutoBet();
                            return;
                        }
                        if (balance < betAmount) {
                            console.log(`\n${C.redBg}${C.white}${C.bold} ⚠️ HẾT VỐN! DỪNG BOT. ${C.reset}`);
                            stopAutoBet();
                            return;
                        }
                        break;
                    }
                }
            }
        }

        if (lastBetSession !== null && (lastProcessedSession === null || lastProcessedSession < lastBetSession)) {
            const latestResult = txHistory[txHistory.length - 1];
            if (latestResult && lastBetSession >= latestResult.session) {
                betInterval = setTimeout(betLoop, 2000);
                return;
            }
        }

        if (nextSessionId === null) {
            nextSessionId = currentSessionId + 1;
        }

        const prediction = predictNext();

        await placeBet(prediction);
    }

    betInterval = setTimeout(betLoop, 2000);
}

function stopAutoBet() {
    bettingActive = false;
    if (betInterval) {
        clearInterval(betInterval);
        betInterval = null;
    }
    const profit = balance - initialBalance;
    const profitColor = profit >= 0 ? C.green : C.red;
    console.log(`\n${C.dim}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${C.reset}`);
    console.log(`${C.yellowBg}${C.white}${C.bold} ⏹ ĐÃ DỪNG AUTO BET ${C.reset}`);
    console.log(`${C.dim}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${C.reset}`);
    console.log(`📊 Tổng: ${C.bold}${totalBets}${C.reset} | ✅ ${C.green}${wins}${C.reset} | ❌ ${C.red}${losses}${C.reset}`);
    console.log(`💰 ${profitColor}${C.bold}${profit >= 0 ? '+' : ''}${formatMoney(profit)}đ${C.reset}`);
    console.log(`${C.dim}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${C.reset}`);
}

async function main() {
    console.log(`${C.cyan}╔═══════════════════════════════════════╗${C.reset}`);
    console.log(`${C.cyan}║${C.reset}       ${C.bold}🎰 LC79 AUTO BET BOT${C.reset}        ${C.cyan}║${C.reset}`);
    console.log(`${C.cyan}║${C.reset}   ${C.dim}Create by: @mrtinhios${C.reset}         ${C.cyan}║${C.reset}`);
    console.log(`${C.cyan}║${C.reset}   ${C.dim}📱 Box Chat: @ChatToolTXViP${C.reset}     ${C.cyan}║${C.reset}`);
    console.log(`${C.cyan}╚═══════════════════════════════════════╝${C.reset}\n`);

    username = "chicuong17cm";
    password = "Duongtien2@@";

    const loggedIn = await login(username, password);
    if (!loggedIn) {
        console.log(`${C.red}❌ Không thể đăng nhập.${C.reset}`);
        rl.close();
        process.exit(1);
    }
    if (loggedIn) {
        await fetchHistory();
        await getBalance();
        console.log(`${C.cyan}💰 Số dư tài khoản:${C.reset} ${C.bold}${formatMoney(balance)}đ${C.reset}`);

        let vonInput = await question(`${C.yellow}➤ Nhập số vốn: ${C.reset}`);
        let von = parseInt(vonInput.replace(/\./g, ""));
        if (!isNaN(von) && von > 0) {
            balance = von;
        }
        console.log(`${C.green}✓ Done${C.reset}`);

        let targetInput = await question(`${C.yellow}➤ Nhập số tiền muốn lời (0 = không giới hạn): ${C.reset}`);
        targetProfit = parseInt(targetInput.replace(/\./g, ""));
        if (isNaN(targetProfit) || targetProfit < 0) targetProfit = 0;

        let betInput = await question(`${C.yellow}➤ Mỗi tay bao nhiêu: ${C.reset}`);
        let bet = parseInt(betInput.replace(/\./g, ""));
        if (!isNaN(bet) && bet > 0 && bet <= balance) {
            betAmount = bet;
        }

        initialBalance = balance;

        rl.close();

        startAutoBet();
    } else {
        rl.close();
    }

    process.on("SIGINT", () => {
        console.log(`\n${C.yellow}⟳ Đang dừng bot...${C.reset}`);
        stopAutoBet();
        process.exit(0);
    });

    process.on("SIGTERM", () => {
        console.log(`\n${C.yellow}⟳ Đang dừng bot...${C.reset}`);
        stopAutoBet();
        process.exit(0);
    });
}

main();
