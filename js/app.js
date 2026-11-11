/* UI: screens, chalkboard drawing, word runner, audio, settings. Needs js/core.js. */
(function () {
'use strict';
var $ = function (id) { return document.getElementById(id); };
var REDUCED = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

/* ================= state ================= */
var DEFAULTS = { states: 4, alpha: 3, level: 2, showSink: false, tester: true, rounds: 5, mode: 'rounds', union: '|', music: true, volume: 0.6, sfx: true };
var STORE = 'ai-ve-dung-dfa';
var S = { screen: 'menu', settings: Object.assign({}, DEFAULTS), best: 0, bestEndless: 0, bestEndlessRounds: 0, game: null };

function loadStore() {
  try {
    var raw = JSON.parse(localStorage.getItem(STORE) || '{}');
    if (raw.settings) Object.keys(DEFAULTS).forEach(function (k) { if (typeof raw.settings[k] === typeof DEFAULTS[k]) S.settings[k] = raw.settings[k]; });
    ['best', 'bestEndless', 'bestEndlessRounds'].forEach(function (k) { if (typeof raw[k] === 'number') S[k] = raw[k]; });
  } catch (e) {}
  if (S.settings.mode !== 'endless') S.settings.mode = 'rounds';
  S.settings.states = Math.max(3, Math.min(8, S.settings.states | 0));
}
function saveStore() { try { localStorage.setItem(STORE, JSON.stringify({ settings: S.settings, best: S.best, bestEndless: S.bestEndless, bestEndlessRounds: S.bestEndlessRounds })); } catch (e) {} }

var WHO = ['Turing', 'Giesl'];
var QUIPS = ['Took me two minutes.', 'I tested five words. All fine.', 'This one is already minimal.', 'You can tell at a glance.', 'I checked it by hand, twice.', 'The other board has a wrong edge.', 'Trust me.', 'Count the states again.', 'I am sure about this one.', 'This is the clean way to draw it.'];
var LEVELS = {
  1: { name: 'Obvious', base: 100, hint: 'Both boards use the same layout. The mistake shows up on very short words.' },
  2: { name: 'Subtle', base: 150, hint: 'Both boards use the same layout. The mistake only changes the result on long words.' },
  3: { name: 'Shuffled', base: 200, hint: 'Each scientist names and arranges the states differently, so you cannot compare the pictures. The mistake only changes the result on long words.' }
};
var KIND = { redir: 'edge to the wrong state', del: 'missing edge', add: 'extra edge', swap: 'two labels swapped', relabel: 'wrong label on an edge', flip: 'misplaced double circle' };

function sigmaOf(n) { return n === 2 ? ['a', 'b'] : ['a', 'b', 'c']; }
function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
function fmt(n) { return String(Math.round(n)).replace(/\B(?=(\d{3})+(?!\d))/g, ','); }
function pl(n, w) { return n + ' ' + w + (n === 1 ? '' : 's'); }
function wordText(w, sigma) { return w.length ? w.map(function (x) { return sigma[x]; }).join('') : 'ε'; }

/* ================= drawing ================= */
var VW = 560, VH = 384, CX = 280, CY = 196;
function f1(v) { return v.toFixed(1); }
function qSvg(i) { return 'q<tspan dy="5" font-size="13">' + i + '</tspan>'; }
function qHtml(i) { return 'q<sub>' + i + '</sub>'; }

/* M: machine, board: {slot, names}, o: {sigma, hidden, bugEdges, bugStates, ghosts} */
function drawDfa(M, board, o) {
  var sigma = o.sigma, hidden = o.hidden, s, drawn = [];
  for (s = 0; s < M.n; s++) if (s !== hidden) drawn.push(s);
  var center = board.center == null ? -1 : board.center;
  var ring = drawn.filter(function (q) { return q !== center; }), m = ring.length;
  var r = drawn.length <= 5 ? 25 : drawn.length <= 6 ? 23 : 21;
  var rx = m <= 3 ? 150 : m === 4 ? 190 : 182, ry = m <= 3 ? 98 : m === 4 ? 128 : center >= 0 ? 118 : 112;
  var th0 = m === 4 ? Math.PI * 1.25 : Math.PI;
  var P = {};
  ring.forEach(function (q) { var th = th0 + 2 * Math.PI * board.slot[q] / m; P[q] = [CX + rx * Math.cos(th), CY + ry * Math.sin(th)]; });
  if (center >= 0) P[center] = [CX, CY];

  var groups = {}, order = [];
  function grp(a, b) { var k = a + '-' + b; if (!groups[k]) { groups[k] = { s: a, t: b, labels: [], cls: '' }; order.push(k); } return groups[k]; }
  drawn.forEach(function (q) { M.d[q].forEach(function (t, x) { if (t !== hidden) grp(q, t).labels.push(sigma[x]); }); });
  (o.bugEdges || []).forEach(function (e) { if (groups[e[0] + '-' + e[1]]) groups[e[0] + '-' + e[1]].cls = ' bug'; });
  (o.ghosts || []).forEach(function (g) {
    var k = g.s + '-' + g.t;
    if (groups[k]) { if (!g.onlyIfAbsent) groups[k].cls = ' bug'; }
    else { var G = grp(g.s, g.t); G.labels.push(g.label); G.cls = ' ghost'; }
  });

  var strokes = [], labels = [], placed = [];
  function head(tip, dx, dy) {
    var bx = tip[0] - dx * 11, by = tip[1] - dy * 11;
    return '<polygon points="' + f1(tip[0]) + ',' + f1(tip[1]) + ' ' + f1(bx - dy * 5) + ',' + f1(by + dx * 5) + ' ' + f1(bx + dy * 5) + ',' + f1(by - dx * 5) + '"/>';
  }
  function outward(p) {
    var dx = p[0] - CX, dy = p[1] - CY, l = Math.hypot(dx, dy);
    if (l < 1) { var g = th0 + Math.PI / m; return [Math.cos(g), Math.sin(g)]; } // centre state: aim between two ring states
    return [dx / l, dy / l];
  }

  // start arrow
  var p0 = P[0], u0 = outward(p0), a0 = Math.atan2(u0[1], u0[0]) + (groups['0-0'] ? 0.95 : 0);
  var sd = [Math.cos(a0), Math.sin(a0)];
  var sFrom = [p0[0] + sd[0] * (r + 38), p0[1] + sd[1] * (r + 38)], sTip = [p0[0] + sd[0] * (r + 4), p0[1] + sd[1] * (r + 4)];
  strokes.push('<g class="ed start"><path d="M' + f1(sFrom[0]) + ' ' + f1(sFrom[1]) + 'L' + f1(sTip[0] + sd[0] * 8) + ' ' + f1(sTip[1] + sd[1] * 8) + '"/>' + head(sTip, -sd[0], -sd[1]) + '</g>');
  placed.push([(sFrom[0] + sTip[0]) / 2, (sFrom[1] + sTip[1]) / 2]);

  function labelAt(x, y, g) {
    placed.push([x, y]);
    labels.push('<text class="el' + g.cls + '" data-e="' + g.s + '-' + g.t + '" x="' + f1(x) + '" y="' + f1(y + 6.5) + '">' + esc(g.labels.join(',')) + '</text>');
  }

  // self-loops first: their label position is fixed
  order.forEach(function (k) {
    var g = groups[k]; if (g.s !== g.t) return;
    var p = P[g.s], u = outward(p), phi = Math.atan2(u[1], u[0]), R = r * 2.75;
    var A = [p[0] + r * Math.cos(phi - 0.42), p[1] + r * Math.sin(phi - 0.42)];
    var B = [p[0] + (r + 3) * Math.cos(phi + 0.42), p[1] + (r + 3) * Math.sin(phi + 0.42)];
    var C1 = [p[0] + R * Math.cos(phi - 0.62), p[1] + R * Math.sin(phi - 0.62)];
    var C2 = [p[0] + R * Math.cos(phi + 0.62), p[1] + R * Math.sin(phi + 0.62)];
    var dx = B[0] - C2[0], dy = B[1] - C2[1], l = Math.hypot(dx, dy); dx /= l; dy /= l;
    var E = [B[0] - dx * 8, B[1] - dy * 8];
    strokes.push('<g class="ed' + g.cls + '" data-e="' + k + '"><path d="M' + f1(A[0]) + ' ' + f1(A[1]) + 'C' + f1(C1[0]) + ' ' + f1(C1[1]) + ' ' + f1(C2[0]) + ' ' + f1(C2[1]) + ' ' + f1(E[0]) + ' ' + f1(E[1]) + '"/>' + head(B, dx, dy) + '</g>');
    var ap = [(A[0] + 3 * C1[0] + 3 * C2[0] + B[0]) / 8, (A[1] + 3 * C1[1] + 3 * C2[1] + B[1]) / 8];
    labelAt(ap[0] + u[0] * 13, ap[1] + u[1] * 13, g);
  });

  order.forEach(function (k) {
    var g = groups[k]; if (g.s === g.t) return;
    var A = P[g.s], B = P[g.t], dx = B[0] - A[0], dy = B[1] - A[1], dist = Math.hypot(dx, dy);
    var ux = dx / dist, uy = dy / dist, nx = -uy, ny = ux;
    var both = !!groups[g.t + '-' + g.s];
    var bend = both ? Math.max(15, Math.min(30, dist * 0.14)) : 0;
    if (center >= 0 && g.s !== center && g.t !== center) {
      // keep chords clear of the state in the middle
      var along = (CX - A[0]) * ux + (CY - A[1]) * uy, off = (CX - A[0]) * nx + (CY - A[1]) * ny;
      var t0 = Math.max(0.2, Math.min(0.8, along / dist)), reach = 4 * t0 * (1 - t0), need = r + 17;
      if (along > 0 && along < dist && Math.abs(bend * reach - off) < need) bend = (bend * reach >= off ? off + need : off - need) / reach;
    }
    var mx = (A[0] + B[0]) / 2, my = (A[1] + B[1]) / 2;
    var C = [mx + nx * bend * 2, my + ny * bend * 2];
    var a = [C[0] - A[0], C[1] - A[1]], al = Math.hypot(a[0], a[1]);
    var b = [C[0] - B[0], C[1] - B[1]], bl = Math.hypot(b[0], b[1]);
    var Q0 = [A[0] + a[0] / al * r, A[1] + a[1] / al * r];
    var tip = [B[0] + b[0] / bl * (r + 3), B[1] + b[1] / bl * (r + 3)];
    var hd = [-b[0] / bl, -b[1] / bl];
    var Q1 = [tip[0] - hd[0] * 8, tip[1] - hd[1] * 8];
    strokes.push('<g class="ed' + g.cls + '" data-e="' + k + '"><path d="M' + f1(Q0[0]) + ' ' + f1(Q0[1]) + 'Q' + f1(C[0]) + ' ' + f1(C[1]) + ' ' + f1(Q1[0]) + ' ' + f1(Q1[1]) + '"/>' + head(tip, hd[0], hd[1]) + '</g>');
    // label: on the bend side, or the side away from the middle of the board
    var sx = nx, sy = ny;
    if (bend < 0) { sx = -nx; sy = -ny; }
    else if (bend === 0) {
      var d1 = Math.hypot(mx + nx * 14 - CX, my + ny * 14 - CY), d2 = Math.hypot(mx - nx * 14 - CX, my - ny * 14 - CY);
      if (d2 > d1 + 0.5) { sx = -nx; sy = -ny; }
    }
    var best = null, bestScore = -1e9, ts = [0.5, 0.4, 0.6, 0.3, 0.7, 0.22, 0.78];
    var cands = ts.map(function (t) { return [t, 1]; });
    if (!both) cands = cands.concat(ts.map(function (t) { return [t, -1]; }));
    cands.some(function (c) {
      var t = c[0];
      var x = (1 - t) * (1 - t) * Q0[0] + 2 * (1 - t) * t * C[0] + t * t * tip[0] + sx * 14 * c[1];
      var y = (1 - t) * (1 - t) * Q0[1] + 2 * (1 - t) * t * C[1] + t * t * tip[1] + sy * 14 * c[1];
      var score = 1e9;
      placed.forEach(function (q) { score = Math.min(score, Math.hypot(q[0] - x, q[1] - y) - 25); });
      drawn.forEach(function (q) { score = Math.min(score, Math.hypot(P[q][0] - x, P[q][1] - y) - (r + 11)); });
      if (score > bestScore) { bestScore = score; best = [x, y]; }
      return score >= 0;
    });
    labelAt(best[0], best[1], g);
  });

  var bugS = o.bugStates || [];
  drawn.forEach(function (q) {
    var p = P[q], cls = bugS.indexOf(q) >= 0 ? ' bug' : '';
    strokes.push('<g class="st' + cls + '" data-s="' + q + '"><circle cx="' + f1(p[0]) + '" cy="' + f1(p[1]) + '" r="' + r + '"/>' +
      (M.acc[q] ? '<circle class="inner" cx="' + f1(p[0]) + '" cy="' + f1(p[1]) + '" r="' + (r - 5) + '"/>' : '') + '</g>');
    labels.push('<text class="sl" data-s="' + q + '" x="' + f1(p[0]) + '" y="' + f1(p[1] + 5) + '">' + qSvg(board.names[q]) + '</text>');
  });

  return '<svg class="dfa" viewBox="0 0 ' + VW + ' ' + VH + '" role="img" aria-label="' + esc(o.title || 'DFA') + '">' +
    '<g filter="url(#chalk)">' + strokes.join('') + '</g><g>' + labels.join('') + '</g></svg>';
}

function avatar(i) {
  var hair = i === 0
    ? '<path d="M10 30c-3-13 4-22 14-22s17 9 14 22c-1-8-5-12-14-12s-13 4-14 12z" fill="#15302a"/>'
    : '<path d="M12 21c0-8 5-13 12-13s12 5 12 13c-3-4-7-6-12-6s-9 2-12 6z" fill="#15302a"/>';
  var specs = i === 0
    ? '<circle cx="18.5" cy="26.5" r="4.2"/><circle cx="29.5" cy="26.5" r="4.2"/><path d="M22.7 26.5h2.6"/>'
    : '<rect x="13.5" y="22.5" width="9" height="7" rx="1.5"/><rect x="25.5" y="22.5" width="9" height="7" rx="1.5"/><path d="M22.5 26h3"/>';
  var mouth = i === 0 ? '<path d="M19.5 35c2.8 2.2 6.2 2.2 9 0"/>' : '<path d="M19 35.5h10"/><path d="M17 33c2 6 12 6 14 0" opacity=".45"/>';
  return '<svg class="avatar" viewBox="0 0 48 48" aria-hidden="true"><circle cx="24" cy="24" r="22.5" fill="#f7f6ef"/>' + hair +
    '<g fill="none" stroke="#15302a" stroke-width="1.7" stroke-linecap="round">' + specs + mouth + '</g></svg>';
}

/* ================= running a word on boards ================= */
var runToken = 0;
function clearMarks(root) {
  root.querySelectorAll('.on, .stuck').forEach(function (el) { el.classList.remove('on'); el.classList.remove('stuck'); });
}
/* targets: [{root, M, board, hidden}], w: symbol indices */
function runWord(w, sigma, targets, opts) {
  opts = opts || {};
  var token = ++runToken;
  var paths = targets.map(function (t) { return Core.trace(t.M, w); });
  var tape = opts.tape;
  targets.forEach(function (t) { clearMarks(t.root); t.root.querySelector('[data-status]').innerHTML = '&nbsp;'; });
  function paintTape(i) {
    if (!tape) return;
    if (!w.length) { tape.innerHTML = '<span class="cur">ε</span>'; return; }
    tape.innerHTML = w.map(function (x, j) { return '<span class="' + (j < i - 1 ? 'done' : j === i - 1 ? 'cur' : '') + '">' + sigma[x] + '</span>'; }).join('');
  }
  function mark(i) {
    targets.forEach(function (t, k) {
      clearMarks(t.root);
      var path = paths[k], cur = path[i];
      // while the machine is in the undrawn dead state, keep pointing at where it got stuck
      var stuckAt = -1;
      for (var j = 0; j <= i; j++) if (path[j] === t.hidden) { stuckAt = j; break; }
      if (stuckAt >= 0) {
        t.root.querySelectorAll('[data-s="' + path[stuckAt - 1] + '"]').forEach(function (el) { el.classList.add('stuck'); });
        return;
      }
      t.root.querySelectorAll('[data-s="' + cur + '"]').forEach(function (el) { el.classList.add('on'); });
      if (i > 0) t.root.querySelectorAll('[data-e="' + path[i - 1] + '-' + cur + '"]').forEach(function (el) { el.classList.add('on'); });
    });
    paintTape(i);
  }
  function finish() {
    var word = esc(wordText(w, sigma));
    targets.forEach(function (t, k) {
      var path = paths[k], end = path[path.length - 1], st = t.root.querySelector('[data-status]');
      var stuckAt = path.indexOf(t.hidden);
      if (t.M.acc[end]) st.innerHTML = word + ' → <span class="ok">accepts</span>';
      else if (t.hidden >= 0 && stuckAt > 0) st.innerHTML = word + ' → <span class="no">rejects</span>, stuck at ' + qHtml(t.board.names[path[stuckAt - 1]]) + ' on ' + sigma[w[stuckAt - 1]];
      else st.innerHTML = word + ' → <span class="no">rejects</span>';
    });
    if (opts.done) opts.done();
  }
  var i = 0, delay = REDUCED ? 0 : (opts.delay || 430);
  (function step() {
    if (token !== runToken) return;
    if (REDUCED) i = w.length;
    mark(i);
    if (i >= w.length) { finish(); return; }
    i++;
    setTimeout(step, delay);
  })();
}

/* ================= audio ================= */
var Audio_ = (function () {
  var ctx = null, master = null, sfxGain = null, buf = null, el = null, loading = false, timer = 0, live = [], XF = 3.5;
  function ensure() {
    if (ctx) return true;
    var AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return false;
    try {
      ctx = new AC();
      master = ctx.createGain(); master.gain.value = 0; master.connect(ctx.destination);
      sfxGain = ctx.createGain(); sfxGain.gain.value = 0.5; sfxGain.connect(ctx.destination);
    } catch (e) { ctx = null; return false; }
    return true;
  }
  function schedule(at, first) {
    if (!buf || !S.settings.music) return;
    var src = ctx.createBufferSource(), g = ctx.createGain(), d = buf.duration, xf = Math.min(XF, d / 4);
    src.buffer = buf;
    g.gain.setValueAtTime(0, at);
    g.gain.linearRampToValueAtTime(1, at + (first ? 2 : xf));
    g.gain.setValueAtTime(1, at + d - xf);
    g.gain.linearRampToValueAtTime(0, at + d);
    src.connect(g); g.connect(master); src.start(at);
    live.push(src);
    src.onended = function () { live = live.filter(function (x) { return x !== src; }); };
    var next = at + d - xf;
    clearTimeout(timer);
    timer = setTimeout(function () { schedule(Math.max(next, ctx.currentTime + 0.05), false); }, Math.max(0, (next - ctx.currentTime - 6) * 1000));
  }
  function stopAll() {
    clearTimeout(timer);
    live.forEach(function (s) { try { s.stop(); } catch (e) {} });
    live = [];
  }
  function fallback() {
    try {
      el = new Audio('audio/ambient.mp3'); el.loop = true; el.volume = S.settings.volume;
      if (S.settings.music) el.play().catch(function () {});
    } catch (e) {}
  }
  function load() {
    if (loading) return; loading = true;
    fetch('audio/ambient.mp3').then(function (r) { if (!r.ok) throw new Error('http'); return r.arrayBuffer(); })
      .then(function (ab) { return new Promise(function (ok, no) { ctx.decodeAudioData(ab, ok, no); }); })
      .then(function (b) { buf = b; if (S.settings.music) schedule(ctx.currentTime + 0.05, true); })
      .catch(fallback);
  }
  /* call from a click */
  function apply() {
    var on = S.settings.music, vol = S.settings.volume;
    if (!ensure()) { if (!el) fallback(); if (el) { el.volume = vol; if (on) el.play().catch(function () {}); else el.pause(); } return; }
    if (ctx.state === 'suspended') ctx.resume().catch(function () {});
    master.gain.cancelScheduledValues(ctx.currentTime);
    master.gain.setTargetAtTime(on ? vol : 0, ctx.currentTime, 0.25);
    if (el) { el.volume = vol; if (on) el.play().catch(function () {}); else el.pause(); return; }
    if (!buf) { load(); return; }
    if (on && !live.length) schedule(ctx.currentTime + 0.05, true);
    if (!on) setTimeout(function () { if (!S.settings.music) stopAll(); }, 900);
  }
  function tone(freq, t0, dur, type, peak) {
    var o = ctx.createOscillator(), g = ctx.createGain();
    o.type = type; o.frequency.setValueAtTime(freq, t0);
    g.gain.setValueAtTime(0, t0); g.gain.linearRampToValueAtTime(peak, t0 + 0.015); g.gain.exponentialRampToValueAtTime(0.001, t0 + dur);
    o.connect(g); g.connect(sfxGain); o.start(t0); o.stop(t0 + dur + 0.05);
  }
  function sfx(good) {
    if (!S.settings.sfx || !ensure()) return;
    try {
      if (ctx.state === 'suspended') ctx.resume().catch(function () {});
      var t = ctx.currentTime + 0.02;
      if (good) { tone(659.3, t, 0.22, 'sine', 0.35); tone(987.8, t + 0.12, 0.4, 'sine', 0.3); }
      else { tone(207.7, t, 0.3, 'triangle', 0.35); tone(155.6, t + 0.14, 0.45, 'triangle', 0.3); }
    } catch (e) {}
  }
  return { apply: apply, sfx: sfx };
})();

/* ================= settings UI ================= */
function syncSettings() {
  var st = S.settings;
  document.querySelectorAll('[data-set]').forEach(function (inp) {
    var k = inp.dataset.set, ty = inp.dataset.type;
    if (ty === 'bool') inp.checked = !!st[k];
    else if (ty === 'pct') inp.value = Math.round(st[k] * 100);
    else inp.checked = String(st[k]) === inp.value;
  });
  document.querySelectorAll('[data-out="states"]').forEach(function (o) { o.textContent = st.states; });
  document.querySelectorAll('[data-step="states"]').forEach(function (b) { b.disabled = (b.dataset.d === '-1' && st.states <= 3) || (b.dataset.d === '1' && st.states >= 8); });
  document.querySelectorAll('[data-level-hint]').forEach(function (p) { p.textContent = LEVELS[st.level].hint; });
  document.querySelectorAll('[data-music]').forEach(function (b) { b.setAttribute('aria-pressed', st.music ? 'true' : 'false'); b.textContent = st.music ? 'Music: on' : 'Music: off'; });
  document.querySelectorAll('[data-mode-hint]').forEach(function (p) {
    p.textContent = st.mode === 'endless' ? 'Play until your first wrong pick. Your best score is saved.' : 'A game of ' + st.rounds + ' rounds. A wrong pick does not end it.';
  });
  var rec = [];
  if (S.bestEndless > 0) rec.push('Endless best: ' + fmt(S.bestEndless) + ' points over ' + pl(S.bestEndlessRounds, 'round'));
  if (S.best > 0) rec.push('Rounds best: ' + fmt(S.best) + ' points');
  $('record').textContent = rec.join(' · ');
}
function setSetting(k, v) {
  S.settings[k] = v; saveStore(); syncSettings();
  if (k === 'music' || k === 'volume') Audio_.apply();
  if (k === 'union' && S.game && S.game.cur) renderProblem();
  if (k === 'tester' && S.screen === 'game') renderTesterState();
}
document.addEventListener('change', function (e) {
  var inp = e.target; if (!inp.dataset || !inp.dataset.set) return;
  var ty = inp.dataset.type;
  setSetting(inp.dataset.set, ty === 'bool' ? inp.checked : ty === 'int' ? parseInt(inp.value, 10) : ty === 'pct' ? inp.value / 100 : inp.value);
});
document.addEventListener('input', function (e) {
  if (e.target.id === 's-volume') { S.settings.volume = e.target.value / 100; Audio_.apply(); }
});
document.addEventListener('click', function (e) {
  var b = e.target.closest('button'); if (!b) return;
  if (b.dataset.step) setSetting('states', Math.max(3, Math.min(8, S.settings.states + parseInt(b.dataset.d, 10))));
  else if (b.dataset.open) $(b.dataset.open).showModal();
  else if ('close' in b.dataset) b.closest('dialog').close();
  else if ('music' in b.dataset) setSetting('music', !S.settings.music);
});
$('btn-defaults').addEventListener('click', function () {
  Object.assign(S.settings, DEFAULTS); saveStore(); syncSettings(); Audio_.apply();
  if (S.game && S.game.cur) { renderProblem(); renderTesterState(); }
});
document.querySelectorAll('dialog').forEach(function (d) {
  d.addEventListener('click', function (e) { if (e.target === d) d.close(); });
});

/* ================= screens ================= */
function show(name) {
  S.screen = name;
  ['menu', 'game', 'end'].forEach(function (n) { $('screen-' + n).hidden = n !== name; });
  runToken++;
  if (name === 'menu') { syncSettings(); startDemo(); }
  window.scrollTo(0, 0);
}

/* menu demo: a*bc reading a few words */
var demo = null;
function startDemo() {
  if (!demo) {
    var sig = ['a', 'b', 'c'];
    var M = Core.regexToDfa(Core.cat([Core.star(Core.sym('a')), Core.sym('b'), Core.sym('c')]), sig);
    var names = {}; Core.drawnStates(M, true).forEach(function (s, i) { names[s] = i; });
    demo = { M: M, sig: sig, board: { slot: Core.bestSlots(M, true), names: names }, words: ['aabc', 'abcc', 'bc', 'aab'], i: 0 };
    $('demo-board').querySelector('[data-svg]').innerHTML = drawDfa(M, demo.board, { sigma: sig, hidden: M.sink, title: 'DFA for a*bc' });
  }
  var target = [{ root: $('demo-board'), M: demo.M, board: demo.board, hidden: demo.M.sink }];
  (function loop() {
    var w = demo.words[demo.i % demo.words.length].split('').map(function (c) { return demo.sig.indexOf(c); });
    demo.i++;
    runWord(w, demo.sig, target, {
      delay: 620,
      done: function () {
        if (REDUCED) return;
        var token = runToken;
        setTimeout(function () { if (token === runToken && S.screen === 'menu') loop(); }, 1900);
      }
    });
  })();
}

/* ================= game ================= */
function inProgress() { var g = S.game; return !!g && S.screen === 'game' && (g.round > 0 || (g.cur && g.cur.answered)); }

function newGame() {
  S.game = { round: 0, total: S.settings.rounds, endless: S.settings.mode === 'endless', score: 0, streak: 0, bestStreak: 0, history: [], recent: [], cur: null };
  dealRound();
  show('game');
  renderRound();
}
function dealRound() {
  var g = S.game, st = S.settings;
  var rd = Core.makeRound({ sigma: sigmaOf(st.alpha), states: st.states, showSink: st.showSink, level: st.level }, Math.random, g.recent);
  var q1 = Math.floor(Math.random() * QUIPS.length), q2 = (q1 + 1 + Math.floor(Math.random() * (QUIPS.length - 1))) % QUIPS.length;
  rd.quips = [q1, q2]; rd.answered = false; rd.pick = -1; rd.usedTester = false; rd.gained = 0;
  g.cur = rd; g.recent.push(Core.show(rd.regex));
}
function machineOf(rd, i) { return rd.boards[i].correct ? rd.dfa : rd.bad; }
function hiddenOf(rd) { return rd.hide ? rd.dfa.sink : -1; }
function targetsOf(rd) { return [0, 1].map(function (i) { return { root: $('board-' + i), M: machineOf(rd, i), board: rd.boards[i], hidden: hiddenOf(rd) }; }); }

function bugMarks(rd) {
  var mu = rd.mu, B = rd.bad, hidden = hiddenOf(rd), sig = rd.sigma, o = { bugEdges: [], bugStates: [], ghosts: [] };
  if (mu.kind === 'flip') o.bugStates.push(mu.s);
  else if (mu.kind === 'redir') { o.bugEdges.push([mu.s, mu.newT]); o.ghosts.push({ s: mu.s, t: mu.oldT, label: sig[mu.x], onlyIfAbsent: true }); }
  else if (mu.kind === 'add') o.bugEdges.push([mu.s, mu.newT]);
  else if (mu.kind === 'del') o.ghosts.push({ s: mu.s, t: mu.oldT, label: sig[mu.x] });
  else if (mu.kind === 'swap') o.bugEdges.push([mu.s, B.d[mu.s][mu.x]], [mu.s, B.d[mu.s][mu.y]]);
  else o.bugEdges.push([mu.s, B.d[mu.s][mu.x] === hidden ? B.d[mu.s][mu.y] : B.d[mu.s][mu.x]]);
  return o;
}
function explain(rd, wrongIdx) {
  var mu = rd.mu, M = rd.dfa, B = rd.bad, hidden = hiddenOf(rd), sig = rd.sigma, nm = rd.boards[wrongIdx].names, who = WHO[wrongIdx];
  var q = function (s) { return qHtml(nm[s]); };
  var c = function (x) { return '<code>' + sig[x] + '</code>'; };
  switch (mu.kind) {
    case 'flip': return B.acc[mu.s]
      ? q(mu.s) + ' is not an accepting state, but ' + who + ' drew a double circle.'
      : q(mu.s) + ' must be an accepting state. ' + who + ' forgot the double circle.';
    case 'redir': return 'From ' + q(mu.s) + ' on ' + c(mu.x) + ' the machine must go to ' + q(mu.oldT) + '. ' + who + ' sent it to ' + q(mu.newT) + '.';
    case 'del': return who + ' left out the edge ' + q(mu.s) + ' → ' + q(mu.oldT) + ' labelled ' + c(mu.x) + ' (dashed on the board).';
    case 'add': return 'From ' + q(mu.s) + ' on ' + c(mu.x) + ' the machine must reject. ' + who + ' drew an extra edge to ' + q(mu.newT) + '.';
    case 'swap': return 'At ' + q(mu.s) + ', the labels ' + c(mu.x) + ' and ' + c(mu.y) + ' are swapped.';
    default: {
      var right = M.d[mu.s][mu.x] === hidden ? mu.y : mu.x, wrong = right === mu.x ? mu.y : mu.x;
      return 'The edge ' + q(mu.s) + ' → ' + q(M.d[mu.s][right]) + ' must be labelled ' + c(right) + '. ' + who + ' wrote ' + c(wrong) + '.';
    }
  }
}

function renderProblem() {
  var g = S.game, rd = g.cur;
  $('regex').innerHTML = '<span class="L">L = </span>' + esc(Core.show(rd.regex, S.settings.union));
  var m = Core.drawnStates(rd.dfa, rd.hide).length;
  $('chips').innerHTML =
    '<span class="chip mono">Σ = {' + rd.sigma.join(', ') + '}</span>' +
    '<span class="chip">' + m + ' states</span>' +
    '<span class="chip">Trap: ' + LEVELS[rd.level].name + '</span>' +
    '<span class="chip">' + (rd.hide ? 'Missing edge = reject' : 'Complete DFA') + '</span>';
}
function renderHud() {
  var g = S.game;
  $('hud-round').textContent = g.endless ? 'Round ' + (g.round + 1) + ' · endless' : 'Round ' + (g.round + 1) + '/' + g.total;
  var best = g.endless ? S.bestEndless : S.best;
  $('hud-best-k').textContent = g.score > best ? 'New best' : g.endless ? 'Endless best' : 'Best';
  $('hud-best').textContent = fmt(Math.max(best, g.score));
  $('hud-score').textContent = fmt(g.score);
  $('hud-streak').textContent = g.streak;
  var pips = '';
  for (var i = 0; !g.endless && i < g.total; i++) {
    var h = g.history[i];
    pips += '<span class="pip ' + (h ? (h.ok ? 'ok' : 'no') : i === g.round ? 'cur' : '') + '"></span>';
  }
  $('pips').innerHTML = pips;
  $('pips').hidden = g.endless;
}
function renderTesterState() {
  var rd = S.game.cur;
  $('tester').hidden = !S.settings.tester && !rd.answered;
  $('keys').innerHTML = rd.sigma.map(function (c) { return '<button type="button" class="btn" data-key="' + c + '">' + c + '</button>'; }).join('');
  $('word').placeholder = 'e.g. ' + rd.sigma.join('') + rd.sigma[0];
  $('tester-note').textContent = rd.answered
    ? 'This round is scored. You can still run words to see where the two machines differ.'
    : rd.usedTester ? 'Leave it empty and press Run to test the empty word ε.'
    : 'Leave it empty and press Run to test the empty word ε. Finish the round without a test run for 50 bonus points.';
}
function renderBoards() {
  var rd = S.game.cur, hidden = hiddenOf(rd);
  [0, 1].forEach(function (i) {
    var el = $('board-' + i), b = rd.boards[i], o = { sigma: rd.sigma, hidden: hidden, title: 'DFA by Dr. ' + WHO[i] };
    if (rd.answered && !b.correct) Object.assign(o, bugMarks(rd));
    el.querySelector('[data-svg]').innerHTML = drawDfa(machineOf(rd, i), b, o);
    el.querySelector('[data-avatar]').innerHTML = avatar(i);
    el.querySelector('[data-who]').textContent = 'Dr. ' + WHO[i];
    el.querySelector('[data-quip]').textContent = '“' + QUIPS[rd.quips[i]] + '”';
    el.querySelector('[data-status]').innerHTML = '&nbsp;';
    el.classList.toggle('is-correct', rd.answered && b.correct);
    el.classList.toggle('is-wrong', rd.answered && !b.correct);
    el.classList.toggle('is-picked', rd.answered && rd.pick === i);
    var stamp = el.querySelector('[data-stamp]');
    stamp.hidden = !rd.answered; stamp.textContent = b.correct ? 'RIGHT' : 'WRONG';
    $('pick-' + i).disabled = rd.answered;
    $('pick-' + i).textContent = rd.answered && rd.pick === i ? 'You picked ' + WHO[i] : WHO[i] + ' is right';
  });
}
function renderVerdict() {
  var g = S.game, rd = g.cur, v = $('verdict');
  if (!rd.answered) { v.hidden = true; return; }
  var wrongIdx = rd.boards[0].correct ? 1 : 0, ok = rd.pick !== wrongIdx;
  var w = wordText(rd.witness, rd.sigma), badAcc = !rd.witnessInL;
  var last = g.endless ? !ok : g.round + 1 >= g.total;
  v.className = 'card verdict ' + (ok ? 'good' : 'bad');
  v.innerHTML =
    '<h2>' + (ok ? 'Correct.' : g.endless ? 'Wrong. Game over.' : 'Not quite.') + ' Dr. ' + WHO[wrongIdx] + ' drew it wrong.</h2>' +
    '<p><b>The mistake (' + KIND[rd.mu.kind] + '):</b> ' + explain(rd, wrongIdx) + '</p>' +
    '<p><b>Shortest counterexample:</b> <code>' + esc(w) + '</code> ' + (rd.witnessInL ? 'is in' : 'is not in') + ' L, yet ' + WHO[wrongIdx] + '’s machine ' + (badAcc ? 'accepts' : 'rejects') + ' it.</p>' +
    '<div class="verdict-actions">' +
    '<button type="button" class="btn btn-primary" id="btn-next">' + (last ? 'See results' : 'Next round') + '</button>' +
    '<button type="button" class="btn" id="btn-witness">Run the counterexample on both boards</button>' +
    '<span class="pts">' + (ok ? '+' + fmt(rd.gained) + ' points' : '+0 points') + '</span></div>';
  v.hidden = false;
}
function renderRound() {
  runToken++;
  $('word').value = ''; $('tape').innerHTML = '';
  renderHud(); renderProblem(); renderBoards(); renderVerdict(); renderTesterState();
}

function choose(i) {
  var g = S.game, rd = g && g.cur;
  if (!rd || rd.answered || S.screen !== 'game') return;
  var ok = rd.boards[i].correct;
  rd.answered = true; rd.pick = i;
  if (ok) {
    g.streak++; g.bestStreak = Math.max(g.bestStreak, g.streak);
    rd.gained = LEVELS[rd.level].base + Math.min(g.streak - 1, 4) * 25 + (rd.usedTester ? 0 : 50);
    g.score += rd.gained;
  } else g.streak = 0;
  g.history.push({ regex: rd.regex, ok: ok, pts: rd.gained, kind: rd.mu.kind });
  Audio_.sfx(ok);
  runToken++;
  renderHud(); renderBoards(); renderVerdict(); renderTesterState();
  $('tape').innerHTML = '';
  var v = $('verdict');
  if (v.scrollIntoView) v.scrollIntoView({ block: 'nearest', behavior: REDUCED ? 'auto' : 'smooth' });
}
function next() {
  var g = S.game;
  if (!g || !g.cur || !g.cur.answered) return;
  if (g.endless ? !g.history[g.history.length - 1].ok : g.round + 1 >= g.total) { endGame(); return; }
  g.round++; dealRound(); renderRound();
  window.scrollTo(0, 0);
}
function endGame() {
  var g = S.game, right = g.history.filter(function (h) { return h.ok; }).length;
  var record;
  if (g.endless) {
    record = g.score > S.bestEndless;
    if (record) { S.bestEndless = g.score; S.bestEndlessRounds = right; saveStore(); }
    $('end-title').textContent = right === 0 ? 'Caught in the very first round.' : 'Out in round ' + g.history.length + ' after ' + right + ' correct.';
    $('end-stats').innerHTML = '<span>points' + (record ? ' · new endless best' : '') + '</span>' +
      '<span>Survived <b>' + right + '</b> round' + (right === 1 ? '' : 's') + '</span>' +
      '<span>Endless best <b>' + fmt(S.bestEndless) + '</b> points, <b>' + S.bestEndlessRounds + '</b> round' + (S.bestEndlessRounds === 1 ? '' : 's') + '</span>';
  } else {
    record = g.score > S.best;
    if (record) { S.best = g.score; saveStore(); }
    $('end-title').textContent = right === g.total ? 'Nobody fooled you.' : right === 0 ? 'Trapped in all ' + g.total + ' rounds.' : right + '/' + g.total + ' rounds correct.';
    $('end-stats').innerHTML = '<span>points' + (record && g.score > 0 ? ' · new best' : '') + '</span>' +
      '<span>Longest streak <b>' + g.bestStreak + '</b></span><span>Best <b>' + fmt(S.best) + '</b></span>';
  }
  $('end-score').textContent = fmt(g.score);
  $('recap').innerHTML = g.history.map(function (h, i) {
    return '<li><span class="small">Round ' + (i + 1) + '</span><span class="rx">' + esc(Core.show(h.regex, S.settings.union)) + '</span>' +
      '<span class="trap">' + KIND[h.kind] + '</span><span class="pill ' + (h.ok ? 'ok' : 'no') + '">' + (h.ok ? 'Right, +' + fmt(h.pts) : 'Wrong') + '</span></li>';
  }).join('');
  show('end');
}

/* tester */
function cleanWord(v, sigma) { return v.toLowerCase().split('').filter(function (c) { return sigma.indexOf(c) >= 0; }).join('').slice(0, 24); }
function runTester(wordStr) {
  var g = S.game, rd = g && g.cur; if (!rd) return;
  var s = cleanWord(wordStr, rd.sigma);
  $('word').value = s;
  if (!rd.answered && !rd.usedTester) { rd.usedTester = true; renderTesterState(); }
  runWord(s.split('').map(function (c) { return rd.sigma.indexOf(c); }), rd.sigma, targetsOf(rd), { tape: $('tape') });
}
$('word').addEventListener('input', function () { var rd = S.game && S.game.cur; if (rd) { var c = cleanWord(this.value, rd.sigma); if (c !== this.value) this.value = c; } });
$('word').addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); e.stopPropagation(); runTester(this.value); } });
$('btn-run').addEventListener('click', function () { runTester($('word').value); });
$('btn-clear').addEventListener('click', function () { $('word').value = ''; $('tape').innerHTML = ''; $('word').focus(); });
$('keys').addEventListener('click', function (e) { var b = e.target.closest('[data-key]'); if (b) { var w = $('word'); if (w.value.length < 24) w.value += b.dataset.key; } });
$('verdict').addEventListener('click', function (e) {
  if (e.target.id === 'btn-next') next();
  else if (e.target.id === 'btn-witness') {
    var rd = S.game.cur;
    $('tester').hidden = false;
    runTester(rd.witness.map(function (x) { return rd.sigma[x]; }).join(''));
    $('board-0').scrollIntoView({ block: 'nearest', behavior: REDUCED ? 'auto' : 'smooth' });
  }
});
$('pick-0').addEventListener('click', function () { choose(0); });
$('pick-1').addEventListener('click', function () { choose(1); });

/* navigation */
var confirmAction = null;
function askLeave(title, action) {
  if (!inProgress()) { action(); return; }
  $('confirm-title').textContent = title; confirmAction = action; $('dlg-confirm').showModal();
}
$('confirm-yes').addEventListener('click', function () { $('dlg-confirm').close(); var a = confirmAction; confirmAction = null; if (a) a(); });
$('btn-start').addEventListener('click', function () { Audio_.apply(); newGame(); });
$('btn-again').addEventListener('click', newGame);
$('btn-restart').addEventListener('click', function () { askLeave('Restart from round 1?', newGame); });
$('btn-menu').addEventListener('click', function () { askLeave('Abandon this game?', function () { S.game = null; show('menu'); }); });
$('btn-end-menu').addEventListener('click', function () { S.game = null; show('menu'); });

document.addEventListener('keydown', function (e) {
  if (S.screen !== 'game' || document.querySelector('dialog[open]')) return;
  var tag = (e.target.tagName || '').toLowerCase();
  if (tag === 'input' || tag === 'select' || tag === 'textarea') return;
  if (e.key === '1') choose(0);
  else if (e.key === '2') choose(1);
  else if (e.key === 'Enter' && tag !== 'button' && S.game && S.game.cur && S.game.cur.answered) next();
});

/* the first click anywhere may start the music */
document.addEventListener('click', function first() { document.removeEventListener('click', first, true); Audio_.apply(); }, true);

/* ================= boot ================= */
function start() {
  loadStore();
  syncSettings();
  show('menu');
}
start();
})();
