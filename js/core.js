/* Core: regex -> minimal DFA, near-miss mutants, shortest counterexample, circular layout.
   Pure functions on plain JSON so a round can be snapshotted. */
var Core = (function () {
  'use strict';

  /* ---------- regex AST ---------- */
  var sym = function (c) { return { t: 'sym', c: c }; };
  var star = function (x) { return { t: 'star', x: x }; };
  var alt = function (xs) { return { t: 'alt', xs: xs }; };
  function cat(xs) {
    var flat = [];
    xs.forEach(function (x) { if (x.t === 'cat') flat.push.apply(flat, x.xs); else flat.push(x); });
    return flat.length === 1 ? flat[0] : { t: 'cat', xs: flat };
  }
  var PREC = { alt: 0, cat: 1, star: 2, sym: 3 };

  function show(r, union, ctx) {
    union = union || '|'; ctx = ctx || 0;
    var s;
    if (r.t === 'sym') s = r.c;
    else if (r.t === 'star') s = show(r.x, union, 3) + '*';
    else if (r.t === 'cat') s = r.xs.map(function (x) { return show(x, union, 1); }).join('');
    else s = r.xs.map(function (x) { return show(x, union, 0); }).join(union === '+' ? ' + ' : '|');
    return PREC[r.t] < ctx ? '(' + s + ')' : s;
  }

  function randRegex(rng, sigma, size) {
    var pick = function (a) { return a[Math.floor(rng() * a.length)]; };
    var L = function () { return sym(pick(sigma)); };
    function group() {
      var k = rng();
      if (k < 0.6) {
        var a = pick(sigma);
        var b = pick(sigma.filter(function (c) { return c !== a; }));
        if (a > b) { var t = a; a = b; b = t; }
        if (rng() < 0.3) return alt([sym(a), cat([sym(b), L()])]);
        return alt([sym(a), sym(b)]);
      }
      return cat([L(), L()]);
    }
    function factor() {
      var k = rng();
      if (k < 0.5) return L();
      if (k < 0.68) return star(L());
      if (k < 0.87) return star(group());
      var g = group();
      return g.t === 'alt' ? g : star(g);
    }
    function seq(n) {
      var xs = [];
      for (var i = 0; i < n; i++) {
        var f = factor();
        var prev = xs[xs.length - 1];
        if (prev && prev.t === 'star' && f.t === 'star' && show(prev) === show(f)) f = L();
        xs.push(f);
      }
      return cat(xs);
    }
    var r = seq(size);
    if (rng() < 0.08 && size >= 2) r = alt([r, seq(1 + Math.floor(rng() * 2))]);
    return r;
  }

  /* ---------- regex -> NFA -> DFA ---------- */
  function toNfa(r) {
    var eps = [], tr = [];
    var ns = function () { eps.push([]); tr.push([]); return eps.length - 1; };
    function go(r) {
      var s, e, p;
      if (r.t === 'sym') { s = ns(); e = ns(); tr[s].push([r.c, e]); return [s, e]; }
      if (r.t === 'cat') {
        var first = -1, last = -1;
        r.xs.forEach(function (x) { p = go(x); if (first < 0) first = p[0]; else eps[last].push(p[0]); last = p[1]; });
        return [first, last];
      }
      s = ns(); e = ns();
      if (r.t === 'alt') { r.xs.forEach(function (x) { p = go(x); eps[s].push(p[0]); eps[p[1]].push(e); }); return [s, e]; }
      p = go(r.x); eps[s].push(p[0], e); eps[p[1]].push(p[0], e);
      return [s, e];
    }
    var se = go(r);
    return { eps: eps, tr: tr, s: se[0], e: se[1] };
  }

  function closure(nfa, set) {
    var seen = {}, stack = set.slice(), out = [];
    while (stack.length) {
      var q = stack.pop();
      if (seen[q]) continue;
      seen[q] = 1; out.push(q);
      nfa.eps[q].forEach(function (t) { if (!seen[t]) stack.push(t); });
    }
    return out.sort(function (a, b) { return a - b; });
  }

  function regexToDfa(r, sigma) {
    var nfa = toNfa(r);
    var start = closure(nfa, [nfa.s]);
    var ids = {}; ids[start.join(',')] = 0;
    var sets = [start], d = [], acc = [];
    for (var i = 0; i < sets.length; i++) {
      var S = sets[i];
      acc[i] = S.indexOf(nfa.e) >= 0;
      d[i] = sigma.map(function (c) {
        var mv = [];
        S.forEach(function (q) { nfa.tr[q].forEach(function (e) { if (e[0] === c) mv.push(e[1]); }); });
        var T = closure(nfa, mv), k = T.join(',');
        if (!(k in ids)) { ids[k] = sets.length; sets.push(T); }
        return ids[k];
      });
    }
    return minimize({ n: sets.length, acc: acc, d: d });
  }

  /* Moore minimisation; start state is 0; result is numbered in BFS order. */
  function minimize(M) {
    var seen = [0], idx = { 0: 0 }, i, s;
    for (i = 0; i < seen.length; i++) M.d[seen[i]].forEach(function (t) { if (!(t in idx)) { idx[t] = seen.length; seen.push(t); } });
    var n = seen.length;
    var acc = seen.map(function (q) { return M.acc[q]; });
    var d = seen.map(function (q) { return M.d[q].map(function (t) { return idx[t]; }); });
    var block = acc.map(function (a) { return a ? 1 : 0; });
    var nb = acc.some(Boolean) && !acc.every(Boolean) ? 2 : 1;
    for (;;) {
      var sig = {}, cnt = 0, nbk = [];
      for (s = 0; s < n; s++) {
        var key = block[s] + '|' + d[s].map(function (t) { return block[t]; }).join(',');
        if (!(key in sig)) sig[key] = cnt++;
        nbk[s] = sig[key];
      }
      block = nbk;
      if (cnt === nb) break;
      nb = cnt;
    }
    var rep = [];
    for (s = 0; s < n; s++) if (rep[block[s]] === undefined) rep[block[s]] = s;
    var order = [block[0]], pos = {}; pos[block[0]] = 0;
    for (i = 0; i < order.length; i++) d[rep[order[i]]].forEach(function (t) {
      var b = block[t];
      if (!(b in pos)) { pos[b] = order.length; order.push(b); }
    });
    var nacc = order.map(function (b) { return acc[rep[b]]; });
    var nd = order.map(function (b) { return d[rep[b]].map(function (t) { return pos[block[t]]; }); });
    var sink = -1;
    for (s = 0; s < order.length; s++) if (!nacc[s] && nd[s].every(function (t) { return t === s; })) sink = s;
    return { n: order.length, acc: nacc, d: nd, sink: sink };
  }

  /* Shortest word on which A and B disagree (array of symbol indices), or null if equivalent. */
  function distinguish(A, B) {
    var k = A.d[0].length, seen = {}, queue = [[0, 0, null, -1]];
    seen['0,0'] = 1;
    for (var i = 0; i < queue.length; i++) {
      var cur = queue[i];
      if (A.acc[cur[0]] !== B.acc[cur[1]]) {
        var w = [];
        for (var c = cur; c[2]; c = c[2]) w.push(c[3]);
        return w.reverse();
      }
      for (var x = 0; x < k; x++) {
        var p = A.d[cur[0]][x], q = B.d[cur[1]][x], key = p + ',' + q;
        if (!seen[key]) { seen[key] = 1; queue.push([p, q, cur, x]); }
      }
    }
    return null;
  }

  /* Path of states visited (length w+1). */
  function trace(M, w) {
    var s = 0, path = [0];
    w.forEach(function (x) { s = M.d[s][x]; path.push(s); });
    return path;
  }
  function accepts(M, w) { var p = trace(M, w); return M.acc[p[p.length - 1]]; }

  /* ---------- near-miss mutants ---------- */
  function applyMutation(M, mu) {
    var N = { n: M.n, acc: M.acc.slice(), d: M.d.map(function (r) { return r.slice(); }), sink: M.sink };
    if (mu.kind === 'flip') N.acc[mu.s] = !N.acc[mu.s];
    else if (mu.kind === 'swap' || mu.kind === 'relabel') { N.d[mu.s][mu.x] = M.d[mu.s][mu.y]; N.d[mu.s][mu.y] = M.d[mu.s][mu.x]; }
    else N.d[mu.s][mu.x] = mu.newT;
    return N;
  }

  function mutants(M, hideSink) {
    var out = [], n = M.n, k = M.d[0].length;
    var hidden = hideSink ? M.sink : -1;
    for (var s = 0; s < n; s++) {
      if (s === hidden) continue;
      for (var x = 0; x < k; x++) {
        var old = M.d[s][x];
        for (var t = 0; t < n; t++) {
          if (t === old) continue;
          var kind = hidden >= 0 && old === hidden ? 'add' : hidden >= 0 && t === hidden ? 'del' : 'redir';
          out.push({ kind: kind, s: s, x: x, oldT: old, newT: t });
        }
        for (var y = x + 1; y < k; y++) {
          if (M.d[s][x] === M.d[s][y]) continue;
          var rel = hidden >= 0 && (M.d[s][x] === hidden || M.d[s][y] === hidden);
          out.push({ kind: rel ? 'relabel' : 'swap', s: s, x: x, y: y });
        }
      }
      out.push({ kind: 'flip', s: s });
    }
    var good = [], rest = [];
    out.forEach(function (mu) {
      var N = applyMutation(M, mu);
      var w = distinguish(M, N);
      if (!w) return;
      mu.dfa = N; mu.witness = w; mu.witnessInL = accepts(M, w);
      (minimize(N).n === n ? good : rest).push(mu);
    });
    return good.length ? good : rest;
  }

  function chooseMutant(M, hideSink, level, rng) {
    var c = mutants(M, hideSink);
    if (!c.length) return null;
    c.sort(function (a, b) { return a.witness.length - b.witness.length; });
    var lens = c.map(function (m) { return m.witness.length; });
    var q = function (p) { return lens[Math.min(lens.length - 1, Math.floor(p * lens.length))]; };
    var band;
    if (level <= 1) { var hi = q(0.3); band = c.filter(function (m) { return m.witness.length <= hi; }); }
    else { var lo = q(level === 2 ? 0.55 : 0.75); band = c.filter(function (m) { return m.witness.length >= lo; }); }
    var kinds = {};
    band.forEach(function (m) { (kinds[m.kind] = kinds[m.kind] || []).push(m); });
    var names = Object.keys(kinds);
    var pool = kinds[names[Math.floor(rng() * names.length)]];
    return pool[Math.floor(rng() * pool.length)];
  }

  /* ---------- layout: order of drawn states around an ellipse ---------- */
  function drawnStates(M, hideSink) {
    var out = [];
    for (var s = 0; s < M.n; s++) if (!(hideSink && s === M.sink)) out.push(s);
    return out;
  }

  /* Returns slot[state] (0..m-1) for drawn states, start in slot 0; fewest crossings, short chords. */
  function bestSlots(M, hideSink, center) {
    var drawn = drawnStates(M, hideSink).filter(function (s) { return s !== center; }), m = drawn.length, li = {};
    drawn.forEach(function (s, i) { li[s] = i; });
    var pairs = [], seen = {};
    drawn.forEach(function (s) {
      M.d[s].forEach(function (t) {
        if (t === s || !(t in li)) return;
        var a = Math.min(li[s], li[t]), b = Math.max(li[s], li[t]), key = a + '-' + b;
        if (!seen[key]) { seen[key] = 1; pairs.push([a, b]); }
      });
    });
    var perm = [], best = null, bestCost = Infinity, P = pairs.length;
    for (var i = 0; i < m; i++) perm.push(i);
    var lo = new Array(P), hi = new Array(P);
    function cost() {
      var c = 0, i, j;
      for (i = 0; i < P; i++) {
        var a = perm[pairs[i][0]], b = perm[pairs[i][1]];
        lo[i] = a < b ? a : b; hi[i] = a < b ? b : a;
        var dist = hi[i] - lo[i]; if (m - dist < dist) dist = m - dist;
        c += dist * dist;
      }
      for (i = 0; i < P; i++) for (j = i + 1; j < P; j++) {
        if ((lo[i] < lo[j] && lo[j] < hi[i] && hi[i] < hi[j]) || (lo[j] < lo[i] && lo[i] < hi[j] && hi[j] < hi[i])) c += 7;
      }
      for (i = 0; i < m; i++) c += 0.01 * Math.abs(perm[i] - i);
      return c;
    }
    (function rec(k) {
      if (k === m) { var c = cost(); if (c < bestCost) { bestCost = c; best = perm.slice(); } return; }
      for (var i = k; i < m; i++) {
        var t = perm[k]; perm[k] = perm[i]; perm[i] = t;
        rec(k + 1);
        t = perm[k]; perm[k] = perm[i]; perm[i] = t;
      }
    })(1);
    var slot = {};
    drawn.forEach(function (s, i) { slot[s] = best[i]; });
    return slot;
  }

  /* ---------- a full round ---------- */
  function usesAll(r, sigma) { var s = show(r); return sigma.every(function (c) { return s.indexOf(c) >= 0; }); }

  function makeRound(opts, rng, avoid) {
    rng = rng || Math.random; avoid = avoid || [];
    var sigma = opts.sigma, N = opts.states, hide = !opts.showSink;
    var maxLen = 8 + 2 * N, found = null, fallback = null, fbGap = 99;
    for (var tries = 0; tries < 6000 && !found; tries++) {
      var size = 1 + Math.floor(rng() * Math.min(7, N + 1));
      var r = randRegex(rng, sigma, size);
      var text = show(r);
      if (text.length > maxLen || !usesAll(r, sigma) || avoid.indexOf(text) >= 0) continue;
      var M = regexToDfa(r, sigma);
      var live = M.n - (hide && M.sink >= 0 ? 1 : 0);
      if (!M.acc.some(Boolean)) continue;
      if (live === N) found = { r: r, M: M };
      else if (Math.abs(live - N) < fbGap) { fbGap = Math.abs(live - N); fallback = { r: r, M: M }; }
    }
    found = found || fallback;
    var M0 = found.M;
    var mu = chooseMutant(M0, hide, opts.level, rng);
    var drawn = drawnStates(M0, hide);
    // a drawn dead state sits in the middle of the ring: everything falls into it
    var center = !hide && M0.sink >= 0 && drawn.length >= 5 ? M0.sink : -1;
    var ring = drawn.filter(function (s) { return s !== center; }), m = ring.length;
    var slot = bestSlots(M0, hide, center);
    var names = {}; drawn.forEach(function (s, i) { names[s] = i; });
    if (hide && M0.sink >= 0) names[M0.sink] = m;
    var correctSide = rng() < 0.5 ? 0 : 1;
    var boards = [0, 1].map(function (side) {
      var b = { correct: side === correctSide, slot: slot, names: names, center: center };
      if (opts.level >= 3) {
        // same machine, different drawing: rotate / mirror the ring and rename the states
        var shift = Math.floor(rng() * m), mirror = rng() < 0.5;
        var sl = {}, nm = {}, perm = drawn.map(function (_, i) { return i; });
        for (var i = perm.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        ring.forEach(function (s) { sl[s] = ((mirror ? m - slot[s] : slot[s]) + shift) % m; });
        drawn.forEach(function (s, i) { nm[s] = perm[i]; });
        if (hide && M0.sink >= 0) nm[M0.sink] = m;
        b.slot = sl; b.names = nm;
      }
      return b;
    });
    if (opts.level >= 3) {
      // make sure the two drawings are not accidentally identical
      var same = ring.every(function (s) { return boards[0].slot[s] === boards[1].slot[s]; });
      if (same && m > 1) ring.forEach(function (s) { boards[1].slot[s] = (boards[1].slot[s] + 1) % m; });
    }
    return {
      regex: found.r, sigma: sigma, hide: hide, level: opts.level,
      dfa: M0,
      bad: mu.dfa,
      mu: { kind: mu.kind, s: mu.s, x: mu.x, y: mu.y, oldT: mu.oldT, newT: mu.newT },
      witness: mu.witness, witnessInL: mu.witnessInL,
      boards: boards
    };
  }

  return {
    sym: sym, star: star, alt: alt, cat: cat, show: show, randRegex: randRegex,
    regexToDfa: regexToDfa, minimize: minimize, distinguish: distinguish,
    trace: trace, accepts: accepts, mutants: mutants, applyMutation: applyMutation,
    drawnStates: drawnStates, bestSlots: bestSlots, makeRound: makeRound
  };
})();
if (typeof module !== 'undefined') module.exports = Core;
