const C = require('../js/core.js');
const assert = require('assert');

function rng32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }

// 1. known language: a*bc
const abc = ['a', 'b', 'c'];
const r1 = C.cat([C.star(C.sym('a')), C.sym('b'), C.sym('c')]);
assert.strictEqual(C.show(r1), 'a*bc');
const M1 = C.regexToDfa(r1, abc);
assert.strictEqual(M1.n, 4); assert.ok(M1.sink >= 0);
const w = s => [...s].map(c => abc.indexOf(c));
for (const [s, exp] of [['bc', true], ['aaabc', true], ['abcc', false], ['', false], ['b', false], ['abca', false]]) assert.strictEqual(C.accepts(M1, w(s)), exp, s);

// 2. (a|b)*abb -> 4 states, no sink
const r2 = C.cat([C.star(C.alt([C.sym('a'), C.sym('b')])), C.sym('a'), C.sym('b'), C.sym('b')]);
assert.strictEqual(C.show(r2), '(a|b)*abb'); assert.strictEqual(C.show(r2, '+'), '(a + b)*abb');
const M2 = C.regexToDfa(r2, ['a', 'b']);
assert.strictEqual(M2.n, 4); assert.strictEqual(M2.sink, -1);

// 3. DFA vs brute-force regex matching through JS RegExp on random regexes
const rng = rng32(42);
for (let i = 0; i < 400; i++) {
  const r = C.randRegex(rng, abc, 1 + Math.floor(rng() * 5));
  const re = new RegExp('^(?:' + C.show(r) + ')$');
  const M = C.regexToDfa(r, abc);
  for (let j = 0; j < 60; j++) {
    const len = Math.floor(rng() * 7); let s = '';
    for (let k = 0; k < len; k++) s += abc[Math.floor(rng() * 3)];
    assert.strictEqual(C.accepts(M, w(s)), re.test(s), C.show(r) + ' on "' + s + '"');
  }
}

// 4. rounds: every combination of settings
let stats = {};
for (const sigma of [['a', 'b'], abc]) for (const showSink of [false, true]) for (let N = 3; N <= 8; N++) for (const level of [1, 2, 3]) {
  let exact = 0, t0 = Date.now(), wl = 0, kinds = {};
  const R = 40;
  for (let i = 0; i < R; i++) {
    const rd = C.makeRound({ sigma, states: N, showSink, level }, rng);
    const live = C.drawnStates(rd.dfa, rd.hide).length;
    if (live === N) exact++;
    // the wrong machine must really differ, and the witness must prove it
    const dw = C.distinguish(rd.dfa, rd.bad);
    assert.ok(dw, 'mutant equivalent');
    assert.deepStrictEqual(dw, rd.witness);
    assert.notStrictEqual(C.accepts(rd.dfa, rd.witness), C.accepts(rd.bad, rd.witness));
    assert.strictEqual(C.accepts(rd.dfa, rd.witness), rd.witnessInL);
    // regex and correct machine agree
    const re = new RegExp('^(?:' + C.show(rd.regex) + ')$');
    for (let j = 0; j < 40; j++) { const len = Math.floor(rng() * 8); let s = ''; for (let k = 0; k < len; k++) s += sigma[Math.floor(rng() * sigma.length)]; assert.strictEqual(C.accepts(rd.dfa, [...s].map(c => sigma.indexOf(c))), re.test(s)); }
    // exactly one correct board; slots are a permutation
    assert.strictEqual(rd.boards.filter(b => b.correct).length, 1);
    for (const b of rd.boards) { const sl = C.drawnStates(rd.dfa, rd.hide).filter(s => s !== b.center).map(s => b.slot[s]).sort((a, c) => a - c); assert.deepStrictEqual(sl, sl.map((_, i) => i)); const nm = C.drawnStates(rd.dfa, rd.hide).map(s => b.names[s]).sort((a, c) => a - c); assert.deepStrictEqual(nm, nm.map((_, i) => i)); }
    if (rd.hide && rd.dfa.sink >= 0) assert.ok(rd.bad.d[rd.dfa.sink].every(t => t === rd.dfa.sink) && !rd.bad.acc[rd.dfa.sink]);
    JSON.parse(JSON.stringify(rd));
    wl += rd.witness.length; kinds[rd.mu.kind] = (kinds[rd.mu.kind] || 0) + 1;
  }
  const key = `|Σ|=${sigma.length} sink=${showSink ? 'shown' : 'hidden'} N=${N} L${level}`;
  stats[key] = `exact ${exact}/${R}  ${((Date.now() - t0) / R).toFixed(1)}ms/round  avg witness ${(wl / R).toFixed(1)}  ${JSON.stringify(kinds)}`;
}
console.log(Object.keys(stats).length + ' setting combinations checked');
console.log('samples:');
for (let i = 0; i < 12; i++) { const rd = C.makeRound({ sigma: abc, states: 3 + (i % 6), showSink: false, level: 1 + (i % 3) }, rng); console.log(' ', C.show(rd.regex).padEnd(22), 'N=' + C.drawnStates(rd.dfa, true).length, rd.mu.kind, 'witness=' + (rd.witness.map(x => abc[x]).join('') || 'ε')); }
console.log('ALL OK');
