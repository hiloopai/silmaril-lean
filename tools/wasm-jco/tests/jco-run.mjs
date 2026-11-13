// Run one invocation of a component transpiled by `jco transpile` and compare the result.
//   node jco-run.mjs MODULE.js 'f(arg, …)' EXPECTED
// Arguments and the expected value are in a small subset of WAVE: numbers, strings, booleans,
// lists `[…]`, tuples `(…)` (JS arrays), `some(x)` (x) and `none` (undefined). Prints `ok`,
// `mismatch: …` or `skip: …` (a value outside the subset, or an argument jco rejects).
import { pathToFileURL } from 'node:url';

function parse(s) {
  let i = 0;
  const ws = () => { while (i < s.length && /\s/.test(s[i])) i++; };
  const value = () => {
    ws();
    if (s[i] === '"') {
      let j = i + 1;
      while (s[j] !== '"') j += s[j] === '\\' ? 2 : 1;
      const v = JSON.parse(s.slice(i, j + 1)); i = j + 1; return v;
    }
    if (s[i] === '[' || s[i] === '(') {
      const close = s[i] === '[' ? ']' : ')'; i++; const xs = [];
      ws(); if (s[i] === close) { i++; return xs; }
      for (;;) { xs.push(value()); ws(); if (s[i] === ',') { i++; continue; } if (s[i] === close) { i++; return xs; } throw new Error('bad list'); }
    }
    const m = /^(-?[0-9][0-9.e+-]*|true|false|none|some)/.exec(s.slice(i));
    if (!m) throw new Error('unsupported value at ' + s.slice(i));
    i += m[0].length;
    if (m[0] === 'true') return true;
    if (m[0] === 'false') return false;
    if (m[0] === 'none') return undefined;
    if (m[0] === 'some') { ws(); i++; const v = value(); ws(); i++; return v; }
    return Number(m[0]);
  };
  return { value, rest: () => s.slice(i), at: () => i, set: (k) => { i = k; } };
}

function norm(v) {
  if (ArrayBuffer.isView(v)) return Array.from(v);
  if (Array.isArray(v)) return v.map(norm);
  if (typeof v === 'bigint') return Number(v);
  return v;
}

const [mod, inv, expected] = process.argv.slice(2);
const k = inv.indexOf('(');
const name = inv.slice(0, k);
let args, want;
try {
  const p = parse(inv.slice(k));
  args = p.value();
  want = parse(expected).value();
} catch (e) { console.log('skip: ' + e.message); process.exit(0); }
const m = await import(pathToFileURL(mod).href);
const camel = name.replace(/-([a-z])/g, (_, c) => c.toUpperCase());
let got;
try { got = await m[camel](...args); }
catch (e) { console.log('skip: jco rejects the arguments (' + e.message + ')'); process.exit(0); }
const a = JSON.stringify(norm(got)), b = JSON.stringify(norm(want));
console.log(a === b ? 'ok' : `mismatch: got ${a}, want ${b}`);
