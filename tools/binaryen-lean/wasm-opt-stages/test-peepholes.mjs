// Differential smoke test for wasm-opt's peephole and local-variable stages.
//
// Builds small core modules by hand (no wat2wasm needed), runs
// all verified stages plus silmaril's vacuum for two rounds (or the given options), then with Node's WebAssembly engine
// checks that the output validates and that every export returns the same results
// as the input on a fixed set of edge-case and pseudo-random arguments.
//
// usage: node tools/wasm-opt/test-peepholes.mjs [path/to/wasm-opt] [extra args...]
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const exe = process.argv[2] ?? ".lake/build/bin/wasm-opt";
const extra = process.argv.length > 3 ? process.argv.slice(3) : ["--neutral-ops", "--eqz-pair", "--rse-line", "--drop-get", "--vacuum", "--tee-form", "--rounds", "2"];

const uleb = (n) => { const out = []; do { let b = n & 0x7f; n >>>= 7; if (n) b |= 0x80; out.push(b); } while (n); return out; };
const sleb = (v) => { v = BigInt(v); const out = []; for (;;) { const b = Number(v & 0x7fn); v >>= 7n;
  if ((v === 0n && !(b & 0x40)) || (v === -1n && (b & 0x40))) { out.push(b); return out; } out.push(b | 0x80); } };
const vec = (items) => [...uleb(items.length), ...items.flat()];
const section = (id, body) => [id, ...uleb(body.length), ...body];
const str = (s) => vec([...Buffer.from(s)].map((b) => [b]));
const I32 = 0x7f, I64 = 0x7e;
const op = { get: 0x20, set: 0x21, tee: 0x22, c32: 0x41, c64: 0x42, block: 0x02, end: 0x0b, br_if: 0x0d, select: 0x1b, drop: 0x1a, i32: { add: 0x6a, sub: 0x6b, mul: 0x6c, and: 0x71, or: 0x72, xor: 0x73,
  shl: 0x74, shr_s: 0x75, shr_u: 0x76, rotl: 0x77, rotr: 0x78, eqz: 0x45, eq: 0x46, clz: 0x67, lt_u: 0x49 },
  i64: { add: 0x7c, sub: 0x7d, mul: 0x7e, and: 0x83, or: 0x84, xor: 0x85, shl: 0x86, shr_s: 0x87, shr_u: 0x88,
    rotl: 0x89, rotr: 0x8a, eqz: 0x50, eq: 0x51, clz: 0x79 } };
const get = (i) => [op.get, ...uleb(i)];
const c32 = (v) => [op.c32, ...sleb(v)];
const c64 = (v) => [op.c64, ...sleb(v)];

function module(funcs) {
  const types = funcs.map((f) => [0x60, ...vec(f.params.map((t) => [t])), ...vec(f.results.map((t) => [t]))]);
  const bodies = funcs.map((f) => { const loc = f.locals ? [0x01, f.locals, I32] : [0x00]; const b = [...loc, ...f.code, 0x0b]; return [...uleb(b.length), ...b]; });
  return Uint8Array.from([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    ...section(1, vec(types)), ...section(3, vec(funcs.map((_, i) => uleb(i)))),
    ...section(7, vec(funcs.map((f, i) => [...str(f.name), 0x00, ...uleb(i)]))),
    ...section(10, vec(bodies))]);
}

const cases = [
  // name, params, results, code; comments state the expected rewrite.
  { name: "mul_add0", params: [I32, I32], results: [I32], code: [...get(1), ...get(0), ...c32(0), op.i32.add, op.i32.mul] }, // rewrites
  { name: "eqz_sub0", params: [I32], results: [I32], code: [...get(0), ...c32(0), op.i32.sub, op.i32.eqz] }, // rewrites
  { name: "mul1_first", params: [I32, I32], results: [I32], code: [...get(0), ...c32(1), op.i32.mul, ...get(1), op.i32.add] }, // not adjacent: kept
  { name: "eq64_and_m1", params: [I64, I64], results: [I32], code: [...get(0), ...get(1), ...c64(-1), op.i64.and, op.i64.eq] }, // rewrites
  { name: "clz_shl0", params: [I32], results: [I32], code: [...get(0), ...c32(0), op.i32.shl, op.i32.clz] }, // rewrites
  { name: "or0_return", params: [I32], results: [I32], code: [...get(0), ...c32(0), op.i32.or] }, // consumer is end: kept
  { name: "rotl64_xor0", params: [I64], results: [I64], code: [...get(0), ...get(0), ...c64(0), op.i64.xor, op.i64.rotl] }, // rewrites
  { name: "sub_rotr0", params: [I32, I32], results: [I32], code: [...get(0), ...get(1), ...c32(0), op.i32.rotr, op.i32.sub] }, // rewrites
  { name: "chain_add0", params: [I32], results: [I32], code: [...get(0), ...c32(0), op.i32.add, ...c32(0), op.i32.add, op.i32.eqz] }, // two rounds
  { name: "shl32_kept", params: [I32], results: [I32], code: [...get(0), ...c32(32), op.i32.shl, op.i32.eqz] }, // k = 32 not matched
  { name: "lt_shr0", params: [I32, I32], results: [I32], code: [...get(0), ...get(1), ...c32(0), op.i32.shr_s, op.i32.lt_u] }, // rewrites
  { name: "mul64_one", params: [I64, I64], results: [I64], code: [...get(0), ...get(1), ...c64(1), op.i64.mul, op.i64.sub] }, // rewrites
  // eqz-pair
  { name: "eqz3", params: [I32], results: [I32], code: [...get(0), op.i32.eqz, op.i32.eqz, op.i32.eqz] }, // rewrites
  { name: "select_eqz2", params: [I32, I32, I32], results: [I32], code: [...get(0), ...get(1), ...get(2), op.i32.eqz, op.i32.eqz, op.select] }, // rewrites
  { name: "brif_eqz2", params: [I32], results: [I32], code: [op.block, 0x7f, ...c32(7), ...get(0), op.i32.eqz, op.i32.eqz, op.br_if, 0x00, op.drop, ...c32(9), op.end] }, // rewrites
  { name: "eqz2_return", params: [I32], results: [I32], code: [...get(0), op.i32.eqz, op.i32.eqz] }, // consumer is end: kept
  // rse-line, drop-get, tee-form (local-variable stages)
  { name: "set_get", params: [I32], results: [I32], locals: 1, code: [...get(0), ...c32(5), op.i32.add, op.set, 1, op.get, 1, ...c32(3), op.i32.mul] }, // tee-form
  { name: "self_copy", params: [I32], results: [I32], code: [...get(0), op.set, 0, ...get(0), ...c32(1), op.i32.add] }, // rse-line, drop-get, vacuum
  { name: "self_tee", params: [I32], results: [I32], code: [...get(0), op.tee, 0, op.i32.eqz] }, // rse-line
  { name: "eqz4_chain", params: [I32], results: [I32], code: [...get(0), op.i32.eqz, op.i32.eqz, op.i32.eqz, op.i32.eqz, op.i32.eqz] }, // two rounds
];

const i32s = [0, 1, -1, 2, 31, 32, 0x7fffffff, -0x80000000, 12345, -987654];
const i64s = [0n, 1n, -1n, 63n, 64n, 0x7fffffffffffffffn, -0x8000000000000000n, 1234567890123n];
const args = (params) => {
  const out = [];
  for (let i = 0; i < 12; i++) out.push(params.map((t, j) => (t === I32 ? i32s[(i + 3 * j) % i32s.length] : i64s[(i + 5 * j) % i64s.length])));
  return out;
};

const dir = mkdtempSync(join(tmpdir(), "wasm-opt-"));
const input = module(cases);
const inPath = join(dir, "in.wasm"), outPath = join(dir, "out.wasm");
writeFileSync(inPath, input);
const run = spawnSync(exe, [inPath, ...extra, "--stats", "-o", outPath], { stdio: ["ignore", "pipe", "pipe"] });
if (run.status !== 0) throw new Error(`wasm-opt failed: ${run.stderr}`);
const stderr = run.stderr.toString();
const output = new Uint8Array(readFileSync(outPath));
if (!WebAssembly.validate(input)) throw new Error("input does not validate");
if (!WebAssembly.validate(output)) throw new Error("output does not validate");
const a = (await WebAssembly.instantiate(input)).instance.exports;
const b = (await WebAssembly.instantiate(output)).instance.exports;
let checks = 0;
for (const c of cases) for (const xs of args(c.params)) {
  const ra = a[c.name](...xs), rb = b[c.name](...xs);
  if (ra !== rb) throw new Error(`${c.name}(${xs}) = ${ra} vs ${rb}`);
  checks++;
}
console.log(`args: ${extra.join(" ")}`);
console.log(`input ${input.length} bytes -> output ${output.length} bytes; both validate; ${checks} differential checks passed`);
const ssaLines = stderr.split("\n").filter((l) => l.includes("ssa iteration 1 func"));
if (ssaLines.length > 0) {
  const rewritten = ssaLines.filter((l) => l.includes("rewritten (")).length;
  console.log(`ssa: ${rewritten} of ${ssaLines.length} functions rewritten (first iteration)`);
}
for (const l of stderr.split("\n").filter((l) => l.includes("certified:"))) console.log(l.trim());
