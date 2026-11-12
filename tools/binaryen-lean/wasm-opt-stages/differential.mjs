// Differential check of an optimised module against its input with Node's engine.
//
// usage: node tools/wasm-opt/differential.mjs IN.wasm OUT.wasm
//
// Both must validate. Every exported function is called on a fixed set of
// arguments (typed from the binary), after filling exported memory with the same
// pattern on both sides; results, traps and a memory hash must agree. Modules
// that cannot be instantiated with stub imports are reported as skipped.
import { readFileSync } from "node:fs";
import { parse } from "./analyze.mjs";

const [inPath, outPath] = process.argv.slice(2);
const load = (p) => new Uint8Array(readFileSync(p));
const a = load(inPath), b = load(outPath);
if (!WebAssembly.validate(a)) { console.log("SKIP input does not validate"); process.exit(0); }
if (!WebAssembly.validate(b)) { console.log("FAIL output does not validate"); process.exit(1); }
const m = parse(a);
const stub = new Proxy({}, { get: () => new Proxy({}, { get: () => () => 0 }) });
const I32 = [0, 1, 2, 3, 7, 16, 100, 255, 1000, 12345], I64 = [0n, 1n, 5n, 12n, 100n, 1000n];
async function run(bytes) {
  let inst;
  try { inst = (await WebAssembly.instantiate(bytes, stub)).instance; } catch (e) { return null; }
  const out = [];
  const mem = inst.exports.memory;
  const fill = () => { if (mem) { const u = new Uint8Array(mem.buffer); for (let i = 0; i < Math.min(u.length, 1 << 17); i++) u[i] = (i * 131 + 7) & 0x3f; } };
  const nimp = m.funcTypes.filter((x) => x[0] === "import").length;
  for (const [name, kind, idx] of m.exports ?? []) {
    if (kind !== 0) continue;
    const ty = m.types[m.funcTypes[idx][1]].split("->")[0].split(",").filter((x) => x).map(Number);
    if (ty.some((t) => t !== 0x7f && t !== 0x7e)) { out.push(`${name}: skipped (float params)`); continue; }
    for (let k = 0; k < 6; k++) {
      fill();
      const args = ty.map((t, j) => (t === 0x7f ? I32[(k + 2 * j) % I32.length] : I64[(k + 3 * j) % I64.length]));
      let r; try { r = inst.exports[name](...args); } catch (e) {
        // Core Wasm has a single trap outcome; engine messages ("divide by zero",
        // "unreachable") are not observable, so only the trap itself is compared.
        r = e instanceof WebAssembly.RuntimeError ? "trap" : "error:" + e.message; }
      let h = 0; if (mem) { const u = new Uint8Array(mem.buffer); for (let i = 0; i < Math.min(u.length, 1 << 17); i++) h = (h * 31 + u[i]) >>> 0; }
      out.push(`${name}(${args})=${r} mem=${h}`);
    }
  }
  return out;
}
const ra = await run(a), rb = await run(b);
if (ra === null) { console.log("SKIP cannot instantiate with stub imports"); process.exit(0); }
if (rb === null) { console.log("FAIL output cannot be instantiated"); process.exit(1); }
const same = ra.length === rb.length && ra.every((x, i) => x === rb[i]);
console.log(same ? `OK ${ra.length} calls agree` : "FAIL\n" + ra.filter((x, i) => x !== rb[i]).slice(0, 5).join("\n") + "\nvs\n" + rb.filter((x, i) => x !== ra[i]).slice(0, 5).join("\n"));
process.exit(same ? 0 : 1);
