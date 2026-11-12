// Differential suite of wasm-asyncify.
//
// For every example and argument list: run the source module under Node with a synchronous host
// (each import call answers at once), run the asyncified module under Node with the asyncify host
// protocol (on return with asyncify_state = 1 read the request at word 0, write the answers at
// word 0, set asyncify_state = 2, call the export again), and run both in the Lean model
// (`wasm-asyncify run-src` / `run-tgt`). The target is produced twice, with the re-entry checks
// elided (the default) and guarded (`--no-elide`). All six outcomes (results and the log of import
// calls) must agree. The host is `testHost` of Silmaril/Wasm/FX/Asyncify/Tool/Run/Defs.lean.
//
//   node tools/wasm-asyncify/differential.mjs [path/to/wasm-asyncify]
//
// The examples are regenerated into a temporary directory by `wasm-asyncify example`.

import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const tool = process.argv[2] ?? ".lake/build/bin/wasm-asyncify";
const dir = mkdtempSync(join(tmpdir(), "wasm-asyncify-"));

const cases = {
  "sleep-add": [[0], [5], [4294967295]],
  "twice": [[5, 3], [0, 0], [123456, 789]],
  "chain": [[5], [0], [4000000000]],
  "multi": [[17, 5], [0, 1], [99, 98]],
  "no-susp": [[7], [65536]],
  "fused": [[3], [0], [4294967295]],
  "trap-after": [[5], [0]],
  "deep": [[1], [100], [4294967295]],
  "many": [[1, 2], [0, 0], [77, 4000000000]],
  "computed-arg": [[0], [41], [4294967295]],
  "live": [[0], [9], [3000000000]],
  "live-chain": [[1, 2], [0, 0], [123, 4000000000]],
};

// The answer j to the c-th call of import f with arguments as.
function answers(log, f, as) {
  const s = as.reduce((a, b) => a + b, 0);
  const ans = [0, 1, 2, 3].map((j) => Number((31n * BigInt(s) + 7n * BigInt(f) + 1000n * BigInt(log.length) + BigInt(j)) % 4294967296n));
  log.push({ import: f, args: as, answers: ans });
  return ans;
}

function funcImports(mod) {
  return WebAssembly.Module.imports(mod).filter((i) => i.kind === "function");
}

function u32(x) { return x >>> 0; }

function runSource(bytes, name, args, nres) {
  const mod = new WebAssembly.Module(bytes);
  const log = [];
  const env = {};
  funcImports(mod).forEach((imp, f) => {
    env[imp.module] ??= {};
    env[imp.module][imp.name] = (...as) => {
      const ans = answers(log, f, as.map(u32));
      const m = nres[f];
      return m === 0 ? undefined : m === 1 ? ans[0] : ans.slice(0, m);
    };
  });
  try {
    const inst = new WebAssembly.Instance(mod, env);
    const r = inst.exports[name](...args);
    const results = r === undefined ? [] : Array.isArray(r) ? r.map(u32) : [u32(r)];
    return { outcome: "done", results, log };
  } catch (e) {
    if (e instanceof WebAssembly.RuntimeError) return { outcome: "trap", log };
    throw e;
  }
}

function runTarget(bytes, name, args, arity, nres) {
  const mod = new WebAssembly.Module(bytes);
  const log = [];
  const env = {};
  for (const imp of funcImports(mod)) {
    env[imp.module] ??= {};
    env[imp.module][imp.name] = () => { throw new Error("asyncified code called an import"); };
  }
  try {
    const inst = new WebAssembly.Instance(mod, env);
    const state = inst.exports.asyncify_state;
    const mem = () => new Uint32Array(inst.exports.asyncify_memory.buffer);
    for (let rounds = 0; ; rounds++) {
      if (rounds > 100000) throw new Error("too many rounds");
      const r = inst.exports[name](...args);
      if (state.value !== 1) {
        const results = r === undefined ? [] : Array.isArray(r) ? r.map(u32) : [u32(r)];
        return { outcome: "done", results, log };
      }
      const f = mem()[0];
      const as = [...mem().slice(1, 1 + arity[f])];
      const ans = answers(log, f, as);
      for (let j = 0; j < nres[f]; j++) mem()[j] = ans[j];
      state.value = 2;
    }
  } catch (e) {
    if (e instanceof WebAssembly.RuntimeError) return { outcome: "trap", log };
    throw e;
  }
}

function model(cmd, file, name, args) {
  const out = execFileSync(tool, [cmd, file, name, args.join(",")], { encoding: "utf8" });
  return JSON.parse(out);
}

// Arities and result counts of the imports, from the example sources (the JS API hides them).
const sigs = {
  "sleep-add": { arity: [1], nres: [1] },
  "twice": { arity: [1, 1], nres: [1, 1] },
  "chain": { arity: [1], nres: [1] },
  "multi": { arity: [2, 1], nres: [2, 0] },
  "no-susp": { arity: [], nres: [] },
  "fused": { arity: [1], nres: [1] },
  "trap-after": { arity: [1], nres: [1] },
  "deep": { arity: [0, 0], nres: [0, 1] },
  "many": { arity: [2], nres: [1] },
  "computed-arg": { arity: [1], nres: [1] },
  "live": { arity: [1], nres: [1] },
  "live-chain": { arity: [1, 2], nres: [2, 0] },
};

let failures = 0, runs = 0;
for (const [ex, argss] of Object.entries(cases)) {
  const src = join(dir, `${ex}.wasm`), tgt = join(dir, `${ex}.async.wasm`);
  const tgtG = join(dir, `${ex}.guarded.wasm`);
  execFileSync(tool, ["example", ex, "-o", src]);
  execFileSync(tool, ["asyncify", src, "-o", tgt]);
  // The guarded pass covers the statement form only; spilled examples have no guarded variant.
  let guarded = true;
  try {
    execFileSync(tool, ["asyncify", src, "-o", tgtG, "--no-elide"], { stdio: "pipe" });
  } catch {
    guarded = false;
  }
  // The selective pass covers the statement form only, like the guarded one.
  const sel = join(dir, `${ex}.sel.wasm`);
  let selective = true;
  try {
    execFileSync(tool, ["asyncify", src, "-o", sel, "--selective"], { stdio: "pipe" });
  } catch {
    selective = false;
  }
  const { arity, nres } = sigs[ex];
  for (const args of argss) {
    runs++;
    const outs = {
      "node-src": runSource(readFileSync(src), "main", args, nres),
      "node-tgt": runTarget(readFileSync(tgt), "main", args, arity, nres),
      ...(guarded ? { "node-tgt-guarded": runTarget(readFileSync(tgtG), "main", args, arity, nres) } : {}),
      "model-src": model("run-src", src, "main", args),
      "model-tgt": model("run-tgt", tgt, "main", args),
      ...(guarded ? { "model-tgt-guarded": model("run-tgt", tgtG, "main", args) } : {}),
      ...(selective ? { "node-sel": runTarget(readFileSync(sel), "main", args, arity, nres) } : {}),
      ...(selective ? { "model-sel": model("run-tgt", sel, "main", args) } : {}),
    };
    const ref = JSON.stringify(outs["node-src"]);
    const bad = Object.entries(outs).filter(([, o]) => JSON.stringify(o) !== ref);
    if (bad.length > 0) {
      failures++;
      console.log(`FAIL ${ex} ${JSON.stringify(args)}`);
      for (const [k, o] of Object.entries(outs)) console.log(`  ${k}: ${JSON.stringify(o)}`);
    } else {
      console.log(`ok   ${ex} ${JSON.stringify(args)} -> ${JSON.stringify(outs["node-src"].results)} (${outs["node-src"].log.length} suspensions${guarded ? "" : ", spilled"})`);
    }
  }
}
// The rejected example must be refused.
const rej = join(dir, "rejected.wasm");
execFileSync(tool, ["example", "rejected", "-o", rej]);
try {
  execFileSync(tool, ["asyncify", rej, "-o", join(dir, "rejected.async.wasm")], { stdio: "pipe" });
  failures++;
  console.log("FAIL rejected: the tool accepted a module outside the fragment");
} catch {
  console.log("ok   rejected (refused)");
}
console.log(`${runs - failures}/${runs} differential runs agree`);
process.exit(failures === 0 ? 0 : 1);
