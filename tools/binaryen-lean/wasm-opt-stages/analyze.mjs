// Count Binaryen-style optimisation opportunities in core Wasm binaries.
//
// usage: node tools/wasm-opt/analyze.mjs FILE.wasm...
//
// A small MVP (+ sign-extension, saturating conversions, bulk memory) decoder;
// unknown opcodes stop the scan of that function and are reported. Patterns are
// textual over the flat instruction stream, so they are opportunity *upper bounds*.
import { readFileSync } from "node:fs";

function reader(b, pos = 0) {
  const r = {
    pos, b,
    u8() { return b[r.pos++]; },
    uleb() { let x = 0, s = 0, c; do { c = b[r.pos++]; x += (c & 0x7f) * 2 ** s; s += 7; } while (c & 0x80); return x; },
    sleb() { let x = 0n, s = 0n, c; do { c = b[r.pos++]; x |= BigInt(c & 0x7f) << s; s += 7n; } while (c & 0x80);
      if (c & 0x40) x -= 1n << s; return x; },
  };
  return r;
}
const names = {
  0x00: "unreachable", 0x01: "nop", 0x02: "block", 0x03: "loop", 0x04: "if", 0x05: "else", 0x0b: "end",
  0x0c: "br", 0x0d: "br_if", 0x0e: "br_table", 0x0f: "return", 0x10: "call", 0x11: "call_indirect",
  0x1a: "drop", 0x1b: "select", 0x1c: "select_t", 0x20: "local.get", 0x21: "local.set", 0x22: "local.tee",
  0x23: "global.get", 0x24: "global.set", 0x3f: "memory.size", 0x40: "memory.grow",
  0x41: "i32.const", 0x42: "i64.const", 0x43: "f32.const", 0x44: "f64.const",
};
const loads = ["i32.load", "i64.load", "f32.load", "f64.load", "i32.load8_s", "i32.load8_u", "i32.load16_s", "i32.load16_u",
  "i64.load8_s", "i64.load8_u", "i64.load16_s", "i64.load16_u", "i64.load32_s", "i64.load32_u",
  "i32.store", "i64.store", "f32.store", "f64.store", "i32.store8", "i32.store16", "i64.store8", "i64.store16", "i64.store32"];
loads.forEach((n, i) => (names[0x28 + i] = n));
const numeric = "i32.eqz i32.eq i32.ne i32.lt_s i32.lt_u i32.gt_s i32.gt_u i32.le_s i32.le_u i32.ge_s i32.ge_u i64.eqz i64.eq i64.ne i64.lt_s i64.lt_u i64.gt_s i64.gt_u i64.le_s i64.le_u i64.ge_s i64.ge_u f32.eq f32.ne f32.lt f32.gt f32.le f32.ge f64.eq f64.ne f64.lt f64.gt f64.le f64.ge i32.clz i32.ctz i32.popcnt i32.add i32.sub i32.mul i32.div_s i32.div_u i32.rem_s i32.rem_u i32.and i32.or i32.xor i32.shl i32.shr_s i32.shr_u i32.rotl i32.rotr i64.clz i64.ctz i64.popcnt i64.add i64.sub i64.mul i64.div_s i64.div_u i64.rem_s i64.rem_u i64.and i64.or i64.xor i64.shl i64.shr_s i64.shr_u i64.rotl i64.rotr f32.abs f32.neg f32.ceil f32.floor f32.trunc f32.nearest f32.sqrt f32.add f32.sub f32.mul f32.div f32.min f32.max f32.copysign f64.abs f64.neg f64.ceil f64.floor f64.trunc f64.nearest f64.sqrt f64.add f64.sub f64.mul f64.div f64.min f64.max f64.copysign i32.wrap_i64 i32.trunc_f32_s i32.trunc_f32_u i32.trunc_f64_s i32.trunc_f64_u i64.extend_i32_s i64.extend_i32_u i64.trunc_f32_s i64.trunc_f32_u i64.trunc_f64_s i64.trunc_f64_u f32.convert_i32_s f32.convert_i32_u f32.convert_i64_s f32.convert_i64_u f32.demote_f64 f64.convert_i32_s f64.convert_i32_u f64.convert_i64_s f64.convert_i64_u f64.promote_f32 i32.reinterpret_f32 i64.reinterpret_f64 f32.reinterpret_i32 f64.reinterpret_i64 i32.extend8_s i32.extend16_s i64.extend8_s i64.extend16_s i64.extend32_s".split(" ");
numeric.forEach((n, i) => (names[0x45 + i] = n));

function decodeBody(r, end) {
  const nloc = r.uleb(); const locals = [];
  for (let i = 0; i < nloc; i++) { const c = r.uleb(); const t = r.u8(); locals.push([c, t]); }
  const ins = [];
  while (r.pos < end) {
    const op = r.u8(); let name = names[op], imm = null;
    if (op === 0x02 || op === 0x03 || op === 0x04) { const bt = r.b[r.pos]; if (bt === 0x40 || (bt >= 0x7b && bt <= 0x7f)) r.pos++; else imm = r.sleb(); }
    else if (op === 0x0c || op === 0x0d || (op >= 0x20 && op <= 0x24) || op === 0x10) imm = r.uleb();
    else if (op === 0x0e) { const n = r.uleb(); const ls = []; for (let i = 0; i <= n; i++) ls.push(r.uleb()); imm = ls; }
    else if (op === 0x11) { imm = r.uleb(); r.uleb(); }
    else if (op === 0x1c) { const n = r.uleb(); for (let i = 0; i < n; i++) r.u8(); }
    else if (op >= 0x28 && op <= 0x3e) { const align = r.uleb(); imm = { align, offset: r.uleb() }; }
    else if (op === 0x3f || op === 0x40) r.u8();
    else if (op === 0x41 || op === 0x42) imm = r.sleb();
    else if (op === 0x43) r.pos += 4;
    else if (op === 0x44) r.pos += 8;
    else if (op === 0xfc) { const sub = r.uleb(); name = "fc." + sub;
      if (sub === 8) { r.uleb(); r.u8(); } else if (sub === 9) r.uleb(); else if (sub === 10) { r.u8(); r.u8(); } else if (sub === 11) r.u8(); }
    else if (!name) return { locals, ins, unknown: op.toString(16) };
    ins.push({ name, imm });
  }
  return { locals, ins };
}

export function parse(bytes) {
  const r = reader(bytes, 8); const m = { types: [], funcTypes: [], bodies: [], custom: [], imports: 0, sections: {} };
  while (r.pos < bytes.length) {
    const id = r.u8(), size = r.uleb(), end = r.pos + size;
    m.sections[id] = (m.sections[id] ?? 0) + size;
    if (id === 0) { const nl = r.uleb(); const nm = Buffer.from(bytes.slice(r.pos, r.pos + nl)).toString(); m.custom.push([nm, size]); }
    else if (id === 1) { const n = r.uleb(); for (let i = 0; i < n; i++) { r.u8(); const p = r.uleb(); const ps = []; for (let j = 0; j < p; j++) ps.push(r.u8());
      const q = r.uleb(); const qs = []; for (let j = 0; j < q; j++) qs.push(r.u8()); m.types.push(ps.join(",") + "->" + qs.join(",")); } }
    else if (id === 2) { const n = r.uleb(); for (let i = 0; i < n; i++) { let l = r.uleb(); r.pos += l; l = r.uleb(); r.pos += l; const k = r.u8();
      if (k === 0) m.funcTypes.push(["import", r.uleb()]); else if (k === 1) { r.u8(); const fl = r.uleb(); r.uleb(); if (fl & 1) r.uleb(); }
      else if (k === 2) { const fl = r.uleb(); r.uleb(); if (fl & 1) r.uleb(); } else { r.u8(); r.u8(); } m.imports++; } }
    else if (id === 3) { const n = r.uleb(); for (let i = 0; i < n; i++) m.funcTypes.push(["def", r.uleb()]); }
    else if (id === 7) { const n = r.uleb(); m.exports = []; for (let i = 0; i < n; i++) { const nl = r.uleb();
      const nm = Buffer.from(bytes.slice(r.pos, r.pos + nl)).toString(); r.pos += nl; const k = r.u8(); m.exports.push([nm, k, r.uleb()]); } }
    else if (id === 10) { const n = r.uleb(); for (let i = 0; i < n; i++) { const sz = r.uleb(); const e = r.pos + sz;
      const raw = Buffer.from(bytes.slice(r.pos, e)).toString("hex");
      m.bodies.push({ ...decodeBody(r, e), raw }); r.pos = e; } }
    r.pos = end;
  }
  return m;
}

const neutral = (name, k) => {
  const [t, o] = name.split(".");
  if (["add", "sub", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr"].includes(o)) return k === 0n;
  if (o === "mul") return k === 1n; if (o === "and") return k === -1n; return false;
};

function analyze(file) {
  const bytes = new Uint8Array(readFileSync(file)); const m = parse(bytes); const c = {};
  const inc = (k, n = 1) => (c[k] = (c[k] ?? 0) + n);
  let total = 0;
  const bodyKey = new Map();
  m.bodies.forEach((b, fi) => {
    if (b.unknown) inc("unknown-opcode:" + b.unknown);
    const s = b.ins; total += s.length;
    if (process.env.DUMP) console.log("func", fi, b.locals, "\n  " + s.map((x) => x.name + (x.imm != null ? " " + (typeof x.imm === "object" ? JSON.stringify(x.imm, (_, v) => typeof v === "bigint" ? Number(v) : v) : x.imm) : "")).join("; "));
    const defType = m.funcTypes.filter((x) => x[0] === "def")[fi]?.[1];
    const key = defType + ":" + b.raw; bodyKey.set(key, (bodyKey.get(key) ?? 0) + 1);
    const used = new Set(); s.forEach((x) => { if (x.name.startsWith("local.")) used.add(x.imm); });
    const declared = b.locals.reduce((a, [n]) => a + n, 0);
    const nparams = (m.types[defType] ?? "->").split("->")[0].split(",").filter((x) => x).length;
    let unusedLocals = 0; for (let i = nparams; i < nparams + declared; i++) if (!used.has(i)) unusedLocals++;
    inc("unused-declared-locals", unusedLocals);
    inc("local-decl-groups", b.locals.length);
    for (let i = 0; i < s.length; i++) {
      const a = s[i], n1 = s[i + 1], n2 = s[i + 2];
      if (a.name === "local.set" && n1?.name === "local.get" && n1.imm === a.imm) inc("set x; get x (tee formation / untee inverse)");
      if (a.name === "local.tee" && n1?.name === "drop") inc("tee; drop");
      if (a.name === "local.get" && n1?.name === "local.set" && n1.imm === a.imm) inc("get x; set x (no-op copy)");
      if (a.name === "local.get" && n1?.name === "local.get" && n1.imm === a.imm) inc("get x; get x (dup read)");
      if (a.name === "local.get" && n1?.name === "local.tee" && n1.imm === a.imm) inc("get x; tee x (self tee, rse-line)");
      if (a.name === "local.get" && n1?.name === "drop") inc("get x; drop");
      if ((a.name === "i32.const" || a.name === "i64.const") && n1 && n1.name.startsWith(a.name.slice(0, 3) + ".") && neutral(n1.name, a.imm)) {
        inc("neutral const-op (any consumer)"); inc("  next after neutral: " + (n2?.name ?? "<eof>"));
      }
      if (a.name === "i32.eqz" && n1?.name === "i32.eqz") inc("eqz; eqz (next: " + (n2?.name ?? "") + ")");
      if (a.name === "i32.const" && n1?.name === "i32.add" && n2 && /load|store/.test(n2.name) && a.imm >= 0n) inc("const k; add; load/store (optimize-added-constants upper bound)");
      if (a.name === "i32.const" && a.imm >= 0n && n1?.name === "i32.add" && n2?.name === "local.tee") inc("const k; add; tee (address arithmetic)");
      if (a.name === "drop" && i > 0 && /const|local.get|global.get/.test(s[i - 1].name)) inc("pure; drop (vacuum)");
      if (a.name === "i32.const" && n1?.name === "i32.const" && n2 && /^i32\.(add|sub|mul|and|or|xor|shl|shr)/.test(n2.name)) inc("const; const; binop (precompute)");
      if (a.name === "br" && n1?.name === "end") inc("br; end");
      if (a.name === "local.set") {
        // straight-line redundant set: another set to x before any get/tee of x or control flow
        for (let j = i + 1; j < s.length; j++) {
          const y = s[j];
          if ((y.name === "local.get" || y.name === "local.tee") && y.imm === a.imm) break;
          if (["block", "loop", "if", "else", "end", "br", "br_if", "br_table", "return", "call", "call_indirect", "unreachable"].includes(y.name)) break;
          if (y.name === "local.set" && y.imm === a.imm) { inc("straight-line dead set (rse-line upper bound)"); break; }
        }
      }
      inc("op:" + a.name);
    }
  });
  let dupFuncs = 0; for (const n of bodyKey.values()) if (n > 1) dupFuncs += n - 1;
  const usedTypes = new Set(m.funcTypes.map((x) => x[1]));
  return { file, size: bytes.length, funcs: m.bodies.length, instrs: total, types: m.types.length,
    unusedTypes: m.types.filter((_, i) => !usedTypes.has(i)).length, duplicateFuncs: dupFuncs, custom: m.custom, counts: c };
}

if (import.meta.url === `file://${process.argv[1]}`) for (const f of process.argv.slice(2)) {
  const a = analyze(f);
  console.log(`== ${a.file}: ${a.size} B, ${a.funcs} funcs, ${a.instrs} instrs, types ${a.types} (unused ${a.unusedTypes}), duplicate funcs ${a.duplicateFuncs}, custom ${JSON.stringify(a.custom)}`);
  const keys = Object.keys(a.counts).filter((k) => !k.startsWith("op:")).sort();
  for (const k of keys) console.log(`   ${k}: ${a.counts[k]}`);
  if (process.env.OPS) for (const k of Object.keys(a.counts).filter((k) => k.startsWith("op:")).sort((x, y) => a.counts[y] - a.counts[x]).slice(0, 15)) console.log(`   ${k}: ${a.counts[k]}`);
}
