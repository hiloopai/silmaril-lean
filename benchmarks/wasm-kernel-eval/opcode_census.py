#!/usr/bin/env python3
"""Count instruction mnemonics in the code sections of Wasm binaries (core modules, and core
modules nested in components). Covers the MVP, sign-extension, saturating truncation, bulk
memory and reference opcodes; a function using any other opcode is counted under `<other>`
and skipped from that point. Usage: python3 -I opcode_census.py FILE.wasm... [--json]"""
import json, sys
from collections import Counter

def leb(b, i, signed=False):
    r = s = 0
    while True:
        x = b[i]; i += 1
        r |= (x & 0x7f) << s; s += 7
        if x < 0x80:
            if signed and x & 0x40: r -= 1 << s
            return r, i

NAMES = {0x00: "unreachable", 0x01: "nop", 0x02: "block", 0x03: "loop", 0x04: "if", 0x05: "else",
         0x0b: "end", 0x0c: "br", 0x0d: "br_if", 0x0e: "br_table", 0x0f: "return", 0x10: "call",
         0x11: "call_indirect", 0x1a: "drop", 0x1b: "select", 0x1c: "select_t",
         0x20: "local.get", 0x21: "local.set", 0x22: "local.tee", 0x23: "global.get",
         0x24: "global.set", 0x25: "table.get", 0x26: "table.set", 0x3f: "memory.size",
         0x40: "memory.grow", 0x41: "i32.const", 0x42: "i64.const", 0x43: "f32.const",
         0x44: "f64.const", 0xd0: "ref.null", 0xd1: "ref.is_null", 0xd2: "ref.func"}
MEM = ["i32.load", "i64.load", "f32.load", "f64.load", "i32.load8_s", "i32.load8_u",
       "i32.load16_s", "i32.load16_u", "i64.load8_s", "i64.load8_u", "i64.load16_s",
       "i64.load16_u", "i64.load32_s", "i64.load32_u", "i32.store", "i64.store", "f32.store",
       "f64.store", "i32.store8", "i32.store16", "i64.store8", "i64.store16", "i64.store32"]
for k, n in enumerate(MEM): NAMES[0x28 + k] = n
NUM = ("i32.eqz i32.eq i32.ne i32.lt_s i32.lt_u i32.gt_s i32.gt_u i32.le_s i32.le_u i32.ge_s "
       "i32.ge_u i64.eqz i64.eq i64.ne i64.lt_s i64.lt_u i64.gt_s i64.gt_u i64.le_s i64.le_u "
       "i64.ge_s i64.ge_u f32.eq f32.ne f32.lt f32.gt f32.le f32.ge f64.eq f64.ne f64.lt f64.gt "
       "f64.le f64.ge i32.clz i32.ctz i32.popcnt i32.add i32.sub i32.mul i32.div_s i32.div_u "
       "i32.rem_s i32.rem_u i32.and i32.or i32.xor i32.shl i32.shr_s i32.shr_u i32.rotl i32.rotr "
       "i64.clz i64.ctz i64.popcnt i64.add i64.sub i64.mul i64.div_s i64.div_u i64.rem_s "
       "i64.rem_u i64.and i64.or i64.xor i64.shl i64.shr_s i64.shr_u i64.rotl i64.rotr f32.abs "
       "f32.neg f32.ceil f32.floor f32.trunc f32.nearest f32.sqrt f32.add f32.sub f32.mul f32.div "
       "f32.min f32.max f32.copysign f64.abs f64.neg f64.ceil f64.floor f64.trunc f64.nearest "
       "f64.sqrt f64.add f64.sub f64.mul f64.div f64.min f64.max f64.copysign i32.wrap_i64 "
       "i32.trunc_f32_s i32.trunc_f32_u i32.trunc_f64_s i32.trunc_f64_u i64.extend_i32_s "
       "i64.extend_i32_u i64.trunc_f32_s i64.trunc_f32_u i64.trunc_f64_s i64.trunc_f64_u "
       "f32.convert_i32_s f32.convert_i32_u f32.convert_i64_s f32.convert_i64_u f32.demote_f64 "
       "f64.convert_i32_s f64.convert_i32_u f64.convert_i64_s f64.convert_i64_u f64.promote_f32 "
       "i32.reinterpret_f32 i64.reinterpret_f64 f32.reinterpret_i32 f64.reinterpret_i64 "
       "i32.extend8_s i32.extend16_s i64.extend8_s i64.extend16_s i64.extend32_s").split()
for k, n in enumerate(NUM): NAMES[0x45 + k] = n
FC = {0: "i32.trunc_sat_f32_s", 1: "i32.trunc_sat_f32_u", 2: "i32.trunc_sat_f64_s",
      3: "i32.trunc_sat_f64_u", 4: "i64.trunc_sat_f32_s", 5: "i64.trunc_sat_f32_u",
      6: "i64.trunc_sat_f64_s", 7: "i64.trunc_sat_f64_u", 8: "memory.init", 9: "data.drop",
      10: "memory.copy", 11: "memory.fill", 12: "table.init", 13: "elem.drop", 14: "table.copy",
      15: "table.grow", 16: "table.size", 17: "table.fill"}

def blocktype(b, i):
    if b[i] == 0x40 or b[i] in (0x7f, 0x7e, 0x7d, 0x7c, 0x7b, 0x70, 0x6f): return i + 1
    _, i = leb(b, i, True); return i

def body(b, i, end, c):
    while i < end:
        op = b[i]; i += 1
        if op == 0xfc:
            sub, i = leb(b, i)
            if sub not in FC: c["<other>"] += 1; return
            c[FC[sub]] += 1
            if sub in (8, 12, 14): _, i = leb(b, i); _, i = leb(b, i)
            elif sub in (9, 11, 13, 15, 16, 17): _, i = leb(b, i)
            elif sub == 10: i += 2
            continue
        if op not in NAMES: c["<other>"] += 1; return
        n = NAMES[op]; c[n] += 1
        if op in (0x02, 0x03, 0x04): i = blocktype(b, i)
        elif op in (0x0c, 0x0d, 0x10, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0xd2): _, i = leb(b, i)
        elif op == 0x0e:
            k, i = leb(b, i)
            for _ in range(k + 1): _, i = leb(b, i)
        elif op == 0x11: _, i = leb(b, i); _, i = leb(b, i)
        elif op == 0x1c:
            k, i = leb(b, i); i += k
        elif 0x28 <= op <= 0x3e: _, i = leb(b, i); _, i = leb(b, i)
        elif op in (0x3f, 0x40): i += 1
        elif op == 0x41: _, i = leb(b, i, True)
        elif op == 0x42: _, i = leb(b, i, True)
        elif op == 0x43: i += 4
        elif op == 0x44: i += 8
        elif op == 0xd0: i += 1

def module(b, i, end, c):
    i += 8
    while i < end:
        sid = b[i]; size, j = leb(b, i + 1); nxt = j + size
        if sid == 10:
            n, j = leb(b, j)
            for _ in range(n):
                fsz, j = leb(b, j); fend = j + fsz
                k, j = leb(b, j)
                for _ in range(k): _, j = leb(b, j); j += 1
                body(b, j, fend, c); j = fend
        i = nxt

def file(b, c):
    if b[4:8] == b"\x01\x00\x00\x00": module(b, 0, len(b), c); return
    i = 8  # component: core modules are section 1
    while i < len(b):
        sid = b[i]; size, j = leb(b, i + 1)
        if sid == 1: module(b, j, j + size, c)
        i = j + size

if __name__ == "__main__":
    c = Counter()
    for f in [a for a in sys.argv[1:] if not a.startswith("--")]:
        file(open(f, "rb").read(), c)
    del c["end"]
    tot = sum(c.values())
    if "--json" in sys.argv: print(json.dumps({"total": tot, "counts": c.most_common()})); sys.exit()
    acc = 0
    for n, k in c.most_common(40):
        acc += k; print(f"{n:22s} {k:7d} {100*k/tot:5.1f}% cum {100*acc/tot:5.1f}%")
    print("total", tot)
