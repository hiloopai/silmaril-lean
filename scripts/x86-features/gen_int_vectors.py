#!/usr/bin/env python3
"""Generate the native differential vectors of the integer lanes.

The oracle is the host processor (the lanes' briefs name an i7-8700, which has
BMI1, BMI2, ADX and MOVBE). Every case is one instruction written in AT&T
syntax, assembled by GNU `as` (so the byte strings are the assembler's
encodings, which the canonical decoders must accept), and executed natively by
`int_ext_harness.c` from random register, flag and memory values. Memory
operands address the harness's data area (`DATA = 0x10000800`, 64 bytes).

Each case records which lanes claim it: bit 0 `IntExt.ext` (isa/x86-int-ext),
bit 1 `BaseInt.baseIntExt` (isa/x86-ext-baseint). Cases claimed by both are the
overlap of the two lanes; `IntMerged/Vectors.lean` checks them through both.

Usage: gen_int_vectors.py [--seed N] [--per N]
Writes Silmaril/X86/Features/Ext/IntMerged/Vectors.lean.
"""

import argparse
import os
import random
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Features", "Ext", "IntMerged", "Vectors.lean")

R64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
       "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
R32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
       "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
R16 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di",
       "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"]
NAMES = {64: R64, 32: R32, 16: R16}
SUFFIX = {64: "q", 32: "l", 16: "w"}

DATA = 0x10000800
CENTER = DATA + 0x20
# Operand registers: never RSP. Base registers additionally avoid the implicit
# operands RAX, RCX (CL counts) and RDX (MULX, one-operand IMUL).
GPR = [i for i in range(16) if i != 4]
BASES = [3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

INTEXT, BASEINT, BOTH = 1, 2, 3

EDGE = [0, 1, 2, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF, 0x7FFFFFFF, 0x80000000,
        0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]


def rnd64(rng):
    k = rng.random()
    if k < 0.25:
        return rng.choice(EDGE)
    if k < 0.4:
        return rng.getrandbits(8)
    return rng.getrandbits(64)


class Case:
    def __init__(self, asm, mask, fixed=None):
        self.asm = asm
        self.mask = mask
        self.fixed = fixed or {}


def reg(rng, bits, avoid=()):
    i = rng.choice([g for g in GPR if g not in avoid])
    return i, "%" + NAMES[bits][i]


def mem(rng, size, avoid=(), disp=True):
    """A memory operand of `size` bytes inside the data area, and its base."""
    b = rng.choice([x for x in BASES if x not in avoid])
    d = rng.randrange(-32, 32 - size + 1) if disp else 0
    text = ("%d" % d if d else "") + "(%" + R64[b] + ")"
    return b, text, {b: CENTER}


def imm(rng, bits):
    v = rnd64(rng) & ((1 << bits) - 1)
    if v >= 1 << (bits - 1):
        v -= 1 << bits
    return v


def rm_or_reg(rng, bits, avoid=()):
    """An r/m operand: (text, fixed registers, registers used)."""
    if rng.random() < 0.5:
        i, t = reg(rng, bits, avoid)
        return t, {}, {i}
    b, t, fx = mem(rng, bits // 8, avoid)
    return t, fx, {b}


# ---------------------------------------------------------------- templates


def alu(rng, op, bits, mask):
    s = SUFFIX[bits]
    form = rng.randrange(5)
    if form == 0:  # op reg, r/m (AT&T: op %reg, r/m)
        dst, fx, used = rm_or_reg(rng, bits)
        _, src = reg(rng, bits, used)
        return Case(f"{op}{s} {src}, {dst}", mask, fx)
    if form == 1:  # op r/m, reg
        src, fx, used = rm_or_reg(rng, bits)
        _, dst = reg(rng, bits, used)
        return Case(f"{op}{s} {src}, {dst}", mask, fx)
    if form == 2:  # op imm32/imm16, r/m (forced long immediate)
        dst, fx, _ = rm_or_reg(rng, bits)
        v = imm(rng, min(bits, 32))
        if -128 <= v < 128:
            v = (v + 0x1000) if v >= 0 else (v - 0x1000)
        return Case(f"{op}{s} ${v}, {dst}", mask, fx)
    if form == 3:  # op imm8, r/m
        dst, fx, _ = rm_or_reg(rng, bits)
        return Case(f"{op}{s} ${imm(rng, 8)}, {dst}", mask, fx)
    v = imm(rng, min(bits, 32))
    if -128 <= v < 128:
        v = (v + 0x1000) if v >= 0 else (v - 0x1000)
    return Case(f"{op}{s} ${v}, %{NAMES[bits][0]}", mask)


def shd(rng, op, bits, mask):
    s = SUFFIX[bits]
    dst, fx, used = rm_or_reg(rng, bits, avoid=(1,))
    _, src = reg(rng, bits, used | {1})
    if rng.random() < 0.5:
        return Case(f"{op}{s} %cl, {src}, {dst}", mask, fx)
    return Case(f"{op}{s} ${rng.randrange(256)}, {src}, {dst}", mask, fx)


def bt(rng, op, bits, mask):
    s = SUFFIX[bits]
    if rng.random() < 0.5:
        dst, fx, _ = rm_or_reg(rng, bits)
        return Case(f"{op}{s} ${rng.randrange(256)}, {dst}", mask, fx)
    if rng.random() < 0.5:
        d, dst = reg(rng, bits)
        _, src = reg(rng, bits, {d})
        return Case(f"{op}{s} {src}, {dst}", mask)
    b, dst, fx = mem(rng, bits // 8, disp=False)
    o, src = reg(rng, bits, {b})
    fx = dict(fx)
    fx[o] = rng.randrange(-256, 256) & 0xFFFFFFFFFFFFFFFF
    return Case(f"{op}{s} {src}, {dst}", mask, fx)


def int_ext_only(rng):
    """The int-ext forms outside the overlap."""
    bits = rng.choice([32, 64])
    s = SUFFIX[bits]
    k = rng.randrange(14)
    if k == 0:
        src, fx, used = rm_or_reg(rng, bits)
        _, dst = reg(rng, bits, used)
        v = imm(rng, 32) if rng.random() < 0.5 else imm(rng, 8)
        return Case(f"imul{s} ${v}, {src}, {dst}", INTEXT, fx)
    if k == 1:
        src, fx, _ = rm_or_reg(rng, bits, avoid=(0, 2))
        return Case(f"imul{s} {src}", INTEXT, fx)
    if k == 2:
        # Not EAX/RAX: the assembler picks the accumulator form `A9 id`, which
        # the int-ext lane does not decode (a coverage gap, not a mismatch).
        dst, fx, _ = rm_or_reg(rng, bits, avoid=(0,))
        v = imm(rng, 32)
        if -128 <= v < 128:
            v += 0x1000
        return Case(f"test{s} ${v}, {dst}", INTEXT, fx)
    if k == 3:
        src, fx, used = rm_or_reg(rng, bits)
        _, dst = reg(rng, bits, used)
        return Case(f"{rng.choice(['bsf', 'bsr'])}{s} {src}, {dst}", INTEXT, fx)
    if k == 4:
        d, dst = reg(rng, bits)
        _, src = reg(rng, bits, {d})
        return Case(f"{rng.choice(['xadd', 'cmpxchg'])}{s} {src}, {dst}", INTEXT)
    if k == 5:
        src, fx, used = rm_or_reg(rng, bits)
        _, dst = reg(rng, bits, used)
        return Case(f"{rng.choice(['adcx', 'adox'])} {src}, {dst}", INTEXT, fx)
    if k == 6:
        b, m, fx = mem(rng, bits // 8)
        _, r = reg(rng, bits, {b})
        if rng.random() < 0.5:
            return Case(f"movbe{s} {m}, {r}", INTEXT, fx)
        return Case(f"movbe{s} {r}, {m}", INTEXT, fx)
    if k in (7, 8, 9):
        op = rng.choice(["andn", "bextr", "bzhi", "pdep", "pext", "sarx", "shlx", "shrx",
                         "mulx"])
        src, fx, used = rm_or_reg(rng, bits)
        v, vt = reg(rng, bits, used)
        _, dst = reg(rng, bits, used | {v})
        # AT&T operand order: reverse of Intel `op dst, a, b`.
        if op in ("andn", "pdep", "pext", "mulx"):
            # Intel: dst, vvvv, r/m
            return Case(f"{op} {src}, {vt}, {dst}", INTEXT, fx)
        # bextr/bzhi/sarx/shlx/shrx Intel: dst, r/m, vvvv
        return Case(f"{op} {vt}, {src}, {dst}", INTEXT, fx)
    if k in (10, 11):
        op = rng.choice(["blsr", "blsmsk", "blsi"])
        src, fx, used = rm_or_reg(rng, bits)
        _, dst = reg(rng, bits, used)
        return Case(f"{op} {src}, {dst}", INTEXT, fx)
    src, fx, used = rm_or_reg(rng, bits)
    _, dst = reg(rng, bits, used)
    return Case(f"rorx ${rng.randrange(256)}, {src}, {dst}", INTEXT, fx)


def overlap(rng):
    """ADC/SBB, SHLD/SHRD and BTx at 32/64 bits, and PUSH imm: both lanes."""
    bits = rng.choice([32, 64])
    k = rng.randrange(4)
    if k == 0:
        return alu(rng, rng.choice(["adc", "sbb"]), bits, BOTH)
    if k == 1:
        return shd(rng, rng.choice(["shld", "shrd"]), bits, BOTH)
    if k == 2:
        return bt(rng, rng.choice(["bt", "bts", "btr", "btc"]), bits, BOTH)
    v = imm(rng, 32) if rng.random() < 0.5 else imm(rng, 8)
    if rng.random() < 0.5 and -128 <= v < 128:
        v = v + 0x1000 if v >= 0 else v - 0x1000
    return Case(f"pushq ${v}", BOTH)


def base_only(rng):
    """The 16-bit forms of the baseline lane."""
    k = rng.randrange(3)
    if k == 0:
        return alu(rng, rng.choice(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]), 16,
                   BASEINT)
    if k == 1:
        return shd(rng, rng.choice(["shld", "shrd"]), 16, BASEINT)
    return bt(rng, rng.choice(["bt", "bts", "btr", "btc"]), 16, BASEINT)


# ---------------------------------------------------------------- pipeline


def assemble(cases, tmp):
    src = os.path.join(tmp, "c.s")
    obj = os.path.join(tmp, "c.o")
    with open(src, "w") as f:
        f.write(".text\n")
        for c in cases:
            f.write(c.asm + "\n")
    subprocess.run(["as", "--64", "-o", obj, src], check=True)
    out = subprocess.run(["objdump", "-d", "--insn-width=16", obj], check=True,
                         capture_output=True, text=True).stdout
    codes = []
    for line in out.splitlines():
        m = re.match(r"\s*[0-9a-f]+:\t((?:[0-9a-f]{2} )+)\s*\t", line)
        if m:
            codes.append(m.group(1).replace(" ", ""))
    if len(codes) != len(cases):
        sys.exit(f"assembled {len(codes)} instructions for {len(cases)} cases")
    return codes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=3585)
    ap.add_argument("--per", type=int, default=600)
    ap.add_argument("--u0", type=int, default=11, help="expected int-ext unmodeled count")
    ap.add_argument("--u1", type=int, default=97, help="expected baseint unmodeled count")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = [g(rng) for g in (int_ext_only, overlap, base_only) for _ in range(args.per)]
    with tempfile.TemporaryDirectory() as tmp:
        codes = assemble(cases, tmp)
        harness = os.path.join(tmp, "harness")
        subprocess.run(["gcc", "-O1", "-o", harness, os.path.join(HERE, "int_ext_harness.c")],
                       check=True)
        inputs = []
        for c in cases:
            regs = [rnd64(rng) for _ in range(16)]
            regs[4] = 0
            for r, v in c.fixed.items():
                regs[r] = v
            fl = 0x202 | sum(rng.getrandbits(1) << b for b in (0, 2, 4, 6, 7, 11))
            data = [rnd64(rng) for _ in range(8)]
            inputs.append((regs, fl, data))
        text = "".join(
            code + " " + " ".join("%x" % v for v in regs + [fl] + data) + "\n"
            for code, (regs, fl, data) in zip(codes, inputs))
        out = subprocess.run([harness], input=text, check=True, capture_output=True,
                             text=True).stdout.splitlines()
    if len(out) != len(cases):
        sys.exit("harness output is short")
    lines = []
    for c, code, (regs, fl, data), o in zip(cases, codes, inputs, out):
        f = [int(x, 16) for x in o.split()]
        outs, pushed, rsp0 = f[:25], f[25], f[26]
        regs = list(regs)
        regs[4] = rsp0
        fields = [c.mask, len(code) // 2, int(code, 16)] + regs + [fl] + data + outs + [pushed]
        lines.append(" ".join("%x" % v for v in fields) + "  -- " + c.asm)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    body = "\n".join(l.split("  -- ")[0] for l in lines)
    with open(OUT, "w") as f:
        f.write(HEADER.format(seed=args.seed, n=len(lines)))
        f.write("def vectors : String := \"\n" + body + "\n\"\n\n")
        f.write(FOOTER.replace("{n}", str(len(lines))).replace("{u0}", str(args.u0)).replace("{u1}", str(args.u1)))
    with open(os.path.join(ROOT, "scripts", "x86-features", "int_vectors.asm.txt"), "w") as f:
        f.write("\n".join(l.split("  -- ")[1] for l in lines) + "\n")
    print(f"wrote {len(lines)} vectors to {OUT}")


HEADER = """-- Generated by scripts/x86-features/gen_int_vectors.py --seed {seed}; do not edit.
module

public import Silmaril.X86.Features.Ext.IntMerged.Check
public meta import Silmaril.X86.Features.Ext.IntMerged.Check
public meta import Silmaril.X86.Features.Ext.IntExt.Extension
public meta import Silmaril.X86.Features.Ext.BaseInt.Extension
public meta import Silmaril.X86.Features.Checks

/-!
# Native differential vectors of the integer lanes

{n} single-instruction cases, assembled by GNU `as` and executed on the host
(an i7-8700) by `scripts/x86-features/int_ext_harness.c`. Fields per line
(hexadecimal): lanes (bit 0 int-ext, bit 1 baseint), length, code, the sixteen
input registers, RFLAGS, the eight data words, then the sixteen output
registers, RFLAGS, the eight data words and the word at the final RSP. The
assembler text of line `k` is line `k` of `scripts/x86-features/int_vectors.asm.txt`.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntMerged

"""

FOOTER = """-- Lanes: bit 0 int-ext, bit 1 baseint; 3 is the overlap.
#guard (hexFields vectors).length == {n}

-- Every int-ext case decodes, and agrees with the hardware or is unmodeled.
#guard ((hexFields vectors).filter fun r => (r.headD 0).testBit 0).all fun r =>
  (check IntExt.ext r).ok

-- Every baseint case decodes, and agrees with the hardware or is unmodeled.
#guard ((hexFields vectors).filter fun r => (r.headD 0).testBit 1).all fun r =>
  (check BaseInt.baseIntExt r).ok

-- The lanes agree on the overlap: every case claimed by both gets the same
-- verdict from both.
#guard ((hexFields vectors).filter fun r => r.headD 0 == 3).all fun r =>
  check IntExt.ext r == check BaseInt.baseIntExt r

-- The unmodeled cases: BSF/BSR with a zero source, SHLD/SHRD with a zero
-- count and a memory destination, and 16-bit SHLD/SHRD with a count above 16.
#guard ((hexFields vectors).filter fun r =>
  (r.headD 0).testBit 0 && check IntExt.ext r == .unmodeled).length == {u0}
#guard ((hexFields vectors).filter fun r =>
  (r.headD 0).testBit 1 && check BaseInt.baseIntExt r == .unmodeled).length == {u1}

end Silmaril.X86.Features.IntMerged
"""

if __name__ == "__main__":
    main()
