#!/usr/bin/env python3
"""Generate the hardware vectors of Silmaril/X86/Str9FsXN/Vectors.lean.

Oracle: the host processor (an Intel Core i7-8700 when the committed vectors
were generated). Every case is one instruction of `Silmaril.X86.Narrow9`
(16-bit shifts and rotates, 8-bit rotates, 8- and 16-bit ADC/SBB), assembled
as raw bytes (`.byte`, so the bytes are exactly the SDM encoding) into a
function

    pushfq image; popfq          ; CF PF AF ZF SF OF from the case
    load rax..r15 (not rsp)      ; rdi last
    <instruction>
    pushfq; store rax..r15 and RFLAGS

that runs on a 32-byte buffer. A memory operand is `[rbx + disp8]` or
`[rbx + disp32]`; the model puts the buffer at 0x10000, and the harness
relocates rbx to the real buffer for those cases (the generator never writes
rbx in them).

Each vector line is, in hex:

    enc r0..r15 rflags mem | r0'..r15' rflags' mem'

with registers in hardware order (rax rcx rdx rbx rsp rbp rsi rdi r8..r15; rsp
is 0 and not compared), `enc` the instruction bytes (big-endian), `mem` the
buffer as a little-endian number. `Str9FsXN.Checks.checkLine` runs
`Str9FsXN.step` from the input state (code at 0x1000, executable; buffer
read-write) and compares RIP, the fifteen registers, every flag the model
defines, and the buffer.

Usage: gen_narrow_vectors.py [--seed N] [--n PER_FORM]
"""

import argparse
import os
import random
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Str9FsXN", "Vectors.lean")

MEM_BASE = 0x10000
MEM_LEN = 32
FLAG_MASK = 0x8D5  # CF PF AF ZF SF OF

HARNESS_C = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
struct st { uint64_t r[16]; uint64_t fl; };
typedef void (*fn)(struct st *s);
extern fn table[];
static unsigned char mem[64] __attribute__((aligned(16)));
int main(void) {
  static char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    int idx, reloc; struct st s; char ms[256];
    unsigned long long v[17];
    if (sscanf(line, "%d %d %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %255s",
               &idx, &reloc, &v[0], &v[1], &v[2], &v[3], &v[4], &v[5], &v[6], &v[7], &v[8], &v[9],
               &v[10], &v[11], &v[12], &v[13], &v[14], &v[15], &v[16], ms) != 20) break;
    for (int i = 0; i < 16; i++) s.r[i] = v[i];
    s.fl = v[16];
    memset(mem, 0, sizeof mem);
    for (int i = 0; i < 32; i++) { unsigned b; sscanf(ms + 2 * i, "%2x", &b); mem[i] = b; }
    uint64_t delta = (uint64_t)(uintptr_t)mem - 0x10000ull;
    if (reloc) s.r[3] += delta;
    table[idx](&s);
    if (reloc) s.r[3] -= delta;
    for (int i = 0; i < 16; i++) printf("%llx ", (unsigned long long)s.r[i]);
    printf("%llx ", (unsigned long long)s.fl);
    for (int i = 0; i < 32; i++) printf("%02x", mem[i]);
    printf("\n");
  }
  return 0;
}
"""

REGS = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
        "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]


def build(forms, tmp):
    asm = [".text"]
    for i, bs in enumerate(forms):
        asm += [f".globl f_{i}", f"f_{i}:",
                "  push %rbx", "  push %rbp", "  push %r12", "  push %r13", "  push %r14", "  push %r15",
                "  push %rdi", "  pushq 128(%rdi)", "  popfq"]
        for k, r in enumerate(REGS):
            if r not in ("rsp", "rdi"):
                asm.append(f"  mov {8 * k}(%rdi), %{r}")
        asm.append("  mov 56(%rdi), %rdi")
        asm.append("  .byte " + ",".join("0x%02x" % b for b in bs))
        asm += ["  pushfq", "  xchg %rdi, 8(%rsp)"]
        for k, r in enumerate(REGS):
            if r not in ("rsp", "rdi"):
                asm.append(f"  mov %{r}, {8 * k}(%rdi)")
        asm += ["  popq 128(%rdi)", "  popq 56(%rdi)", "  movq $0, 32(%rdi)",
                "  pop %r15", "  pop %r14", "  pop %r13", "  pop %r12", "  pop %rbp", "  pop %rbx",
                "  ret"]
    asm += [".data", ".globl table", "table:"] + [f"  .quad f_{i}" for i in range(len(forms))]
    asm += ['.section .note.GNU-stack,"",@progbits']
    with open(os.path.join(tmp, "forms.s"), "w") as f:
        f.write("\n".join(asm) + "\n")
    with open(os.path.join(tmp, "h.c"), "w") as f:
        f.write(HARNESS_C)
    exe = os.path.join(tmp, "h")
    subprocess.run(["gcc", "-O1", "-o", exe, os.path.join(tmp, "h.c"),
                    os.path.join(tmp, "forms.s")], check=True)
    return exe


# ------------------------------------------------------------------ encodings

def rex(w=0, r=0, x=0, b=0):
    return 0x40 | (w << 3) | (r << 2) | (x << 1) | b


def modrm_reg(reg, rm):
    """ModRM with a register r/m; returns (rex bits r, b, modrm)."""
    return (reg >> 3) & 1, (rm >> 3) & 1, [0xC0 | ((reg & 7) << 3) | (rm & 7)]


def modrm_mem(reg, disp, d32):
    """[rbx + disp8] or [rbx + disp32]."""
    if d32:
        return (reg >> 3) & 1, 0, [0x80 | ((reg & 7) << 3) | 3] + list(disp.to_bytes(4, "little"))
    return (reg >> 3) & 1, 0, [0x40 | ((reg & 7) << 3) | 3, disp]


def encode(pfx66, opc, reg, rmop, force_rex=False):
    """rmop: ('r', n) or ('m', disp, d32). Returns (bytes, uses_mem)."""
    if rmop[0] == "r":
        r, b, mb = modrm_reg(reg, rmop[1])
        mem = False
    else:
        r, b, mb = modrm_mem(reg, rmop[1], rmop[2])
        mem = True
    out = [0x66] if pfx66 else []
    if r or b or force_rex:
        out.append(rex(r=r, b=b))
    return out + opc + mb, mem


# ------------------------------------------------------------------ cases

GPR16 = [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]   # no rsp
NOT_RBX = [r for r in GPR16 if r != 3]


def count_imm(rng):
    return rng.choice([0, 1, 2, 7, 8, 9, 15, 16, 17, 23, 24, 31, 32, 33, 63, 64, 255,
                       rng.randrange(256), rng.randrange(256), rng.randrange(256)])


def rand64(rng):
    return rng.choice([0, 1, 0xFFFF, 0x8000, 0x7FFF, 0xFF, 0x80, 0x7F, (1 << 64) - 1,
                       rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64),
                       rng.getrandbits(64) & 0xFFFF, rng.getrandbits(64) & ~0xFFFF & ((1 << 64) - 1)])


def rm_operand(rng, regs, byte):
    """A register r/m (a hardware register number; for byte forms with high-byte
    choices encoded later) or [rbx + disp]."""
    if rng.random() < 0.35:
        return ("m", rng.randrange(0, 17) if rng.random() < 0.8 else 0, rng.random() < 0.25)
    return ("r", rng.choice(regs))


def gen_cases(rng, n):
    """Yield (bytes, uses_mem, name)."""
    shift_digits = {"rol": 0, "ror": 1, "shl": 4, "shr": 5, "sar": 7}
    for op, d in shift_digits.items():
        for kind in ("imm", "one", "cl"):
            for _ in range(n):
                rm = rm_operand(rng, GPR16, False)
                opc = {"imm": [0xC1], "one": [0xD1], "cl": [0xD3]}[kind]
                bs, mem = encode(True, opc, d, rm)
                if kind == "imm":
                    bs = bs + [count_imm(rng)]
                yield bs, mem, f"{op}16 {kind}"
    for op, d in (("rol", 0), ("ror", 1)):
        for kind in ("imm", "one", "cl"):
            for _ in range(n):
                rm = rm_operand(rng, GPR16, True)
                opc = {"imm": [0xC0], "one": [0xD0], "cl": [0xD2]}[kind]
                force = rm[0] == "r" and rng.random() < 0.3
                if rm[0] == "r" and not force and rm[1] < 8:
                    # without REX, fields 4..7 are AH CH DH BH
                    rm = ("r", rng.choice([0, 1, 2, 3, 4, 5, 6, 7]))
                bs, mem = encode(False, opc, d, rm, force)
                if kind == "imm":
                    bs = bs + [count_imm(rng)]
                yield bs, mem, f"{op}8 {kind}"
    for sub in (False, True):
        nm = "sbb" if sub else "adc"
        for _ in range(n):  # r/m8, r8
            rm = rm_operand(rng, GPR16, True)
            reg = rng.choice(NOT_RBX if rm[0] == "m" else GPR16)
            if rm[0] == "m" and reg in (7,):
                reg = 6
            bs, mem = encode(False, [0x18 if sub else 0x10], reg, rm, rng.random() < 0.2)
            if mem and len(bs) and bs[0] & 0xF0 != 0x40 and reg == 7:
                pass
            yield bs, mem, f"{nm}8 r/m,r"
        for _ in range(n):  # r8, r/m8
            rm = rm_operand(rng, GPR16, True)
            reg = rng.choice([0, 1, 2, 5, 6, 8, 9, 12, 15] if rm[0] == "m" else GPR16)
            bs, mem = encode(False, [0x1A if sub else 0x12], reg, rm, rng.random() < 0.2)
            yield bs, mem, f"{nm}8 r,r/m"
        for _ in range(n):  # al, imm8
            yield [0x1C if sub else 0x14, rng.randrange(256)], False, f"{nm}8 al,imm"
        for _ in range(n):  # r/m8, imm8
            rm = rm_operand(rng, GPR16, True)
            bs, mem = encode(False, [0x80], 3 if sub else 2, rm, rng.random() < 0.2)
            yield bs + [rng.randrange(256)], mem, f"{nm}8 r/m,imm"
        for _ in range(n):  # r/m16, r16
            rm = rm_operand(rng, GPR16, False)
            reg = rng.choice(NOT_RBX if rm[0] == "m" else GPR16)
            bs, mem = encode(True, [0x19 if sub else 0x11], reg, rm)
            yield bs, mem, f"{nm}16 r/m,r"
        for _ in range(n):  # r16, r/m16
            rm = rm_operand(rng, GPR16, False)
            reg = rng.choice(NOT_RBX if rm[0] == "m" else GPR16)
            bs, mem = encode(True, [0x1B if sub else 0x13], reg, rm)
            yield bs, mem, f"{nm}16 r,r/m"
        for _ in range(n):  # ax, imm16
            yield [0x66, 0x1D if sub else 0x15, rng.randrange(256), rng.randrange(256)], False, \
                f"{nm}16 ax,imm"
        for _ in range(n):  # r/m16, imm16 / imm8
            rm = rm_operand(rng, GPR16, False)
            if rng.random() < 0.5:
                bs, mem = encode(True, [0x81], 3 if sub else 2, rm)
                bs = bs + [rng.randrange(256), rng.randrange(256)]
            else:
                bs, mem = encode(True, [0x83], 3 if sub else 2, rm)
                bs = bs + [rng.randrange(256)]
            yield bs, mem, f"{nm}16 r/m,imm"


# The encodings of the gzip API binaries (zlib 1.3.x, musl) that Str9FsX rejects;
# the memory forms are run with rax/rdi relocated by the generator (base 0x10000 - 0x1730).
CENSUS = [
    ([0x66, 0xC1, 0xE8, 0x0F], False, "census shr ax,0xf"),
    ([0x66, 0xC1, 0xED, 0x07], False, "census shr bp,7"),
    ([0x66, 0x41, 0xC1, 0xEC, 0x07], False, "census shr r12w,7"),
    ([0x80, 0xD9, 0xFF], False, "census sbb cl,0xff"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=24)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = list(gen_cases(rng, args.n))
    for c in CENSUS:
        cases += [c] * args.n
    forms = []
    index = {}
    for bs, _, _ in cases:
        k = tuple(bs)
        if k not in index:
            index[k] = len(forms)
            forms.append(bs)
    tmp = tempfile.mkdtemp()
    exe = build(forms, tmp)
    inputs = []
    for bs, mem, _ in cases:
        regs = [rand64(rng) for _ in range(16)]
        regs[4] = 0
        if mem:
            regs[3] = MEM_BASE + rng.randrange(0, 8)
        fl = (rng.getrandbits(12) & FLAG_MASK) | 0x2
        buf = bytes(rng.getrandbits(8) for _ in range(MEM_LEN))
        inputs.append((bs, mem, regs, fl, buf))
    text = "".join("%d %d %s %x %s\n" % (index[tuple(bs)], int(mem), " ".join("%x" % r for r in regs),
                                         fl, buf.hex()) for bs, mem, regs, fl, buf in inputs)
    res = subprocess.run([exe], input=text, capture_output=True, text=True, check=True).stdout.splitlines()
    assert len(res) == len(inputs), (len(res), len(inputs))
    lines = []
    for (bs, mem, regs, fl, buf), out in zip(inputs, res):
        o = out.split()
        oregs = o[:16]
        ofl = int(o[16], 16) & FLAG_MASK
        obuf = bytes.fromhex(o[17])
        enc = "".join("%02x" % b for b in bs)
        ins = " ".join("%x" % r for r in regs) + " %x %x" % (fl & FLAG_MASK, int.from_bytes(buf, "little"))
        outs = " ".join(oregs) + " %x %x" % (ofl, int.from_bytes(obuf, "little"))
        lines.append(f"{enc} {ins} {outs}")
    cpu = "unknown"
    try:
        for l in open("/proc/cpuinfo"):
            if l.startswith("model name"):
                cpu = l.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    with open(OUT, "w") as f:
        f.write(f"""-- Generated by scripts/x86-narrow/gen_narrow_vectors.py --seed {args.seed} --n {args.n}; do not edit.
module

public import Silmaril.X86.Str9FsXN.Checks
public meta import Silmaril.X86.Str9FsXN.Checks

/-! `Narrow9` instructions executed natively on {cpu} (see the generator):
{len(lines)} vectors over {len(forms)} encodings, each checked by `Str9FsXN.Checks.checkLine`
(one `Str9FsXN.step` from the input state, compared with the processor). -/

namespace Silmaril.X86.Str9FsXN.Vectors

open Silmaril.X86.Str9FsXN.Checks

def vectors : String := "
""" + "\n".join(lines) + f""""

#guard (vectorLines vectors).length = {len(lines)}

#guard (vectorLines vectors).all checkLine

end Silmaril.X86.Str9FsXN.Vectors
""")
    print(f"{len(lines)} vectors, {len(forms)} encodings -> {OUT}")


if __name__ == "__main__":
    main()
