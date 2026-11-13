#!/usr/bin/env python3
"""Generate the hardware vectors of Silmaril/X86/Str9D/Vectors.lean.

Oracle: the host processor (an Intel Core i7-8700 when the committed vectors
were generated). Every case is a short instruction sequence of
`Silmaril.X86.Str9D` (the six string forms of the Str9 tower with DF clear or
set, `std`, `cld`, a few non-string forms with DF set, and the backward tail of
glibc's `__memmove_erms`), assembled as raw bytes (`.byte`) into a function

    pushfq image; popfq          ; CF PF AF ZF SF OF and DF from the case
    load rax..r15 (not rsp)      ; rdi last
    <instructions>
    pushfq; cld; store rax..r15 and RFLAGS

that runs on a 64-byte buffer. `rsi` and `rdi` are buffer addresses (the model
puts the buffer at 0x10000): the harness relocates both to the real buffer
before the case and back after it (the cases use them linearly only).

Each vector line is, in hex:

    enc r0..r15 rflags mem | r0'..r15' rflags' mem'

with registers in hardware order (rax rcx rdx rbx rsp rbp rsi rdi r8..r15; rsp
is 0 and not compared), `enc` the code bytes, `mem` the buffer as a
little-endian number, `rflags` masked to CF PF AF ZF SF OF DF.
`Str9D.Checks.checkLine` runs `Str9D.step` from the input state (code at
0x1000, executable; buffer read-write) until RIP leaves the code and compares
RIP, the fifteen registers, every flag the model defines, DF and the buffer.

Usage: gen_dir_vectors.py [--seed N] [--n PER_CASE]
"""

import argparse
import os
import random
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Str9D", "Vectors.lean")

MEM_BASE = 0x10000
MEM_LEN = 64
FLAG_MASK = 0x8D5 | 0x400  # CF PF AF ZF SF OF, DF
DF = 0x400

HARNESS_C = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
struct st { uint64_t r[16]; uint64_t fl; };
typedef void (*fn)(struct st *s);
extern fn table[];
static unsigned char mem[128] __attribute__((aligned(64)));
int main(void) {
  static char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    int idx; struct st s; char ms[256];
    unsigned long long v[17];
    if (sscanf(line, "%d %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %255s",
               &idx, &v[0], &v[1], &v[2], &v[3], &v[4], &v[5], &v[6], &v[7], &v[8], &v[9],
               &v[10], &v[11], &v[12], &v[13], &v[14], &v[15], &v[16], ms) != 19) break;
    for (int i = 0; i < 16; i++) s.r[i] = v[i];
    s.fl = v[16];
    memset(mem, 0, sizeof mem);
    for (int i = 0; i < 64; i++) { unsigned b; sscanf(ms + 2 * i, "%2x", &b); mem[i] = b; }
    uint64_t delta = (uint64_t)(uintptr_t)mem - 0x10000ull;
    s.r[6] += delta; s.r[7] += delta;
    table[idx](&s);
    s.r[6] -= delta; s.r[7] -= delta;
    for (int i = 0; i < 16; i++) printf("%llx ", (unsigned long long)s.r[i]);
    printf("%llx ", (unsigned long long)s.fl);
    for (int i = 0; i < 64; i++) printf("%02x", mem[i]);
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
        asm += ["  pushfq", "  cld", "  xchg %rdi, 8(%rsp)"]
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


# ------------------------------------------------------------------ cases

# (bytes, element width, move?, rep?)
STRINGS = {
    "movsb": ([0xA4], 1, True, False),
    "rep movsb": ([0xF3, 0xA4], 1, True, True),
    "rep movsq": ([0xF3, 0x48, 0xA5], 8, True, True),
    "rep stosb": ([0xF3, 0xAA], 1, False, True),
    "rep stosd": ([0xF3, 0xAB], 4, False, True),
    "rep stosq": ([0xF3, 0x48, 0xAB], 8, False, True),
}

# Non-string forms run with either DF (they must not read it).
OTHERS = [
    [0x48, 0x8D, 0x7C, 0x0F, 0xFF],  # lea -1(%rdi,%rcx), %rdi
    [0x48, 0x8D, 0x74, 0x0E, 0xFF],  # lea -1(%rsi,%rcx), %rsi
    [0x48, 0x89, 0xD1],              # mov %rdx, %rcx
    [0x48, 0x39, 0xF7],              # cmp %rsi, %rdi
    [0x48, 0x01, 0xD8],              # add %rbx, %rax
]

# __memmove_erms's backward tail (glibc 2.39): lea; lea; std; rep movsb; cld.
ERMS_TAIL = [0x48, 0x8D, 0x7C, 0x0F, 0xFF, 0x48, 0x8D, 0x74, 0x0E, 0xFF, 0xFD, 0xF3, 0xA4, 0xFC]


def rand64(rng):
    return rng.choice([0, 1, 0xFF, 0x80, 0x7F, (1 << 64) - 1, rng.getrandbits(64), rng.getrandbits(64),
                       rng.getrandbits(64)])


def base_regs(rng):
    regs = [rand64(rng) for _ in range(16)]
    regs[4] = 0
    regs[6] = MEM_BASE + rng.randrange(MEM_LEN)
    regs[7] = MEM_BASE + rng.randrange(MEM_LEN)
    return regs


def string_case(rng, form, df):
    bs, k, move, rep = STRINGS[form]
    regs = base_regs(rng)
    count = rng.choice([0, 1, 2, 3, rng.randrange(1, 64 // k + 1)]) if rep else 1
    count = min(count, MEM_LEN // k)
    if rep:
        regs[1] = count
    elems = max(count, 1)

    def off():
        if df:  # first element at off, last at off - (elems-1)k
            return rng.randrange((elems - 1) * k, MEM_LEN - k + 1)
        return rng.randrange(0, MEM_LEN - elems * k + 1)
    regs[7] = MEM_BASE + off()
    if move:
        regs[6] = MEM_BASE + off()
    return bs, regs


def gen_cases(rng, n):
    """Yield (bytes, regs, df)."""
    for form in STRINGS:
        for df in (False, True):
            for _ in range(n):
                bs, regs = string_case(rng, form, df)
                yield bs, regs, df
    for bs in ([0xFD], [0xFC]):
        for df in (False, True):
            for _ in range(n // 4 + 1):
                yield bs, base_regs(rng), df
    for bs in OTHERS:
        for df in (False, True):
            for _ in range(n // 2 + 1):
                regs = base_regs(rng)
                regs[1] = rng.randrange(0, 2 * MEM_LEN)  # rcx: a length
                yield bs, regs, df
    for _ in range(2 * n):  # overlapping backward copy, rdi > rsi
        regs = base_regs(rng)
        length = rng.randrange(1, 33)
        src = rng.randrange(0, MEM_LEN - length)
        dst = rng.randrange(src + 1, MEM_LEN - length + 1)
        regs[1], regs[6], regs[7] = length, MEM_BASE + src, MEM_BASE + dst
        yield ERMS_TAIL, regs, False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=40)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = list(gen_cases(rng, args.n))
    forms, index = [], {}
    for bs, _, _ in cases:
        if tuple(bs) not in index:
            index[tuple(bs)] = len(forms)
            forms.append(bs)
    exe = build(forms, tempfile.mkdtemp())
    inputs = []
    for bs, regs, df in cases:
        fl = (rng.getrandbits(12) & 0x8D5) | (DF if df else 0) | 0x2
        buf = bytes(rng.getrandbits(8) for _ in range(MEM_LEN))
        inputs.append((bs, regs, fl, buf))
    text = "".join("%d %s %x %s\n" % (index[tuple(bs)], " ".join("%x" % r for r in regs), fl, buf.hex())
                   for bs, regs, fl, buf in inputs)
    res = subprocess.run([exe], input=text, capture_output=True, text=True, check=True).stdout.splitlines()
    assert len(res) == len(inputs), (len(res), len(inputs))
    lines = []
    for (bs, regs, fl, buf), out in zip(inputs, res):
        o = out.split()
        ofl = int(o[16], 16) & FLAG_MASK
        obuf = bytes.fromhex(o[17])
        enc = "".join("%02x" % b for b in bs)
        ins = " ".join("%x" % r for r in regs) + " %x %x" % (fl & FLAG_MASK, int.from_bytes(buf, "little"))
        outs = " ".join(o[:16]) + " %x %x" % (ofl, int.from_bytes(obuf, "little"))
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
        f.write(f"""-- Generated by scripts/x86-dir/gen_dir_vectors.py --seed {args.seed} --n {args.n}; do not edit.
module

public import Silmaril.X86.Str9D.Checks
public meta import Silmaril.X86.Str9D.Checks

/-! Direction-flag cases executed natively on {cpu} (see the generator):
{len(lines)} vectors over {len(forms)} encodings, each checked by `Str9D.Checks.checkLine`
(`Str9D.step` from the input state until RIP leaves the code, compared with the processor)
and the string forms also by `Str9D.Checks.checkExecStr` (`execStr` alone). -/

namespace Silmaril.X86.Str9D.Vectors

open Silmaril.X86.Str9D.Checks

def vectors : String := "
""" + "\n".join(lines) + f""""

#guard (vectorLines vectors).length = {len(lines)}

#guard (vectorLines vectors).all checkLine

#guard (vectorLines vectors).all checkExecStr

end Silmaril.X86.Str9D.Vectors
""")
    print(f"{len(lines)} vectors, {len(forms)} encodings -> {OUT}")


if __name__ == "__main__":
    main()
