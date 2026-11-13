#!/usr/bin/env python3
"""Generate the differential test vectors of the SSE/SSE2 lane.

Every form of `Silmaril/X86/Features/Ext/Sse2` is executed for real: a
generated C harness loads YMM0, YMM1 (256 bits, with `vmovdqu`), RAX and RDI
(a pointer into a 32-byte buffer), runs the instruction as raw bytes (the
encoding is written here independently of the Lean encoder), and dumps YMM0,
RAX and the buffer. Lean checks `sse2Ext.exec` on the same inputs
(`Sse2.Checks.checkVector`): the same YMM0 with ZMM0 bits 511:256 kept, the
same RAX and buffer. Bits 255:128 of YMM0 are therefore checked against
hardware (legacy SSE keeps them).

The encoding vectors assemble the Intel-syntax text of each form with GNU as
and record the bytes; Lean checks that `Sse2.encode` of the form gives them
and that `Sse2.decode` reads them back.

The host (i7-8700) has SSE2 and AVX, which is all the harness needs; pass
`--qemu PATH` to run it under `qemu-x86_64 -cpu max` instead.

Usage: gen_sse2_vectors.py [--qemu PATH] [--seed N]
Writes Silmaril/X86/Features/Ext/Sse2/Vectors.lean.
"""

import argparse
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Features", "Ext", "Sse2", "Vectors.lean")

MEM_RDI = "{ base := .rdi }"

# (lean name, opcode, lane width or None)
BINOPS = [
    ("(.logic .and)", 0xDB, None), ("(.logic .andn)", 0xDF, None),
    ("(.logic .or)", 0xEB, None), ("(.logic .xor)", 0xEF, None),
    ("(.add .b)", 0xFC, 8), ("(.add .w)", 0xFD, 16), ("(.add .d)", 0xFE, 32),
    ("(.add .q)", 0xD4, 64),
    ("(.sub .b)", 0xF8, 8), ("(.sub .w)", 0xF9, 16), ("(.sub .d)", 0xFA, 32),
    ("(.sub .q)", 0xFB, 64),
    ("(.cmpeq .b)", 0x74, 8), ("(.cmpeq .w)", 0x75, 16), ("(.cmpeq .d)", 0x76, 32),
    ("(.unpackLo .b)", 0x60, 8), ("(.unpackLo .w)", 0x61, 16), ("(.unpackLo .d)", 0x62, 32),
    ("(.unpackLo .q)", 0x6C, 64),
    ("(.unpackHi .b)", 0x68, 8), ("(.unpackHi .w)", 0x69, 16), ("(.unpackHi .d)", 0x6A, 32),
    ("(.unpackHi .q)", 0x6D, 64),
    ("(.shift .srlw)", 0xD1, "shift"), ("(.shift .srld)", 0xD2, "shift"),
    ("(.shift .srlq)", 0xD3, "shift"), ("(.shift .sraw)", 0xE1, "shift"),
    ("(.shift .srad)", 0xE2, "shift"), ("(.shift .sllw)", 0xF1, "shift"),
    ("(.shift .slld)", 0xF2, "shift"), ("(.shift .sllq)", 0xF3, "shift"),
]

# (lean MovKind, prefix bytes, load opcode, store opcode, aligned, register load form here)
MOVS = [
    (".dqa", [0x66], 0x6F, 0x7F, True, True),
    (".dqu", [0xF3], 0x6F, 0x7F, False, True),
    (".aps", [], 0x28, 0x29, True, False),
    (".ups", [], 0x10, 0x11, False, True),
    (".apd", [0x66], 0x28, 0x29, True, False),
    (".upd", [0x66], 0x10, 0x11, False, True),
]

SHIFTS = [(".srlw", 0x71, 2), (".sraw", 0x71, 4), (".sllw", 0x71, 6),
          (".srld", 0x72, 2), (".srad", 0x72, 4), (".slld", 0x72, 6),
          (".srlq", 0x73, 2), (".sllq", 0x73, 6)]

SHIFT_COUNTS = [0, 1, 3, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256,
                2**32, 2**63, 2**64 - 1]
SHIFT_IMMS = [0, 1, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 128, 255]
BYTE_IMMS = [0, 1, 5, 8, 15, 16, 17, 255]
WORD_IMMS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 255]


class Form:
    """One executable case: a Lean term, its bytes, the inputs it needs."""

    def __init__(self, lean, code, kind, imm=0, offsets=(0,), lanes=None):
        self.lean, self.code, self.kind, self.imm = lean, code, kind, imm
        self.offsets, self.lanes = offsets, lanes


def forms():
    out = []
    aligned_offs = (0, 16)
    any_offs = tuple(range(0, 17))
    for name, opc, lanes in BINOPS:
        kind = "shift" if lanes == "shift" else "bin"
        w = None if lanes == "shift" else lanes
        out.append(Form(f".binop {name} .xmm0 (.reg .xmm1)", [0x66, 0x0F, opc, 0xC1], kind,
                        lanes=w))
        out.append(Form(f".binop {name} .xmm0 (.mem {MEM_RDI})", [0x66, 0x0F, opc, 0x07],
                        "binmem", offsets=aligned_offs, lanes=w))
        out.append(Form(f".binop {name} .xmm0 (.reg .xmm0)", [0x66, 0x0F, opc, 0xC0], "bin"))
    for k, pfx, ld, st, aligned, rr in MOVS:
        offs = aligned_offs if aligned else any_offs
        out.append(Form(f".movLoad {k} .xmm0 {MEM_RDI}", pfx + [0x0F, ld, 0x07], "load",
                        offsets=offs))
        out.append(Form(f".movStore {k} {MEM_RDI} .xmm0", pfx + [0x0F, st, 0x07], "store",
                        offsets=offs))
        out.append(Form(f".movRRStore {k} .xmm0 .xmm1", pfx + [0x0F, st, 0xC8], "bin"))
        if rr:
            out.append(Form(f".movRR {k} .xmm0 .xmm1", pfx + [0x0F, ld, 0xC1], "bin"))
    for w, rex in ((".w32", []), (".w64", [0x48])):
        out.append(Form(f".movdLoad {w} .xmm0 {MEM_RDI}", [0x66] + rex + [0x0F, 0x6E, 0x07],
                        "load", offsets=any_offs))
        out.append(Form(f".movdStore {w} {MEM_RDI} .xmm0", [0x66] + rex + [0x0F, 0x7E, 0x07],
                        "store", offsets=any_offs))
    out.append(Form(".movqLoad .xmm0 (.reg .xmm1)", [0xF3, 0x0F, 0x7E, 0xC1], "bin"))
    out.append(Form(f".movqLoad .xmm0 (.mem {MEM_RDI})", [0xF3, 0x0F, 0x7E, 0x07], "load",
                    offsets=any_offs))
    out.append(Form(".movqStore (.reg .xmm0) .xmm1", [0x66, 0x0F, 0xD6, 0xC8], "bin"))
    out.append(Form(f".movqStore (.mem {MEM_RDI}) .xmm0", [0x66, 0x0F, 0xD6, 0x07], "store",
                    offsets=any_offs))
    for k, opc, digit in SHIFTS:
        for imm in SHIFT_IMMS:
            out.append(Form(f".shiftImm {k} .xmm0 {imm}", [0x66, 0x0F, opc, 0xC0 | digit << 3, imm],
                            "bin", imm=imm))
    for left, digit in (("false", 3), ("true", 7)):
        for imm in BYTE_IMMS:
            out.append(Form(f".shiftBytes {left} .xmm0 {imm}",
                            [0x66, 0x0F, 0x73, 0xC0 | digit << 3, imm], "bin", imm=imm))
    rnd = random.Random(7)
    for imm in [0x00, 0x1B, 0xE4, 0x4E, 0xB1, 0xFF] + [rnd.randrange(256) for _ in range(6)]:
        out.append(Form(f".pshufd .xmm0 (.reg .xmm1) {imm}", [0x66, 0x0F, 0x70, 0xC1, imm],
                        "bin", imm=imm))
        out.append(Form(f".pshufd .xmm0 (.mem {MEM_RDI}) {imm}", [0x66, 0x0F, 0x70, 0x07, imm],
                        "binmem", imm=imm, offsets=aligned_offs))
    out.append(Form(".pmovmskb .rax .xmm1", [0x66, 0x0F, 0xD7, 0xC1], "bin"))
    for imm in WORD_IMMS:
        out.append(Form(f".pinsrw .xmm0 (.reg .rax) {imm}", [0x66, 0x0F, 0xC4, 0xC0, imm], "bin",
                        imm=imm))
        out.append(Form(f".pinsrw .xmm0 (.mem {MEM_RDI}) {imm}", [0x66, 0x0F, 0xC4, 0x07, imm],
                        "load", imm=imm, offsets=tuple(range(0, 31, 3))))
        out.append(Form(f".pextrw .rax .xmm1 {imm}", [0x66, 0x0F, 0xC5, 0xC1, imm], "bin",
                        imm=imm))
    return out


def stub(i, f):
    code = ",".join(f"0x{b:02x}" for b in f.code)
    return f"""static void run{i}(unsigned char *st, unsigned char *mem, unsigned long *rax) {{
  __asm__ volatile(
    "vmovdqu (%0), %%ymm0\\n\\tvmovdqu 32(%0), %%ymm1\\n\\tmovq (%2), %%rax\\n\\tmovq %1, %%rdi\\n\\t"
    ".byte {code}\\n\\t"
    "vmovdqu %%ymm0, (%0)\\n\\tvmovdqu %%ymm1, 32(%0)\\n\\tmovq %%rax, (%2)\\n\\t"
    :: "r"(st), "r"(mem), "r"(rax) : "rax", "rdi", "xmm0", "xmm1", "memory");
}}
"""


def harness(fs):
    out = ["#include <stdio.h>", "#include <string.h>", ""]
    out += [stub(i, f) for i, f in enumerate(fs)]
    out.append("typedef void (*fn)(unsigned char *, unsigned char *, unsigned long *);")
    out.append("static fn table[] = {" + ", ".join(f"run{i}" for i in range(len(fs))) + "};")
    out.append(r"""
static int hexbyte(const char *s) { int v; sscanf(s, "%2x", &v); return v; }
int main(void) {
  char line[1024];
  static unsigned char st[64], buf[64] __attribute__((aligned(32)));
  while (fgets(line, sizeof line, stdin)) {
    int id, off; char a[129], m[65]; unsigned long rax;
    if (sscanf(line, "%d %128s %lx %d %64s", &id, a, &rax, &off, m) != 5) continue;
    for (int i = 0; i < 64; i++) st[i] = hexbyte(a + 2 * i);
    for (int i = 0; i < 32; i++) buf[i] = hexbyte(m + 2 * i);
    table[id](st, buf + off, &rax);
    for (int i = 0; i < 64; i++) printf("%02x", st[i]);
    printf(" %lx ", rax);
    for (int i = 0; i < 32; i++) printf("%02x", buf[i]);
    printf("\n");
  }
  return 0;
}
""")
    return "\n".join(out)


def le_hex(n, nbytes):
    return n.to_bytes(nbytes, "little").hex()


def from_le_hex(s):
    return int.from_bytes(bytes.fromhex(s), "little")


def inputs(f, rnd):
    """Inputs (ymm0, ymm1, rax, off, mem) for one execution of `f`."""
    cases = []
    for k in range(12):
        a = rnd.getrandbits(256)
        b = rnd.getrandbits(256)
        if f.lanes and k % 2 == 0:
            w = f.lanes
            for i in range(128 // w):
                if rnd.random() < 0.5:
                    mask = ((1 << w) - 1) << (w * i)
                    b = (b & ~mask) | (a & mask)
        if f.kind == "shift":
            b = (b >> 64 << 64) | SHIFT_COUNTS[k % len(SHIFT_COUNTS)]
        if k == 0:
            b = a
        rax = rnd.getrandbits(64)
        mem = rnd.getrandbits(256)
        off = f.offsets[k % len(f.offsets)]
        cases.append((a, b, rax, off, mem))
    if f.kind == "shift":
        for c in SHIFT_COUNTS[12:]:
            a, b = rnd.getrandbits(256), rnd.getrandbits(256)
            cases.append((a, (b >> 64 << 64) | c, rnd.getrandbits(64), 0, rnd.getrandbits(256)))
    return cases


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw).stdout


def semantic_vectors(fs, qemu, seed):
    rnd = random.Random(seed)
    tmp = tempfile.mkdtemp()
    src, exe = os.path.join(tmp, "h.c"), os.path.join(tmp, "h")
    with open(src, "w") as fh:
        fh.write(harness(fs))
    run(["gcc", "-O1", "-mavx", "-o", exe, src])
    jobs = []
    for i, f in enumerate(fs):
        for a, b, rax, off, mem in inputs(f, rnd):
            jobs.append((i, f, a, b, rax, off, mem))
    stdin = "".join(
        f"{i} {le_hex(a, 32)}{le_hex(b, 32)} {rax:x} {off} {le_hex(mem, 32)}\n"
        for i, f, a, b, rax, off, mem in jobs)
    cmd = [qemu, "-cpu", "max", exe] if qemu else [exe]
    out = subprocess.run(cmd, input=stdin, check=True, capture_output=True, text=True).stdout
    lines = []
    for (i, f, a, b, rax, off, mem), res in zip(jobs, out.splitlines(), strict=True):
        st, rax2, mem2 = res.split()
        ra, rb = from_le_hex(st[:64]), from_le_hex(st[64:])
        assert rb == b, f"form {i} changed ymm1"
        lines.append(f"{i:x} {a:x} {b:x} {rax:x} {off:x} {mem:x} {ra:x} {rax2} {from_le_hex(mem2):x}")
    return lines


# Intel-syntax texts for the encoding vectors: (Lean term, GNU as text).
def encoding_cases():
    regs = [0, 1, 7, 8, 9, 15]
    gprs = [("rax", "eax"), ("rcx", "ecx"), ("r8", "r8d"), ("r15", "r15d")]
    mems = [("{ base := .rdi }", "[rdi]"), ("{ base := .r8, disp := 0x10 }", "[r8+0x10]"),
            ("{ base := .rsp, disp := 0x20 }", "[rsp+0x20]"),
            ("{ base := .rbp, disp := 0xFFFFFF80 }", "[rbp-0x80]"),
            ("{ base := .rax, index := some (⟨.rcx, by decide⟩, .s8), disp := 0x100 }",
             "[rax+rcx*8+0x100]"),
            ("{ base := .r13 }", "[r13]")]
    names = {0xDB: "pand", 0xDF: "pandn", 0xEB: "por", 0xEF: "pxor", 0xFC: "paddb", 0xFD: "paddw",
             0xFE: "paddd", 0xD4: "paddq", 0xF8: "psubb", 0xF9: "psubw", 0xFA: "psubd",
             0xFB: "psubq", 0x74: "pcmpeqb", 0x75: "pcmpeqw", 0x76: "pcmpeqd",
             0x60: "punpcklbw", 0x61: "punpcklwd", 0x62: "punpckldq", 0x6C: "punpcklqdq",
             0x68: "punpckhbw", 0x69: "punpckhwd", 0x6A: "punpckhdq", 0x6D: "punpckhqdq",
             0xD1: "psrlw", 0xD2: "psrld", 0xD3: "psrlq", 0xE1: "psraw", 0xE2: "psrad",
             0xF1: "psllw", 0xF2: "pslld", 0xF3: "psllq"}
    mov_names = {".dqa": "movdqa", ".dqu": "movdqu", ".aps": "movaps", ".ups": "movups",
                 ".apd": "movapd", ".upd": "movupd"}
    rnd = random.Random(11)
    out = []
    for name, opc, _ in BINOPS:
        for d in rnd.sample(regs, 2):
            s = rnd.choice(regs)
            out.append((f".binop {name} .xmm{d} (.reg .xmm{s})", f"{names[opc]} xmm{d}, xmm{s}"))
            lm, tm = rnd.choice(mems)
            out.append((f".binop {name} .xmm{d} (.mem {lm})",
                        f"{names[opc]} xmm{d}, XMMWORD PTR {tm}"))
    for k, _, _, _, _, rr in MOVS:
        for d in rnd.sample(regs, 2):
            lm, tm = rnd.choice(mems)
            out.append((f".movLoad {k} .xmm{d} {lm}", f"{mov_names[k]} xmm{d}, XMMWORD PTR {tm}"))
            out.append((f".movStore {k} {lm} .xmm{d}", f"{mov_names[k]} XMMWORD PTR {tm}, xmm{d}"))
            s = rnd.choice(regs)
            if rr:
                out.append((f".movRR {k} .xmm{d} .xmm{s}", f"{mov_names[k]} xmm{d}, xmm{s}"))
            out.append((f".movRRStore {k} .xmm{d} .xmm{s}",
                        f"{{store}} {mov_names[k]} xmm{d}, xmm{s}"))
    for d in rnd.sample(regs, 3):
        lm, tm = rnd.choice(mems)
        out.append((f".movdLoad .w32 .xmm{d} {lm}", f"movd xmm{d}, DWORD PTR {tm}"))
        out.append((f".movdStore .w32 {lm} .xmm{d}", f"movd DWORD PTR {tm}, xmm{d}"))
        out.append((f".movqLoad .xmm{d} (.mem {lm})", f"movq xmm{d}, QWORD PTR {tm}"))
        out.append((f".movqStore (.mem {lm}) .xmm{d}", f"movq QWORD PTR {tm}, xmm{d}"))
        s = rnd.choice(regs)
        out.append((f".movqLoad .xmm{d} (.reg .xmm{s})", f"movq xmm{d}, xmm{s}"))
        out.append((f".movqStore (.reg .xmm{d}) .xmm{s}", f"{{store}} movq xmm{d}, xmm{s}"))
    for k, _, _ in SHIFTS:
        mn = {".srlw": "psrlw", ".sraw": "psraw", ".sllw": "psllw", ".srld": "psrld",
              ".srad": "psrad", ".slld": "pslld", ".srlq": "psrlq", ".sllq": "psllq"}[k]
        d = rnd.choice(regs)
        imm = rnd.choice(SHIFT_IMMS)
        out.append((f".shiftImm {k} .xmm{d} {imm}", f"{mn} xmm{d}, {imm}"))
    for left, mn in (("false", "psrldq"), ("true", "pslldq")):
        d = rnd.choice(regs)
        out.append((f".shiftBytes {left} .xmm{d} 4", f"{mn} xmm{d}, 4"))
    for d in rnd.sample(regs, 3):
        s = rnd.choice(regs)
        imm = rnd.randrange(256)
        lm, tm = rnd.choice(mems)
        out.append((f".pshufd .xmm{d} (.reg .xmm{s}) {imm}", f"pshufd xmm{d}, xmm{s}, {imm}"))
        out.append((f".pshufd .xmm{d} (.mem {lm}) {imm}",
                    f"pshufd xmm{d}, XMMWORD PTR {tm}, {imm}"))
        g, g32 = rnd.choice(gprs)
        out.append((f".pmovmskb .{g} .xmm{s}", f"pmovmskb {g32}, xmm{s}"))
        out.append((f".pinsrw .xmm{d} (.reg .{g}) {imm % 8}", f"pinsrw xmm{d}, {g32}, {imm % 8}"))
        out.append((f".pinsrw .xmm{d} (.mem {lm}) {imm % 8}",
                    f"pinsrw xmm{d}, WORD PTR {tm}, {imm % 8}"))
        out.append((f".pextrw .{g} .xmm{s} {imm % 8}", f"pextrw {g32}, xmm{s}, {imm % 8}"))
    return out


def encoding_vectors(cases):
    tmp = tempfile.mkdtemp()
    src, obj = os.path.join(tmp, "e.s"), os.path.join(tmp, "e.o")
    with open(src, "w") as fh:
        fh.write(".intel_syntax noprefix\n")
        for _, text in cases:
            fh.write(f"{text}\n.byte 0xcc,0xcc,0xcc\n")
    run(["as", "--64", "-o", obj, src])
    binp = os.path.join(tmp, "e.bin")
    run(["objcopy", "-O", "binary", "-j", ".text", obj, binp])
    with open(binp, "rb") as fh:
        raw = fh.read()
    chunks = raw.split(b"\xcc\xcc\xcc")[:-1]
    assert len(chunks) == len(cases), (len(chunks), len(cases))
    return [(lean, list(c)) for (lean, _), c in zip(cases, chunks)]


HEADER = """-- Generated by scripts/x86-features/gen_sse2_vectors.py; do not edit.
module

public import Silmaril.X86.Features.Ext.Sse2.Checks
public meta import Silmaril.X86.Features.Ext.Sse2.Checks

/-! Differential vectors of the SSE/SSE2 lane (see the generator).

* `form n imm` is the instruction of harness case `n` (operands XMM0, XMM1,
  RAX, `[rdi]`).
* Each line of `vectors` is `case ymm0 ymm1 rax offset buffer ymm0' rax' buffer'`
  in hex, the inputs and outputs of one native execution (`checkLine`).
* `encodings` pairs a form with the bytes GNU as assembles for its Intel-syntax
  text; `Sse2.encode` must give exactly those bytes and `Sse2.decode` must read
  them back.
-/

@[expose] public section

namespace Silmaril.X86.Features.Sse2.Vectors

open Silmaril.X86
open Silmaril.X86.Features.Sse2
open Silmaril.X86.Features.Sse2.Checks

"""


def write(fs, sem, enc):
    lines = [HEADER]
    lines.append("/-- The instruction of each harness case. -/")
    lines.append("def form : Nat → Instr")
    for i, f in enumerate(fs):
        lines.append(f"  | {i} => {f.lean}")
    lines.append("  | _ => .binop (.logic .xor) .xmm0 (.reg .xmm1)")
    lines.append("")
    lines.append("def checkLine : List Nat → Bool")
    lines.append("  | [n, a, b, rax, off, mem, ra, rax', mem'] => checkVector (form n) a b rax off mem ra rax' mem'")
    lines.append("  | _ => false")
    lines.append("")
    lines.append('def vectors : String := "')
    lines += sem
    lines[-1] += '"'
    lines.append("")
    lines.append(f"#guard (hexFields vectors).length = {len(sem)}")
    lines.append("")
    lines.append("#guard (hexFields vectors).all checkLine")
    lines.append("")
    lines.append("/-- Forms with the bytes GNU as assembles for them. -/")
    lines.append("def encodings : List (Instr × List Byte) := [")
    for k, (lean, bs) in enumerate(enc):
        sep = "," if k + 1 < len(enc) else ""
        lines.append(f"  ({lean}, [{', '.join(f'0x{b:02X}' for b in bs)}]){sep}")
    lines.append("]")
    lines.append("")
    lines.append(f"#guard encodings.length = {len(enc)}")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => encode i == bs")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => decode bs == some (i, bs.length)")
    lines.append("")
    lines.append("end Silmaril.X86.Features.Sse2.Vectors")
    with open(OUT, "w") as fh:
        fh.write("\n".join(lines) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu")
    ap.add_argument("--seed", type=int, default=2026)
    args = ap.parse_args()
    fs = forms()
    sem = semantic_vectors(fs, args.qemu, args.seed)
    enc = encoding_vectors(encoding_cases())
    write(fs, sem, enc)
    print(f"{len(fs)} forms, {len(sem)} vectors, {len(enc)} encodings -> {OUT}", file=sys.stderr)


if __name__ == "__main__":
    main()
