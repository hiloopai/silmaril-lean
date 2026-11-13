#!/usr/bin/env python3
"""Generate the differential vectors of the forms only the SsePacked lane has.

The SSE2 lane's native vectors (`gen_sse2_vectors.py`) already cover the forms
both lanes decode (`SseMerged/Vectors.lean` replays them through SsePacked).
This script covers the rest of `Silmaril/X86/Features/Ext/SsePacked`: the
saturating, multiplying, averaging, min/max, compare-greater and packing
integer forms, PSHUFHW/PSHUFLW, MOVMSKPS/PD, MOVHLPS/MOVLHPS, MOVLPS/MOVHPS
and the PD forms, the non-temporal stores, MASKMOVDQU, the packed
floating-point arithmetic, square roots, compares, conversions, unpacks and
shuffles, and the fences and prefetches.

It reuses the harness of `gen_sse2_vectors.py` unchanged. YMM0, YMM1, RAX and
RDI (a pointer into a 32-byte buffer) are loaded, the instruction runs as raw
bytes on the host CPU, and YMM0, RAX and the buffer are recorded. Lean checks
`SsePacked.ext.exec` on the same inputs with `SseMerged.Vectors.checkPacked`.
MXCSR is the process default (`0x1F80`, all exceptions masked, round to
nearest); its flags are not compared. The approximate reciprocals (RCPPS and
friends, `unmodeled`) and RIP-relative operands are not executed.

The hand-written bytes of every form are checked against GNU as here, and the
GNU as bytes are also emitted, with REX and RIP-relative variants, as encoding
vectors for `SsePacked.encode`/`decode`.

Usage: gen_sse_packed_vectors.py [--qemu PATH] [--seed N]
Writes Silmaril/X86/Features/Ext/SseMerged/PackedVectors.lean.
"""

import argparse
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_sse2_vectors as g  # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Features", "Ext", "SseMerged", "PackedVectors.lean")

RDI = "(.mem { base := .rdi })"
SRC_MEM = f"(.mem {RDI})"

# (PIntOp, opcode, mnemonic, lane width for equal-lane mixing)
PINT = [
    ("paddsb", 0xEC, 8), ("paddsw", 0xED, 16), ("paddusb", 0xDC, 8), ("paddusw", 0xDD, 16),
    ("psubsb", 0xE8, 8), ("psubsw", 0xE9, 16), ("psubusb", 0xD8, 8), ("psubusw", 0xD9, 16),
    ("pmullw", 0xD5, None), ("pmulhw", 0xE5, None), ("pmulhuw", 0xE4, None),
    ("pmuludq", 0xF4, None), ("pmaddwd", 0xF5, None), ("psadbw", 0xF6, None),
    ("pavgb", 0xE0, 8), ("pavgw", 0xE3, 16), ("pminub", 0xDA, 8), ("pmaxub", 0xDE, 8),
    ("pminsw", 0xEA, 16), ("pmaxsw", 0xEE, 16),
    ("pcmpgtb", 0x64, 8), ("pcmpgtw", 0x65, 16), ("pcmpgtd", 0x66, 32),
    ("packsswb", 0x63, None), ("packssdw", 0x6B, None), ("packuswb", 0x67, None),
]

PREC = [("single", [], "ps", 32), ("double", [0x66], "pd", 64)]
ARITH = [("add", 0x58), ("mul", 0x59), ("sub", 0x5C), ("min", 0x5D), ("div", 0x5E),
         ("max", 0x5F)]
CMP = ["eq", "lt", "le", "unord", "neq", "nlt", "nle", "ord"]
# (CvtKind, prefix, opcode, mnemonic)
CVT = [("dq2ps", [], 0x5B, "cvtdq2ps"), ("ps2dq", [0x66], 0x5B, "cvtps2dq"),
       ("tps2dq", [0xF3], 0x5B, "cvttps2dq"), ("ps2pd", [], 0x5A, "cvtps2pd"),
       ("pd2ps", [0x66], 0x5A, "cvtpd2ps"), ("dq2pd", [0xF3], 0xE6, "cvtdq2pd"),
       ("pd2dq", [0xF2], 0xE6, "cvtpd2dq"), ("tpd2dq", [0x66], 0xE6, "cvttpd2dq")]
CVT_HALF = {"ps2pd", "dq2pd"}

ALIGNED = (0, 16)
ANY = tuple(range(0, 17))
IMMS = [0x00, 0x1B, 0xE4, 0x4E, 0xB1, 0xFF, 0x01, 0x02, 0x03]


class F(g.Form):
    def __init__(self, lean, code, kind, text, imm=0, offsets=(0,), lanes=None):
        super().__init__(lean, code, kind, imm=imm, offsets=offsets, lanes=lanes)
        self.text = text


def forms():
    out = []
    for op, opc, w in PINT:
        out.append(F(f".pint .{op} .xmm0 (.reg .xmm1)", [0x66, 0x0F, opc, 0xC1], "bin",
                     f"{op} xmm0, xmm1", lanes=w))
        out.append(F(f".pint .{op} .xmm0 {SRC_MEM}", [0x66, 0x0F, opc, 0x07], "binmem",
                     f"{op} xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED, lanes=w))
    for k, pfx, mn in (("hw", 0xF3, "pshufhw"), ("lw", 0xF2, "pshuflw")):
        for imm in IMMS[:6]:
            out.append(F(f".pshuf .{k} .xmm0 (.reg .xmm1) {imm}", [pfx, 0x0F, 0x70, 0xC1, imm],
                         "bin", f"{mn} xmm0, xmm1, {imm}", imm=imm))
        out.append(F(f".pshuf .{k} .xmm0 {SRC_MEM} 27", [pfx, 0x0F, 0x70, 0x07, 27], "binmem",
                     f"{mn} xmm0, XMMWORD PTR [rdi], 27", imm=27, offsets=ALIGNED))
    out.append(F(".movmsk .ps .rax .xmm1", [0x0F, 0x50, 0xC1], "bin", "movmskps eax, xmm1"))
    out.append(F(".movmsk .pd .rax .xmm1", [0x66, 0x0F, 0x50, 0xC1], "bin", "movmskpd eax, xmm1"))
    out.append(F(".movhlps .xmm0 .xmm1", [0x0F, 0x12, 0xC1], "bin", "movhlps xmm0, xmm1"))
    out.append(F(".movlhps .xmm0 .xmm1", [0x0F, 0x16, 0xC1], "bin", "movlhps xmm0, xmm1"))
    for high, lo_opc, mn in (("false", 0x12, "movlp"), ("true", 0x16, "movhp")):
        for pd, pfx, suf in (("false", [], "s"), ("true", [0x66], "d")):
            out.append(F(f".movHalfLoad {high} {pd} .xmm0 {RDI}", pfx + [0x0F, lo_opc, 0x07],
                         "load", f"{mn}{suf} xmm0, QWORD PTR [rdi]", offsets=ANY))
            out.append(F(f".movHalfStore {high} {pd} {RDI} .xmm0",
                         pfx + [0x0F, lo_opc + 1, 0x07], "store",
                         f"{mn}{suf} QWORD PTR [rdi], xmm0", offsets=ANY))
    for k, code, mn in (("ps", [0x0F, 0x2B], "movntps"), ("pd", [0x66, 0x0F, 0x2B], "movntpd"),
                        ("dq", [0x66, 0x0F, 0xE7], "movntdq")):
        out.append(F(f".storeNT .{k} {RDI} .xmm0", code + [0x07], "store",
                     f"{mn} XMMWORD PTR [rdi], xmm0", offsets=ALIGNED))
    out.append(F(".maskmovdqu .xmm0 .xmm1", [0x66, 0x0F, 0xF7, 0xC1], "store",
                 "maskmovdqu xmm0, xmm1", offsets=ANY))
    for p, pfx, suf, w in PREC:
        for op, opc in ARITH:
            out.append(F(f".arithp .{op} .{p} .xmm0 (.reg .xmm1)", pfx + [0x0F, opc, 0xC1], "bin",
                         f"{op}{suf} xmm0, xmm1", lanes=w))
            out.append(F(f".arithp .{op} .{p} .xmm0 {SRC_MEM}", pfx + [0x0F, opc, 0x07],
                         "binmem", f"{op}{suf} xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED,
                         lanes=w))
        out.append(F(f".sqrtp .{p} .xmm0 (.reg .xmm1)", pfx + [0x0F, 0x51, 0xC1], "bin",
                     f"sqrt{suf} xmm0, xmm1"))
        out.append(F(f".sqrtp .{p} .xmm0 {SRC_MEM}", pfx + [0x0F, 0x51, 0x07], "binmem",
                     f"sqrt{suf} xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED))
        for n, pred in enumerate(CMP):
            out.append(F(f".cmpp .{p} .{pred} .xmm0 (.reg .xmm1)", pfx + [0x0F, 0xC2, 0xC1, n],
                         "bin", f"cmp{suf} xmm0, xmm1, {n}", imm=n, lanes=w))
        out.append(F(f".cmpp .{p} .lt .xmm0 {SRC_MEM}", pfx + [0x0F, 0xC2, 0x07, 1], "binmem",
                     f"cmp{suf} xmm0, XMMWORD PTR [rdi], 1", imm=1, offsets=ALIGNED, lanes=w))
        for high, opc, mn in (("false", 0x14, "unpckl"), ("true", 0x15, "unpckh")):
            out.append(F(f".unpckp {high} .{p} .xmm0 (.reg .xmm1)", pfx + [0x0F, opc, 0xC1],
                         "bin", f"{mn}{suf} xmm0, xmm1"))
            out.append(F(f".unpckp {high} .{p} .xmm0 {SRC_MEM}", pfx + [0x0F, opc, 0x07],
                         "binmem", f"{mn}{suf} xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED))
        for imm in IMMS:
            out.append(F(f".shufp .{p} .xmm0 (.reg .xmm1) {imm}", pfx + [0x0F, 0xC6, 0xC1, imm],
                         "bin", f"shuf{suf} xmm0, xmm1, {imm}", imm=imm))
        out.append(F(f".shufp .{p} .xmm0 {SRC_MEM} 27", pfx + [0x0F, 0xC6, 0x07, 27], "binmem",
                     f"shuf{suf} xmm0, XMMWORD PTR [rdi], 27", imm=27, offsets=ALIGNED))
    for k, pfx, opc, mn in CVT:
        out.append(F(f".cvtp .{k} .xmm0 (.reg .xmm1)", pfx + [0x0F, opc, 0xC1], "bin",
                     f"{mn} xmm0, xmm1"))
        if k in CVT_HALF:
            out.append(F(f".cvtp .{k} .xmm0 {SRC_MEM}", pfx + [0x0F, opc, 0x07], "load",
                         f"{mn} xmm0, QWORD PTR [rdi]", offsets=ANY))
        else:
            out.append(F(f".cvtp .{k} .xmm0 {SRC_MEM}", pfx + [0x0F, opc, 0x07], "binmem",
                         f"{mn} xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED))
    for k, b in (("lfence", 0xE8), ("mfence", 0xF0), ("sfence", 0xF8)):
        out.append(F(f".fence .{k}", [0x0F, 0xAE, b], "bin", k))
    for n, h in enumerate(("nta", "t0", "t1", "t2")):
        out.append(F(f".prefetch .{h} {RDI}", [0x0F, 0x18, 0x07 | n << 3], "load",
                     f"prefetch{h} BYTE PTR [rdi]", offsets=ANY))
    return out


def encoding_cases(fs):
    """Every harness form as GNU as assembles it, plus REX and RIP-relative variants."""
    out = [(f.lean, f.text) for f in fs]
    variants = [
        (".pint .pmaddwd .xmm9 (.reg .xmm13)", "pmaddwd xmm9, xmm13"),
        (".pint .packuswb .xmm15 (.mem (.mem { base := .r13, disp := 0x10 }))",
         "packuswb xmm15, XMMWORD PTR [r13+0x10]"),
        (".pint .pcmpgtd .xmm1 (.mem (.rip 0x100))", "pcmpgtd xmm1, XMMWORD PTR [rip+0x100]"),
        (".load .dqa .xmm8 (.rip 0xFFFFFF00)", "movdqa xmm8, XMMWORD PTR [rip-0x100]"),
        (".store .ups (.rip 0x40) .xmm3", "movups XMMWORD PTR [rip+0x40], xmm3"),
        (".arithp .mul .double .xmm10 (.mem (.mem { base := .rsp, disp := 0x20 }))",
         "mulpd xmm10, XMMWORD PTR [rsp+0x20]"),
        (".cmpp .single .nle .xmm2 (.reg .xmm11) ", "cmpps xmm2, xmm11, 6"),
        (".shufp .single .xmm14 (.reg .xmm6) 177", "shufps xmm14, xmm6, 177"),
        (".cvtp .tpd2dq .xmm7 (.reg .xmm8)", "cvttpd2dq xmm7, xmm8"),
        (".movmsk .pd .r9 .xmm13", "movmskpd r9d, xmm13"),
        (".movHalfLoad true true .xmm12 (.mem { base := .rax, index := some (⟨.rcx, by decide⟩, .s8), disp := 0x100 })",
         "movhpd xmm12, QWORD PTR [rax+rcx*8+0x100]"),
        (".storeNT .dq (.mem { base := .r8 }) .xmm9", "movntdq XMMWORD PTR [r8], xmm9"),
        (".logicRip .xor .single .xmm0 0x200", "xorps xmm0, XMMWORD PTR [rip+0x200]"),
        (".logicRip .and .double .xmm11 0x10", "andpd xmm11, XMMWORD PTR [rip+0x10]"),
        (".prefetch .t0 (.rip 0x80)", "prefetcht0 BYTE PTR [rip+0x80]"),
        (".pshuf .d .xmm9 (.mem (.rip 0x30)) 78", "pshufd xmm9, XMMWORD PTR [rip+0x30], 78"),
        (".approx .rsqrtps .xmm1 (.reg .xmm2)", "rsqrtps xmm1, xmm2"),
        (".approx .rcpss .xmm4 (.reg .xmm5)", "rcpss xmm4, xmm5"),
    ]
    return out + variants


HEADER = """-- Generated by scripts/x86-features/gen_sse_packed_vectors.py; do not edit.
module

public import Silmaril.X86.Features.Ext.SseMerged.Vectors
public meta import Silmaril.X86.Features.Ext.SseMerged.Vectors

/-! Native differential vectors of the forms only the SsePacked lane has (see
the generator). `form n` is harness case `n`; each line of `vectors` is
`case ymm0 ymm1 rax offset buffer ymm0' rax' buffer'` in hex, checked by
`SseMerged.Vectors.checkPacked`. `encodings` pairs forms with the bytes GNU
as assembles for them. -/

@[expose] public section

namespace Silmaril.X86.Features.SseMerged.PackedVectors

open Silmaril.X86.Features.SseMerged.Vectors (checkPacked)

"""


def write(fs, sem, enc):
    lines = [HEADER]
    lines.append("/-- The instruction of each harness case. -/")
    lines.append("def form : Nat → SsePacked.Instr")
    for i, f in enumerate(fs):
        lines.append(f"  | {i} => {f.lean}")
    lines.append("  | _ => .fence .lfence")
    lines.append("")
    lines.append("def checkLine : List Nat → Bool")
    lines.append("  | [n, a, b, rax, off, mem, ra, rax', mem'] => "
                 "checkPacked (form n) a b rax off mem ra rax' mem'")
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
    lines.append("def encodings : List (SsePacked.Instr × List X86.Byte) := [")
    for k, (lean, bs) in enumerate(enc):
        sep = "," if k + 1 < len(enc) else ""
        lines.append(f"  ({lean}, [{', '.join(f'0x{b:02X}' for b in bs)}]){sep}")
    lines.append("]")
    lines.append("")
    lines.append(f"#guard encodings.length = {len(enc)}")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => SsePacked.encode i == bs")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => SsePacked.decode bs == some (i, bs.length)")
    lines.append("")
    lines.append("end Silmaril.X86.Features.SseMerged.PackedVectors")
    with open(OUT, "w") as fh:
        fh.write("\n".join(lines) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu")
    ap.add_argument("--seed", type=int, default=2026)
    args = ap.parse_args()
    fs = forms()
    cases = encoding_cases(fs)
    enc = g.encoding_vectors(cases)
    for f, (_, bs) in zip(fs, enc):
        assert list(bs) == f.code, (f.lean, f.code, list(bs))
    sem = g.semantic_vectors(fs, args.qemu, args.seed)
    write(fs, sem, enc)
    print(f"{len(fs)} forms, {len(sem)} vectors, {len(enc)} encodings -> {OUT}", file=sys.stderr)


if __name__ == "__main__":
    main()
