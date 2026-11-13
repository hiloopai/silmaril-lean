#!/usr/bin/env python3
"""Generate the native differential vectors of the SSE3/SSSE3/SSE4 lane.

Every form of `Silmaril/X86/Features/Ext/Sse4` that `Sse4.exec` models
(everything except the floating-point ADDSUB/HADD/HSUB/ROUND/DPPS/DPPD forms
and the string compares, which are `unmodeled`) is run on the host CPU with
the harness of `gen_sse2_vectors.py`. That harness loads YMM0, YMM1, RAX and
RDI (a pointer into a 32-byte buffer), executes the raw bytes, and records
YMM0, RAX and the buffer. Lean checks `sse4Ext.exec` against these records
(`Sse4Vectors.checkLine`). PTEST writes only flags, which the harness does not
record, so its vectors check only that nothing else changes. Register sources
are XMM1 or RAX, because the value of RDI is a host address.

Every form whose text GNU as can express is assembled, and the harness bytes
are checked against the result. The encoding vectors add REX, SIB, `fs:` and
RIP-relative variants for `Sse4.encode`/`decoder`.

Usage: gen_sse4_vectors.py [--qemu PATH] [--seed N]
Writes Silmaril/X86/Features/Ext/Sse4/Vectors.lean.
"""

import argparse
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_sse2_vectors as g  # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Features", "Ext", "Sse4", "Vectors.lean")

ALIGNED = (0, 16)
ANY = tuple(range(0, 17))

# (Op2, prefix, map bytes, opcode, mnemonic, memory width, lanes)
OP2 = [
    ("movddup", 0xF2, [], 0x12, "movddup", 64, None),
    ("movsldup", 0xF3, [], 0x12, "movsldup", 128, None),
    ("movshdup", 0xF3, [], 0x16, "movshdup", 128, None),
    ("pshufb", 0x66, [0x38], 0x00, "pshufb", 128, None),
    ("phaddw", 0x66, [0x38], 0x01, "phaddw", 128, None),
    ("phaddd", 0x66, [0x38], 0x02, "phaddd", 128, None),
    ("phaddsw", 0x66, [0x38], 0x03, "phaddsw", 128, None),
    ("pmaddubsw", 0x66, [0x38], 0x04, "pmaddubsw", 128, None),
    ("phsubw", 0x66, [0x38], 0x05, "phsubw", 128, None),
    ("phsubd", 0x66, [0x38], 0x06, "phsubd", 128, None),
    ("phsubsw", 0x66, [0x38], 0x07, "phsubsw", 128, None),
    ("psignb", 0x66, [0x38], 0x08, "psignb", 128, 8),
    ("psignw", 0x66, [0x38], 0x09, "psignw", 128, 16),
    ("psignd", 0x66, [0x38], 0x0A, "psignd", 128, 32),
    ("pmulhrsw", 0x66, [0x38], 0x0B, "pmulhrsw", 128, None),
    ("pblendvb", 0x66, [0x38], 0x10, "pblendvb", 128, None),
    ("blendvps", 0x66, [0x38], 0x14, "blendvps", 128, None),
    ("blendvpd", 0x66, [0x38], 0x15, "blendvpd", 128, None),
    ("ptest", 0x66, [0x38], 0x17, "ptest", 128, None),
    ("pabsb", 0x66, [0x38], 0x1C, "pabsb", 128, None),
    ("pabsw", 0x66, [0x38], 0x1D, "pabsw", 128, None),
    ("pabsd", 0x66, [0x38], 0x1E, "pabsd", 128, None),
    ("pmovsxbw", 0x66, [0x38], 0x20, "pmovsxbw", 64, None),
    ("pmovsxbd", 0x66, [0x38], 0x21, "pmovsxbd", 32, None),
    ("pmovsxbq", 0x66, [0x38], 0x22, "pmovsxbq", 16, None),
    ("pmovsxwd", 0x66, [0x38], 0x23, "pmovsxwd", 64, None),
    ("pmovsxwq", 0x66, [0x38], 0x24, "pmovsxwq", 32, None),
    ("pmovsxdq", 0x66, [0x38], 0x25, "pmovsxdq", 64, None),
    ("pmuldq", 0x66, [0x38], 0x28, "pmuldq", 128, None),
    ("pcmpeqq", 0x66, [0x38], 0x29, "pcmpeqq", 128, 64),
    ("packusdw", 0x66, [0x38], 0x2B, "packusdw", 128, None),
    ("pmovzxbw", 0x66, [0x38], 0x30, "pmovzxbw", 64, None),
    ("pmovzxbd", 0x66, [0x38], 0x31, "pmovzxbd", 32, None),
    ("pmovzxbq", 0x66, [0x38], 0x32, "pmovzxbq", 16, None),
    ("pmovzxwd", 0x66, [0x38], 0x33, "pmovzxwd", 64, None),
    ("pmovzxwq", 0x66, [0x38], 0x34, "pmovzxwq", 32, None),
    ("pmovzxdq", 0x66, [0x38], 0x35, "pmovzxdq", 64, None),
    ("pcmpgtq", 0x66, [0x38], 0x37, "pcmpgtq", 128, 64),
    ("pminsb", 0x66, [0x38], 0x38, "pminsb", 128, 8),
    ("pminsd", 0x66, [0x38], 0x39, "pminsd", 128, 32),
    ("pminuw", 0x66, [0x38], 0x3A, "pminuw", 128, 16),
    ("pminud", 0x66, [0x38], 0x3B, "pminud", 128, 32),
    ("pmaxsb", 0x66, [0x38], 0x3C, "pmaxsb", 128, 8),
    ("pmaxsd", 0x66, [0x38], 0x3D, "pmaxsd", 128, 32),
    ("pmaxuw", 0x66, [0x38], 0x3E, "pmaxuw", 128, 16),
    ("pmaxud", 0x66, [0x38], 0x3F, "pmaxud", 128, 32),
    ("pmulld", 0x66, [0x38], 0x40, "pmulld", 128, None),
    ("phminposuw", 0x66, [0x38], 0x41, "phminposuw", 128, 16),
]

PTR = {8: "BYTE", 16: "WORD", 32: "DWORD", 64: "QWORD", 128: "XMMWORD"}

# (OpI, opcode, mnemonic)
OPI = [("palignr", 0x0F, "palignr"), ("blendps", 0x0C, "blendps"), ("blendpd", 0x0D, "blendpd"),
       ("pblendw", 0x0E, "pblendw"), ("insertps", 0x21, "insertps"), ("mpsadbw", 0x42, "mpsadbw")]
IMMS = [0x00, 0x01, 0x05, 0x0F, 0x10, 0x1B, 0x1F, 0x20, 0x4E, 0x8D, 0xB1, 0xFF]

# (ExtrOp, opcode, REX.W, mnemonic, width, GNU as register text)
EXTR = [("pextrb", 0x14, False, "pextrb", 8, "eax"), ("pextrw", 0x15, False, "pextrw", 16, None),
        ("pextrd", 0x16, False, "pextrd", 32, "eax"), ("pextrq", 0x16, True, "pextrq", 64, "rax"),
        ("extractps", 0x17, False, "extractps", 32, "eax")]
# (InsOp, opcode, REX.W, mnemonic, width, register text)
INS = [("pinsrb", 0x20, False, "pinsrb", 8, "eax"), ("pinsrd", 0x22, False, "pinsrd", 32, "eax"),
       ("pinsrq", 0x22, True, "pinsrq", 64, "rax")]
# (CrcSz, REX.W, opcode, register text, source register text, width)
CRC = [("b", False, 0xF0, "eax", "al", 8), ("bq", True, 0xF0, "rax", "al", 8),
       ("d", False, 0xF1, "eax", "eax", 32), ("q", True, 0xF1, "rax", "rax", 64)]

M = "(.mem M)"


class F(g.Form):
    def __init__(self, lean, code, kind, text, imm=0, offsets=(0,), lanes=None):
        super().__init__(lean, code, kind, imm=imm, offsets=offsets, lanes=lanes)
        self.text = text


def forms():
    out = []
    for op, pfx, mp, opc, mn, w, lanes in OP2:
        head = [pfx, 0x0F] + mp + [opc]
        out.append(F(f".rr .{op} .xmm0 (.reg .xmm1)", head + [0xC1], "bin", f"{mn} xmm0, xmm1",
                     lanes=lanes))
        kind = "binmem" if w == 128 else "load"
        offs = ALIGNED if w == 128 else ANY
        out.append(F(f".rr .{op} .xmm0 {M}", head + [0x07], kind,
                     f"{mn} xmm0, {PTR[w]} PTR [rdi]", offsets=offs, lanes=lanes))
    out.append(F(f".rr .lddqu .xmm0 {M}", [0xF2, 0x0F, 0xF0, 0x07], "load",
                 "lddqu xmm0, XMMWORD PTR [rdi]", offsets=ANY))
    out.append(F(f".rr .movntdqa .xmm0 {M}", [0x66, 0x0F, 0x38, 0x2A, 0x07], "load",
                 "movntdqa xmm0, XMMWORD PTR [rdi]", offsets=ALIGNED))
    for op, opc, mn in OPI:
        for imm in IMMS:
            out.append(F(f".ri .{op} .xmm0 (.reg .xmm1) {imm}", [0x66, 0x0F, 0x3A, opc, 0xC1, imm],
                         "bin", f"{mn} xmm0, xmm1, {imm}", imm=imm))
        w = 32 if op == "insertps" else 128
        out.append(F(f".ri .{op} .xmm0 {M} 27", [0x66, 0x0F, 0x3A, opc, 0x07, 27],
                     "binmem" if w == 128 else "load", f"{mn} xmm0, {PTR[w]} PTR [rdi], 27",
                     imm=27, offsets=ALIGNED if w == 128 else ANY))
    for op, opc, wbit, mn, w, reg in EXTR:
        rex = [0x48] if wbit else []
        for imm in (0, 1, 3, 5, 7, 9, 15, 255):
            out.append(F(f".extr .{op} (.reg .rax) .xmm1 {imm}",
                         [0x66] + rex + [0x0F, 0x3A, opc, 0xC8, imm], "bin",
                         f"{mn} {reg}, xmm1, {imm}" if reg else None, imm=imm))
        out.append(F(f".extr .{op} {M} .xmm1 6", [0x66] + rex + [0x0F, 0x3A, opc, 0x0F, 6],
                     "store", f"{mn} {PTR[w]} PTR [rdi], xmm1, 6", imm=6, offsets=ANY))
    for op, opc, wbit, mn, w, reg in INS:
        rex = [0x48] if wbit else []
        for imm in (0, 1, 3, 7, 9, 15, 255):
            out.append(F(f".ins .{op} .xmm0 (.reg .rax) {imm}",
                         [0x66] + rex + [0x0F, 0x3A, opc, 0xC0, imm], "bin",
                         f"{mn} xmm0, {reg}, {imm}", imm=imm))
        out.append(F(f".ins .{op} .xmm0 {M} 5", [0x66] + rex + [0x0F, 0x3A, opc, 0x07, 5],
                     "load", f"{mn} xmm0, {PTR[w]} PTR [rdi], 5", imm=5, offsets=ANY))
    for sz, wbit, opc, reg, sreg, w in CRC:
        rex = [0x48] if wbit else []
        out.append(F(f".crc32 .{sz} .rax (.reg .rax)", [0xF2] + rex + [0x0F, 0x38, opc, 0xC0],
                     "bin", f"crc32 {reg}, {sreg}"))
        out.append(F(f".crc32 .{sz} .rax {M}", [0xF2] + rex + [0x0F, 0x38, opc, 0x07], "load",
                     f"crc32 {reg}, {PTR[w]} PTR [rdi]", offsets=ANY))
    return out


def encoding_cases(fs):
    out = [(f.lean, f.text) for f in fs if f.text]
    out += [
        (".rr .pshufb .xmm9 (.reg .xmm13)", "pshufb xmm9, xmm13"),
        (".rr .pmaddubsw .xmm15 (.mem (Ext.Mem.ofReg .r13 none 0x10))",
         "pmaddubsw xmm15, XMMWORD PTR [r13+0x10]"),
        (".rr .pmovzxbw .xmm2 (.mem (Ext.Mem.ofRip 0x100))", "pmovzxbw xmm2, QWORD PTR [rip+0x100]"),
        (".rr .pcmpgtq .xmm3 (.mem (Ext.Mem.ofReg .rsp none 0x20))",
         "pcmpgtq xmm3, XMMWORD PTR [rsp+0x20]"),
        (".ri .palignr .xmm8 (.reg .xmm2) 8", "palignr xmm8, xmm2, 8"),
        (".ri .pcmpistri .xmm1 (.reg .xmm2) 12", "pcmpistri xmm1, xmm2, 12"),
        (".ri .pcmpestri64 .xmm1 (.reg .xmm2) 12", "pcmpestriq xmm1, xmm2, 12"),
        (".ri .roundps .xmm4 (.reg .xmm5) 1", "roundps xmm4, xmm5, 1"),
        (".ri .dpps .xmm6 (.mem (Ext.Mem.ofRip 0x40)) 0xF1", "dpps xmm6, XMMWORD PTR [rip+0x40], 0xF1"),
        (".rr .haddps .xmm1 (.reg .xmm2)", "haddps xmm1, xmm2"),
        (".rr .addsubpd .xmm1 (.reg .xmm2)", "addsubpd xmm1, xmm2"),
        (".extr .pextrd (.reg .r9) .xmm12 2", "pextrd r9d, xmm12, 2"),
        (".extr .pextrq (.mem (Ext.Mem.ofReg .r8 none 0)) .xmm9 1", "pextrq QWORD PTR [r8], xmm9, 1"),
        (".ins .pinsrb .xmm10 (.reg .rsi) 3", "pinsrb xmm10, esi, 3"),
        (".ins .pinsrq .xmm1 (.reg .r15) 1", "pinsrq xmm1, r15, 1"),
        (".crc32 .q .r8 (.reg .r9)", "crc32 r8, r9"),
        (".crc32 .b .rcx (.reg .rsi)", "crc32 ecx, sil"),
        (".crc32 .d .rax (.mem (Ext.Mem.fsAt 0x28))", "crc32 eax, DWORD PTR fs:0x28"),
    ]
    return out


HEADER = """-- Generated by scripts/x86-features/gen_sse4_vectors.py; do not edit.
module

public import Silmaril.X86.Features.Ext.Sse4.Extension
public import Silmaril.X86.Features.Ext.Sse2.Checks
public meta import Silmaril.X86.Features.Ext.Sse4.Extension
public meta import Silmaril.X86.Features.Ext.Sse2.Checks

/-! Native differential vectors of the SSE3/SSSE3/SSE4 lane (see the generator).
`form n` is harness case `n`; each line of `vectors` is
`case ymm0 ymm1 rax offset buffer ymm0' rax' buffer'` in hex, checked by
`checkVector` with `sse4Ext.exec`, using the vector state of `Sse2.Checks`.
`encodings` pairs forms with the bytes GNU as assembles for them. -/

@[expose] public section

namespace Silmaril.X86.Features.Sse4.Vectors

open Silmaril.X86.Features.Sse2.Checks (vstate vmemory vbase upperTag bytesOf)

/-- `[rdi]`. -/
def M : Ext.Mem := Ext.Mem.ofReg .rdi none 0

/-- Execute `i` on the vector's inputs and compare with the recorded outputs. -/
def checkVector (i : Instr) (a b rax off mem ra rax' mem' : Nat) : Bool :=
  match sse4Ext.exec i 6 (vstate a b rax (vbase + off)) (vmemory mem) with
  | .retired s m =>
    s.zmm 0 == BitVec.ofNat 512 (upperTag + ra) && s.zmm 1 == BitVec.ofNat 512 b &&
      s.core.read .rax == BitVec.ofNat 64 rax' && s.core.read .rdi == BitVec.ofNat 64 (vbase + off) &&
      s.rip == 0x1006 && m.readBytes vbase 32 == some (bytesOf mem' 32)
  | _ => false

"""


def write(fs, sem, enc):
    lines = [HEADER]
    lines.append("/-- The instruction of each harness case. -/")
    lines.append("def form : Nat → Instr")
    for i, f in enumerate(fs):
        lines.append(f"  | {i} => {f.lean}")
    lines.append("  | _ => .rr .pshufb .xmm0 (.reg .xmm1)")
    lines.append("")
    lines.append("def checkLine : List Nat → Bool")
    lines.append("  | [n, a, b, rax, off, mem, ra, rax', mem'] => "
                 "checkVector (form n) a b rax off mem ra rax' mem'")
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
    lines.append("def encodings : List (Instr × List X86.Byte) := [")
    for k, (lean, bs) in enumerate(enc):
        sep = "," if k + 1 < len(enc) else ""
        lines.append(f"  ({lean}, [{', '.join(f'0x{b:02X}' for b in bs)}]){sep}")
    lines.append("]")
    lines.append("")
    lines.append(f"#guard encodings.length = {len(enc)}")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => encode i == bs")
    lines.append("")
    lines.append("#guard encodings.all fun (i, bs) => decoder.decode bs == some (i, bs.length)")
    lines.append("")
    lines.append("end Silmaril.X86.Features.Sse4.Vectors")
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
    by_lean = dict(enc)
    for f in fs:
        if f.text:
            assert by_lean[f.lean] == f.code, (f.lean, f.code, by_lean[f.lean])
    sem = g.semantic_vectors(fs, args.qemu, args.seed)
    write(fs, sem, enc)
    print(f"{len(fs)} forms, {len(sem)} vectors, {len(enc)} encodings -> {OUT}", file=sys.stderr)


if __name__ == "__main__":
    main()
