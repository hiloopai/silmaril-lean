#!/usr/bin/env python3
"""Generate the native differential vectors of the `avx` lane.

For every form the Lean semantics models (`MODELED`, mirroring
`Silmaril/X86/Features/Ext/Avx/Semantics.lean`) and every vector length the
form exists at, the script writes test functions that load YMM0-YMM15 from an
input block, execute the instruction once (assembled by GNU as from Intel
syntax, register and `[rsi + disp]` memory operands), and store YMM0-YMM15 and
the 64-byte memory buffer and MXCSR back (floating-point forms run with random
operands, including NaNs, infinities and denormals, every rounding mode, DAZ
and FZ, exceptions masked). A C driver runs them on the host (the oracle:
the CPU itself, which must have AVX2) and prints the instruction bytes, read
from the code, and the results.

Each vector line has hexadecimal fields:

    len b0 .. b(len-1) nin (reg value)*nin memIn nout (reg value)*nout memOut mxIn mxOut

`nin` registers differ from the fixed pattern `pattern(j)` the other inputs
hold, `nout` registers differ from their input after execution, and the
memory buffers are 64-byte little-endian values. Lean
(`Avx/Vectors.lean`, `Avx.checkLine`) decodes the bytes with the lane's
decoder, executes them through `ext.exec`, and checks every YMM register, that
bits 511:256 are zero (VEX zeroing on a state whose upper bits start at zero),
and the buffer.

Usage: gen_avx_vectors.py [--seed N] [--per N]
Writes Silmaril/X86/Features/Ext/Avx/Vectors.lean.
"""

import argparse
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "Silmaril", "X86", "Features", "Ext", "Avx", "Vectors.lean")
sys.path.insert(0, HERE)
import avx_ops  # noqa: E402

M64 = (1 << 64) - 1
M256 = (1 << 256) - 1


def pattern(j):
    q = (0x9E3779B97F4A7C15 * (j + 1)) & M64
    return q | (q << 64) | (q << 128) | (q << 192)


INT = """paddb paddw paddd paddq psubb psubw psubd psubq paddsb paddsw paddusb paddusw psubsb
psubsw psubusb psubusw pmullw pmulhw pmulhuw pmuludq pmuldq pmulld pmaddwd pmaddubsw pmulhrsw
pand andps andpd pandn andnps andnpd por orps orpd pxor xorps xorpd pcmpeqb pcmpeqw pcmpeqd
pcmpeqq pcmpgtb pcmpgtw pcmpgtd pcmpgtq pminub pminuw pminud pmaxub pmaxuw pmaxud pminsb pminsw
pminsd pmaxsb pmaxsw pmaxsd pavgb pavgw psadbw psignb psignw psignd packsswb packuswb packssdw
packusdw punpcklbw punpcklwd punpckldq unpcklps punpcklqdq unpcklpd punpckhbw punpckhwd
punpckhdq unpckhps punpckhqdq unpckhpd pshufb phaddw phaddd phaddsw phsubw phsubd phsubsw psrlw
psrld psrlq psraw psrad psllw pslld psllq psrlv psllv psrav permd permps permilpsV permilpdV
palignr pblendw pblendd blendps blendpd shufps shufpd perm2i128 perm2f128 inserti128 insertf128
pabsb pabsw pabsd pshufd permilpsI pshufhw pshuflw permilpdI permq permpd pmovsxbw pmovsxbd
pmovsxbq pmovsxwd pmovsxwq pmovsxdq pmovzxbw pmovzxbd pmovzxbq pmovzxwd pmovzxwq pmovzxdq
movdqa movdqu movaps movapd movups movupd movntdqa lddqu movsldup movshdup movddup pbroadcastb
pbroadcastw pbroadcastd pbroadcastq broadcastss broadcastsd broadcastf128 broadcasti128
psrlwI psrawI psllwI psrldI psradI pslldI psrlqI psllqI psrldq pslldq pblendvb blendvps
blendvpd movdqaSt movdquSt movapsSt movapdSt movupsSt movupdSt movntdq movntps movntpd
extracti128 extractf128 zeroupper zeroall"""
FP = """addps addpd addss addsd subps subpd subss subsd mulps mulpd mulss mulsd divps divpd divss
divsd minps minpd minss minsd maxps maxpd maxss maxsd sqrtps sqrtpd sqrtss sqrtsd"""
FPSET = set(FP.split())
MODELED = set(INT.split()) | FPSET

ALIGNED = {"movdqa", "movdqaSt", "movaps", "movapsSt", "movapd", "movapdSt", "movntdq",
           "movntps", "movntpd", "movntdqa"}

SIZE_PTR = {1: "BYTE", 2: "WORD", 4: "DWORD", 8: "QWORD", 16: "XMMWORD", 32: "YMMWORD"}


def mem_bytes(name, l, width):
    v = 32 if l else 16
    return {"v": v, "x": 16, "y": 32, "h": v // 2, "q4": v // 4, "q8": v // 8, "d": 4,
            "q": 8, "b": 1, "w": 2, "ddup": 32 if l else 8}[width]


def reg_name(width, l, n):
    if width in ("v", "ddup"):
        return ("ymm" if l else "xmm") + str(n)
    if width == "y":
        return "ymm" + str(n)
    return "xmm" + str(n)


def rand_elem(rng, w):
    edges = [0, 1, (1 << w) - 1, 1 << (w - 1), (1 << (w - 1)) - 1, (1 << (w - 1)) + 1, 2, 0x55]
    if rng.random() < 0.35:
        return rng.choice(edges) & ((1 << w) - 1)
    return rng.getrandbits(w)


def rand_vec(rng, kind=None):
    mode = rng.random()
    if kind == "count":
        # a shift count in the low quadword: small, at the width boundaries, or huge
        c = rng.choice([0, 1, 3, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 200,
                        rng.getrandbits(64)])
        return (rng.getrandbits(256) & ~M64) | c
    if kind == "counts":
        w = rng.choice([32, 64])
        v = 0
        for i in range(256 // w):
            v |= rng.choice([0, 1, 5, 15, 16, 31, 32, 33, 63, 64, 100, rng.getrandbits(w)]) << (i * w)
        return v
    if mode < 0.5:
        return rng.getrandbits(256)
    w = rng.choice([8, 16, 32, 64])
    v = 0
    for i in range(256 // w):
        v |= rand_elem(rng, w) << (i * w)
    return v


def rand_float(rng, w):
    """A binary32/binary64 value: specials, denormals, extremes or random."""
    e, m = (8, 23) if w == 32 else (11, 52)
    sign = rng.getrandbits(1) << (w - 1)
    emax = (1 << e) - 1
    pick = rng.random()
    if pick < 0.08:
        return sign                                    # zero
    if pick < 0.14:
        return sign | (emax << m)                      # infinity
    if pick < 0.20:
        return sign | (emax << m) | (1 << (m - 1)) | rng.getrandbits(m - 1)  # quiet NaN
    if pick < 0.24:
        return sign | (emax << m) | max(1, rng.getrandbits(m - 1))  # signalling NaN
    if pick < 0.32:
        return sign | rng.getrandbits(m)               # denormal
    if pick < 0.38:
        return sign | ((emax - 1) << m) | rng.getrandbits(m)  # huge
    if pick < 0.44:
        return sign | (1 << m) | rng.getrandbits(m)    # smallest normals
    if pick < 0.60:
        bias = (1 << (e - 1)) - 1
        return sign | ((bias + rng.randrange(-4, 5)) << m) | rng.getrandbits(m)
    return rng.getrandbits(w)


def rand_fvec(rng, w):
    v = 0
    for i in range(256 // w):
        v |= rand_float(rng, w) << (i * w)
    return v


def rand_mxcsr(rng):
    """Every exception masked, flags clear, any rounding mode, DAZ and FZ."""
    mx = 0x1F80 | (rng.getrandbits(2) << 13)
    if rng.random() < 0.3:
        mx |= 1 << 6
    if rng.random() < 0.3:
        mx |= 1 << 15
    return mx


def imm_for(name, rng):
    if name in ("psrlwI", "psrawI", "psllwI", "psrldI", "psradI", "pslldI", "psrlqI", "psllqI"):
        return rng.choice([0, 1, 3, 7, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255, rng.getrandbits(8)])
    if name in ("psrldq", "pslldq", "palignr"):
        return rng.choice([0, 1, 4, 8, 15, 16, 17, 31, 32, 33, rng.getrandbits(8)])
    return rng.getrandbits(8)


def forms(row):
    """(l, w) combinations of a row."""
    ls = [row["l"]] if row["l"] is not None else [0, 1]
    if row["name"] in ("psrlv", "psllv"):
        ws = [0, 1]
    else:
        ws = [row["w"] if row["w"] is not None else 0]
    return [(l, w) for l in ls for w in ws]


def mnemonic(row, w):
    if row["name"] in ("psrlv", "psllv"):
        return row["mnem"] + ("q" if w else "d")
    return row["mnem"]


def make_test(row, l, w, rng, use_mem):
    """One test: assembly text and the 16 input registers."""
    name = row["name"]
    toks = row["ops"].split()
    regs = list(range(16))
    rng.shuffle(regs)
    pick = iter(regs)
    operands = []
    involved = []
    srcs = {}
    imm = None
    is4 = None
    disp = 0
    mem = False
    for t in toks:
        role, width = t[0], t[1:]
        if role in "VHU":
            n = next(pick)
            operands.append(reg_name(width, l, n))
            involved.append(n)
            srcs[role] = n
        elif role in "WM":
            if role == "M" or (use_mem and row["kind"] != "reg"):
                k = mem_bytes(name, l, width)
                if name in ALIGNED:
                    disp = rng.choice(range(0, 64 - k + 1, k))
                else:
                    disp = rng.randrange(0, 64 - k + 1)
                operands.append("%s PTR [rsi%s]" % (SIZE_PTR[k], "+%d" % disp if disp else ""))
                mem = True
            else:
                n = next(pick)
                operands.append(reg_name(width, l, n))
                involved.append(n)
                srcs["W"] = n
        elif role == "L":
            n = next(pick)
            operands.append(reg_name(width, l, n))
            involved.append(n)
            is4 = n
        elif role == "I":
            imm = imm_for(name, rng)
            operands.append(str(imm))
    text = mnemonic(row, w) + (" " + ", ".join(operands) if operands else "")
    inputs = [pattern(j) for j in range(16)]
    count_src = name in ("psrlw", "psrld", "psrlq", "psraw", "psrad", "psllw", "pslld", "psllq")
    var_src = name in ("psrlv", "psllv", "psrav")
    for n in involved:
        kind = None
        if count_src and n == srcs.get("W"):
            kind = "count"
        if var_src and n == srcs.get("W"):
            kind = "counts"
        inputs[n] = rand_vec(rng, kind)
    if name in ("zeroupper", "zeroall"):
        inputs = [rand_vec(rng) for _ in range(16)]
    buf = rng.getrandbits(512)
    mx = 0x1F80
    if name in FPSET:
        fw = 64 if name.endswith("d") else 32
        for n in involved:
            inputs[n] = rand_fvec(rng, fw)
        buf = rand_fvec(rng, fw) | (rand_fvec(rng, fw) << 256)
        mx = rand_mxcsr(rng)
    if count_src and mem:
        c = rng.choice([0, 1, 7, 15, 16, 31, 32, 63, 64, 200])
        buf = (buf & ~(M64 << (8 * disp))) | (c << (8 * disp))
    return text, inputs, buf, mx


ASM_HEAD = """\t.intel_syntax noprefix
\t.text
"""


def asm_test(i, text):
    lines = ["\t.globl t%d" % i, "t%d:" % i, "\tldmxcsr DWORD PTR [rcx]"]
    for j in range(16):
        lines.append("\tvmovdqu ymm%d, YMMWORD PTR [rdi+%d]" % (j, 32 * j))
    lines += ["\t.globl ins%d" % i, "ins%d:" % i, "\t" + text, "\t.globl ins%d_end" % i,
              "ins%d_end:" % i]
    for j in range(16):
        lines.append("\tvmovdqu YMMWORD PTR [rdx+%d], ymm%d" % (32 * j, j))
    lines += ["\tstmxcsr DWORD PTR [rcx+4]", "\tldmxcsr DWORD PTR [rcx+8]", "\tvzeroupper",
              "\tret"]
    return "\n".join(lines) + "\n"


def le_words(v, nbytes):
    return ", ".join("0x%02x" % ((v >> (8 * k)) & 0xFF) for k in range(nbytes))


def c_driver(tests):
    out = ["#include <stdio.h>", "#include <string.h>", "#include <stdint.h>",
           "typedef void (*fn)(const uint8_t *, uint8_t *, uint8_t *, uint32_t *);"]
    for i in range(len(tests)):
        out.append("extern void t%d(const uint8_t *, uint8_t *, uint8_t *, uint32_t *);" % i)
        out.append("extern const uint8_t ins%d[], ins%d_end[];" % (i, i))
    out.append("static const uint8_t inputs[%d][512] = {" % len(tests))
    for t in tests:
        out.append("{" + ", ".join(le_words(v, 32) for v in t[1]) + "},")
    out.append("};")
    out.append("static const uint8_t bufs[%d][64] = {" % len(tests))
    for t in tests:
        out.append("{" + le_words(t[2], 64) + "},")
    out.append("};")
    out.append("static const uint32_t mxs[%d] = {" % len(tests) +
               ", ".join("0x%x" % t[3] for t in tests) + "};")
    out.append("static fn fns[] = {" + ", ".join("t%d" % i for i in range(len(tests))) + "};")
    out.append("static const uint8_t *starts[] = {" +
               ", ".join("ins%d" % i for i in range(len(tests))) + "};")
    out.append("static const uint8_t *ends[] = {" +
               ", ".join("ins%d_end" % i for i in range(len(tests))) + "};")
    out.append("""
static void hex(const uint8_t *p, int n) {
  int k = n - 1; while (k > 0 && p[k] == 0) k--;
  printf(" ");
  for (; k >= 0; k--) printf("%02x", p[k]);
}
int main(void) {
  static uint8_t buf[64] __attribute__((aligned(64)));
  uint8_t out[512];
  uint32_t mx[3];
  for (unsigned i = 0; i < sizeof fns / sizeof fns[0]; i++) {
    memcpy(buf, bufs[i], 64);
    mx[0] = mxs[i]; mx[1] = 0; mx[2] = 0x1F80;
    fns[i](inputs[i], buf, out, mx);
    int len = (int)(ends[i] - starts[i]);
    printf("%x", len);
    for (int k = 0; k < len; k++) printf(" %x", starts[i][k]);
    printf(" |");
    for (int j = 0; j < 16; j++) hex(out + 32 * j, 32);
    hex(buf, 64);
    printf(" %x\\n", mx[1]);
  }
  return 0;
}
""")
    return "\n".join(out)


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw).stdout


HEADER = """-- Generated by scripts/x86-features/gen_avx_vectors.py; do not edit.
module

public import Silmaril.X86.Features.Ext.Avx.Check
public meta import Silmaril.X86.Features.Ext.Avx.Check

/-!
# Native differential vectors of the `avx` lane

%d vectors over %d (form, VEX.L, VEX.W) combinations, executed natively on the
host (%s): the instruction bytes come from GNU as and the expected registers
and memory from the CPU. `checkLine` decodes the bytes with `byteDecoder`,
executes them with `ext.exec` and compares all sixteen YMM registers, bits
511:256 (zero) and the 64-byte buffer at `rsi`.
-/

namespace Silmaril.X86.Features.Avx.Vectors

"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--per", type=int, default=6)
    ap.add_argument("--listing", help="also write the assembly text of each vector, one per line")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    tests = []
    combos = 0
    for row in avx_ops.ROWS:
        if row["name"] not in MODELED:
            continue
        for l, w in forms(row):
            combos += 1
            for k in range(args.per):
                use_mem = k % 3 == 2
                tests.append(make_test(row, l, w, rng, use_mem))
    with tempfile.TemporaryDirectory() as tmp:
        s = os.path.join(tmp, "t.s")
        c = os.path.join(tmp, "d.c")
        exe = os.path.join(tmp, "d")
        with open(s, "w") as f:
            f.write(ASM_HEAD + "".join(asm_test(i, t[0]) for i, t in enumerate(tests)))
        with open(c, "w") as f:
            f.write(c_driver(tests))
        run(["gcc", "-O1", "-no-pie", "-o", exe, c, s])
        lines = run([exe]).splitlines()
    cpu = "unknown host"
    with open("/proc/cpuinfo") as f:
        for line in f:
            if line.startswith("model name"):
                cpu = line.split(":", 1)[1].strip()
                break
    vec = []
    for (text, inputs, buf, mx), line in zip(tests, lines):
        head, tail = line.split("|")
        code = head.split()
        res = [int(x, 16) for x in tail.split()]
        outs, mem_out, mx_out = res[:16], res[16], res[17]
        ins = [(j, v) for j, v in enumerate(inputs) if v != pattern(j)]
        chg = [(j, v) for j, v in enumerate(outs) if v != inputs[j]]
        fields = code + ["%x" % len(ins)]
        for j, v in ins:
            fields += ["%x" % j, "%x" % v]
        fields.append("%x" % buf)
        fields.append("%x" % len(chg))
        for j, v in chg:
            fields += ["%x" % j, "%x" % v]
        fields.append("%x" % mem_out)
        fields += ["%x" % mx, "%x" % mx_out]
        vec.append(" ".join(fields))
    chunks = [vec[i:i + 200] for i in range(0, len(vec), 200)]
    with open(OUT, "w") as f:
        f.write(HEADER % (len(vec), combos, cpu))
        for k, chunk in enumerate(chunks):
            f.write("/-- Vectors %d-%d. -/\npublic def v%d : String := \"\n" % (200 * k, 200 * k + len(chunk) - 1, k))
            f.write("\n".join(chunk))
            f.write("\n\"\n\n")
        for k in range(len(chunks)):
            f.write("#guard (hexFields v%d).all checkLine\n" % k)
        f.write("\nend Silmaril.X86.Features.Avx.Vectors\n")
    if args.listing:
        with open(args.listing, "w") as f:
            f.write("".join(t[0] + "\n" for t in tests))
    print("wrote %d vectors (%d combinations) to %s" % (len(vec), combos, OUT))


if __name__ == "__main__":
    main()
