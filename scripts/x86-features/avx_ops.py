#!/usr/bin/env python3
"""The VEX opcode table of the `avx` lane (AVX, AVX2, FMA3, F16C, VEX AES/PCLMUL, GFNI).

One row per `Op` constructor of `Silmaril/X86/Features/Ext/Avx/Ops.lean`, which
`gen_avx_ops.py` writes from this table. The fields are those of the SDM Vol. 2
opcode column `VEX.L.pp.map.W opcode /r`:

* `pp`: the implied mandatory prefix (`""`, `"66"`, `"F3"`, `"F2"`);
* `map`: 1 = `0F`, 2 = `0F38`, 3 = `0F3A`;
* `opc`: the opcode byte;
* `w`: `0`/`1` when VEX.W is fixed; `None` when it is ignored (WIG) or selects
  the form (the Lean semantics reads it);
* `l`: `0`/`1` when VEX.L is fixed (128- or 256-bit-only forms); `None` when it
  selects the vector length or is ignored (LIG);
* `digit`: the ModRM.reg opcode extension of `/digit` forms;
* `kind`: what ModRM.rm may be: `any`, `reg` (mod = 11 only), `mem` (memory
  only) or `none` (no ModRM byte: VZEROUPPER/VZEROALL);
* `vvvv`: whether VEX.vvvv names an operand (otherwise it must be 1111b);
* `feat`: the CPUID feature rule (`FeatClass` in `Ops.lean`);
* `ops`: the operands in Intel order, for the vector generator: `V`/`H`/`W`/`U`/
  `M`/`L` are the reg / vvvv / rm / rm-register / rm-memory / is4 vector
  operands, `G`/`E` the reg / rm general-purpose operands and `I` an imm8; the
  suffix is the width (`v` is xmm for VEX.L0 and ymm for VEX.L1).
"""

ROWS = []


def op(name, mnem, pp, mp, opc, w=None, l=None, digit=None, kind="any", vvvv=True,
       feat="int", ops="Vv Hv Wv"):
    ROWS.append(dict(name=name, mnem=mnem, pp=pp, map=mp, opc=opc, w=w, l=l, digit=digit,
                     kind=kind, vvvv=vvvv, feat=feat, ops=ops))


# ---------------------------------------------------------------- integer binary, 66 0F
for name, opc in [("paddb", 0xFC), ("paddw", 0xFD), ("paddd", 0xFE), ("paddq", 0xD4),
                  ("psubb", 0xF8), ("psubw", 0xF9), ("psubd", 0xFA), ("psubq", 0xFB),
                  ("paddsb", 0xEC), ("paddsw", 0xED), ("paddusb", 0xDC), ("paddusw", 0xDD),
                  ("psubsb", 0xE8), ("psubsw", 0xE9), ("psubusb", 0xD8), ("psubusw", 0xD9),
                  ("pmullw", 0xD5), ("pmulhw", 0xE5), ("pmulhuw", 0xE4), ("pmuludq", 0xF4),
                  ("pmaddwd", 0xF5), ("pand", 0xDB), ("pandn", 0xDF), ("por", 0xEB),
                  ("pxor", 0xEF), ("pcmpeqb", 0x74), ("pcmpeqw", 0x75), ("pcmpeqd", 0x76),
                  ("pcmpgtb", 0x64), ("pcmpgtw", 0x65), ("pcmpgtd", 0x66), ("pminub", 0xDA),
                  ("pmaxub", 0xDE), ("pminsw", 0xEA), ("pmaxsw", 0xEE), ("pavgb", 0xE0),
                  ("pavgw", 0xE3), ("psadbw", 0xF6), ("packsswb", 0x63), ("packuswb", 0x67),
                  ("packssdw", 0x6B), ("punpcklbw", 0x60), ("punpcklwd", 0x61),
                  ("punpckldq", 0x62), ("punpcklqdq", 0x6C), ("punpckhbw", 0x68),
                  ("punpckhwd", 0x69), ("punpckhdq", 0x6A), ("punpckhqdq", 0x6D)]:
    op(name, "v" + name, "66", 1, opc)

# ---------------------------------------------------------------- integer binary, 66 0F38
for name, opc in [("pshufb", 0x00), ("phaddw", 0x01), ("phaddd", 0x02), ("phaddsw", 0x03),
                  ("pmaddubsw", 0x04), ("phsubw", 0x05), ("phsubd", 0x06), ("phsubsw", 0x07),
                  ("psignb", 0x08), ("psignw", 0x09), ("psignd", 0x0A), ("pmulhrsw", 0x0B),
                  ("pmuldq", 0x28), ("pcmpeqq", 0x29), ("packusdw", 0x2B), ("pcmpgtq", 0x37),
                  ("pminsb", 0x38), ("pminsd", 0x39), ("pminuw", 0x3A), ("pminud", 0x3B),
                  ("pmaxsb", 0x3C), ("pmaxsd", 0x3D), ("pmaxuw", 0x3E), ("pmaxud", 0x3F),
                  ("pmulld", 0x40)]:
    op(name, "v" + name, "66", 2, opc)

# ---------------------------------------------------------------- with imm8 / is4
op("palignr", "vpalignr", "66", 3, 0x0F, ops="Vv Hv Wv I")
op("pblendw", "vpblendw", "66", 3, 0x0E, ops="Vv Hv Wv I")
op("pblendd", "vpblendd", "66", 3, 0x02, w=0, feat="avx2", ops="Vv Hv Wv I")
op("pblendvb", "vpblendvb", "66", 3, 0x4C, w=0, ops="Vv Hv Wv Lv")
op("pclmulqdq", "vpclmulqdq", "66", 3, 0x44, feat="clmul", ops="Vv Hv Wv I")
op("gf2p8affineqb", "vgf2p8affineqb", "66", 3, 0xCE, w=1, feat="gfni", ops="Vv Hv Wv I")
op("gf2p8affineinvqb", "vgf2p8affineinvqb", "66", 3, 0xCF, w=1, feat="gfni", ops="Vv Hv Wv I")
op("gf2p8mulb", "vgf2p8mulb", "66", 2, 0xCF, w=0, feat="gfni")

# ---------------------------------------------------------------- AES
op("aesenc", "vaesenc", "66", 2, 0xDC, feat="aes")
op("aesenclast", "vaesenclast", "66", 2, 0xDD, feat="aes")
op("aesdec", "vaesdec", "66", 2, 0xDE, feat="aes")
op("aesdeclast", "vaesdeclast", "66", 2, 0xDF, feat="aes")
op("aesimc", "vaesimc", "66", 2, 0xDB, l=0, vvvv=False, feat="aes", ops="Vx Wx")
op("aeskeygenassist", "vaeskeygenassist", "66", 3, 0xDF, l=0, vvvv=False, feat="aes",
   ops="Vx Wx I")

# ---------------------------------------------------------------- shifts
for name, opc in [("psrlw", 0xD1), ("psrld", 0xD2), ("psrlq", 0xD3), ("psraw", 0xE1),
                  ("psrad", 0xE2), ("psllw", 0xF1), ("pslld", 0xF2), ("psllq", 0xF3)]:
    op(name, "v" + name, "66", 1, opc, ops="Vv Hv Wx")
for name, opc, d in [("psrlwI", 0x71, 2), ("psrawI", 0x71, 4), ("psllwI", 0x71, 6),
                     ("psrldI", 0x72, 2), ("psradI", 0x72, 4), ("pslldI", 0x72, 6),
                     ("psrlqI", 0x73, 2), ("psrldq", 0x73, 3), ("psllqI", 0x73, 6),
                     ("pslldq", 0x73, 7)]:
    mn = "v" + (name[:-1] if name.endswith("I") else name)
    op(name, mn, "66", 1, opc, digit=d, kind="reg", ops="Hv Uv I")
op("psrlv", "vpsrlv", "66", 2, 0x45, feat="avx2")     # W0 d, W1 q
op("psrav", "vpsravd", "66", 2, 0x46, w=0, feat="avx2")
op("psllv", "vpsllv", "66", 2, 0x47, feat="avx2")     # W0 d, W1 q

# ---------------------------------------------------------------- integer unary
op("pshufd", "vpshufd", "66", 1, 0x70, vvvv=False, ops="Vv Wv I")
op("pshufhw", "vpshufhw", "F3", 1, 0x70, vvvv=False, ops="Vv Wv I")
op("pshuflw", "vpshuflw", "F2", 1, 0x70, vvvv=False, ops="Vv Wv I")
op("pabsb", "vpabsb", "66", 2, 0x1C, vvvv=False, ops="Vv Wv")
op("pabsw", "vpabsw", "66", 2, 0x1D, vvvv=False, ops="Vv Wv")
op("pabsd", "vpabsd", "66", 2, 0x1E, vvvv=False, ops="Vv Wv")
op("phminposuw", "vphminposuw", "66", 2, 0x41, l=0, vvvv=False, feat="avx", ops="Vx Wx")
for name, opc, ops in [("pmovsxbw", 0x20, "Vv Wh"), ("pmovsxbd", 0x21, "Vv Wq4"),
                       ("pmovsxbq", 0x22, "Vv Wq8"), ("pmovsxwd", 0x23, "Vv Wh"),
                       ("pmovsxwq", 0x24, "Vv Wq4"), ("pmovsxdq", 0x25, "Vv Wh"),
                       ("pmovzxbw", 0x30, "Vv Wh"), ("pmovzxbd", 0x31, "Vv Wq4"),
                       ("pmovzxbq", 0x32, "Vv Wq8"), ("pmovzxwd", 0x33, "Vv Wh"),
                       ("pmovzxwq", 0x34, "Vv Wq4"), ("pmovzxdq", 0x35, "Vv Wh")]:
    op(name, "v" + name, "66", 2, opc, vvvv=False, ops=ops)
op("ptest", "vptest", "66", 2, 0x17, vvvv=False, feat="avx", ops="Vv Wv")
op("testps", "vtestps", "66", 2, 0x0E, w=0, vvvv=False, feat="avx", ops="Vv Wv")
op("testpd", "vtestpd", "66", 2, 0x0F, w=0, vvvv=False, feat="avx", ops="Vv Wv")

# ---------------------------------------------------------------- moves
for name, pp, opc, st in [("movdqa", "66", 0x6F, False), ("movdqaSt", "66", 0x7F, True),
                          ("movdqu", "F3", 0x6F, False), ("movdquSt", "F3", 0x7F, True),
                          ("movaps", "", 0x28, False), ("movapsSt", "", 0x29, True),
                          ("movapd", "66", 0x28, False), ("movapdSt", "66", 0x29, True),
                          ("movups", "", 0x10, False), ("movupsSt", "", 0x11, True),
                          ("movupd", "66", 0x10, False), ("movupdSt", "66", 0x11, True)]:
    mn = "v" + (name[:-2] if st else name)
    op(name, mn, pp, 1, opc, vvvv=False, feat="avx", ops="Wv Vv" if st else "Vv Wv")
op("movntdq", "vmovntdq", "66", 1, 0xE7, kind="mem", vvvv=False, feat="avx", ops="Mv Vv")
op("movntps", "vmovntps", "", 1, 0x2B, kind="mem", vvvv=False, feat="avx", ops="Mv Vv")
op("movntpd", "vmovntpd", "66", 1, 0x2B, kind="mem", vvvv=False, feat="avx", ops="Mv Vv")
op("movntdqa", "vmovntdqa", "66", 2, 0x2A, kind="mem", vvvv=False, ops="Vv Mv")
op("lddqu", "vlddqu", "F2", 1, 0xF0, kind="mem", vvvv=False, feat="avx", ops="Vv Mv")
op("movsldup", "vmovsldup", "F3", 1, 0x12, vvvv=False, feat="avx", ops="Vv Wv")
op("movshdup", "vmovshdup", "F3", 1, 0x16, vvvv=False, feat="avx", ops="Vv Wv")
op("movddup", "vmovddup", "F2", 1, 0x12, vvvv=False, feat="avx", ops="Vv Wddup")
# MOVD/MOVQ (W selects 32/64)
op("movdToX", "vmov", "66", 1, 0x6E, l=0, vvvv=False, feat="avx", ops="Vx Ey")
op("movdFromX", "vmov", "66", 1, 0x7E, l=0, vvvv=False, feat="avx", ops="Ey Vx")
op("movqXX", "vmovq", "F3", 1, 0x7E, l=0, vvvv=False, feat="avx", ops="Vx Wq")
op("movqSt", "vmovq", "66", 1, 0xD6, l=0, vvvv=False, feat="avx", ops="Wq Vx")
# MOVSS/MOVSD (LIG)
op("movssLd", "vmovss", "F3", 1, 0x10, kind="mem", vvvv=False, feat="avx", ops="Vx Md")
op("movssRR", "vmovss", "F3", 1, 0x10, kind="reg", feat="avx", ops="Vx Hx Ux")
op("movssSt", "vmovss", "F3", 1, 0x11, kind="mem", vvvv=False, feat="avx", ops="Md Vx")
op("movssRR2", "vmovss", "F3", 1, 0x11, kind="reg", feat="avx", ops="Ux Hx Vx")
op("movsdLd", "vmovsd", "F2", 1, 0x10, kind="mem", vvvv=False, feat="avx", ops="Vx Mq")
op("movsdRR", "vmovsd", "F2", 1, 0x10, kind="reg", feat="avx", ops="Vx Hx Ux")
op("movsdSt", "vmovsd", "F2", 1, 0x11, kind="mem", vvvv=False, feat="avx", ops="Mq Vx")
op("movsdRR2", "vmovsd", "F2", 1, 0x11, kind="reg", feat="avx", ops="Ux Hx Vx")
# MOVLPS/MOVHPS family (L0)
op("movlps", "vmovlps", "", 1, 0x12, l=0, kind="mem", feat="avx", ops="Vx Hx Mq")
op("movhlps", "vmovhlps", "", 1, 0x12, l=0, kind="reg", feat="avx", ops="Vx Hx Ux")
op("movlpd", "vmovlpd", "66", 1, 0x12, l=0, kind="mem", feat="avx", ops="Vx Hx Mq")
op("movlpsSt", "vmovlps", "", 1, 0x13, l=0, kind="mem", vvvv=False, feat="avx", ops="Mq Vx")
op("movlpdSt", "vmovlpd", "66", 1, 0x13, l=0, kind="mem", vvvv=False, feat="avx", ops="Mq Vx")
op("movhps", "vmovhps", "", 1, 0x16, l=0, kind="mem", feat="avx", ops="Vx Hx Mq")
op("movlhps", "vmovlhps", "", 1, 0x16, l=0, kind="reg", feat="avx", ops="Vx Hx Ux")
op("movhpd", "vmovhpd", "66", 1, 0x16, l=0, kind="mem", feat="avx", ops="Vx Hx Mq")
op("movhpsSt", "vmovhps", "", 1, 0x17, l=0, kind="mem", vvvv=False, feat="avx", ops="Mq Vx")
op("movhpdSt", "vmovhpd", "66", 1, 0x17, l=0, kind="mem", vvvv=False, feat="avx", ops="Mq Vx")
# masks to general-purpose registers
op("movmskps", "vmovmskps", "", 1, 0x50, kind="reg", vvvv=False, feat="avx", ops="Gd Uv")
op("movmskpd", "vmovmskpd", "66", 1, 0x50, kind="reg", vvvv=False, feat="avx", ops="Gd Uv")
op("pmovmskb", "vpmovmskb", "66", 1, 0xD7, kind="reg", vvvv=False, ops="Gd Uv")
# insert / extract
op("pinsrb", "vpinsrb", "66", 3, 0x20, w=0, l=0, feat="avx", ops="Vx Hx Eb I")
op("pinsrw", "vpinsrw", "66", 1, 0xC4, w=0, l=0, feat="avx", ops="Vx Hx Ew I")
op("pinsrd", "vpinsr", "66", 3, 0x22, l=0, feat="avx", ops="Vx Hx Ey I")   # W0 d, W1 q
op("pextrb", "vpextrb", "66", 3, 0x14, w=0, l=0, vvvv=False, feat="avx", ops="Eb Vx I")
op("pextrw", "vpextrw", "66", 1, 0xC5, w=0, l=0, kind="reg", vvvv=False, feat="avx",
   ops="Gd Ux I")
op("pextrwSt", "vpextrw", "66", 3, 0x15, w=0, l=0, vvvv=False, feat="avx", ops="Ew Vx I")
op("pextrd", "vpextr", "66", 3, 0x16, l=0, vvvv=False, feat="avx", ops="Ey Vx I")  # W0 d, W1 q
op("extractps", "vextractps", "66", 3, 0x17, l=0, vvvv=False, feat="avx", ops="Ed Vx I")
op("insertps", "vinsertps", "66", 3, 0x21, l=0, feat="avx", ops="Vx Hx Wd I")

# ---------------------------------------------------------------- cross-lane
op("permd", "vpermd", "66", 2, 0x36, w=0, l=1, feat="avx2", ops="Vy Hy Wy")
op("permps", "vpermps", "66", 2, 0x16, w=0, l=1, feat="avx2", ops="Vy Hy Wy")
op("permq", "vpermq", "66", 3, 0x00, w=1, l=1, vvvv=False, feat="avx2", ops="Vy Wy I")
op("permpd", "vpermpd", "66", 3, 0x01, w=1, l=1, vvvv=False, feat="avx2", ops="Vy Wy I")
op("perm2i128", "vperm2i128", "66", 3, 0x46, w=0, l=1, feat="avx2", ops="Vy Hy Wy I")
op("perm2f128", "vperm2f128", "66", 3, 0x06, w=0, l=1, feat="avx", ops="Vy Hy Wy I")
op("permilpsV", "vpermilps", "66", 2, 0x0C, w=0, feat="avx")
op("permilpdV", "vpermilpd", "66", 2, 0x0D, w=0, feat="avx")
op("permilpsI", "vpermilps", "66", 3, 0x04, w=0, vvvv=False, feat="avx", ops="Vv Wv I")
op("permilpdI", "vpermilpd", "66", 3, 0x05, w=0, vvvv=False, feat="avx", ops="Vv Wv I")
op("inserti128", "vinserti128", "66", 3, 0x38, w=0, l=1, feat="avx2", ops="Vy Hy Wx I")
op("extracti128", "vextracti128", "66", 3, 0x39, w=0, l=1, vvvv=False, feat="avx2",
   ops="Wx Vy I")
op("insertf128", "vinsertf128", "66", 3, 0x18, w=0, l=1, feat="avx", ops="Vy Hy Wx I")
op("extractf128", "vextractf128", "66", 3, 0x19, w=0, l=1, vvvv=False, feat="avx",
   ops="Wx Vy I")
op("broadcastss", "vbroadcastss", "66", 2, 0x18, w=0, vvvv=False, feat="bcast", ops="Vv Wd")
op("broadcastsd", "vbroadcastsd", "66", 2, 0x19, w=0, l=1, vvvv=False, feat="bcast",
   ops="Vy Wq")
op("broadcastf128", "vbroadcastf128", "66", 2, 0x1A, w=0, l=1, kind="mem", vvvv=False,
   feat="avx", ops="Vy Mx")
op("broadcasti128", "vbroadcasti128", "66", 2, 0x5A, w=0, l=1, kind="mem", vvvv=False,
   feat="avx2", ops="Vy Mx")
op("pbroadcastb", "vpbroadcastb", "66", 2, 0x78, w=0, vvvv=False, feat="avx2", ops="Vv Wb")
op("pbroadcastw", "vpbroadcastw", "66", 2, 0x79, w=0, vvvv=False, feat="avx2", ops="Vv Ww")
op("pbroadcastd", "vpbroadcastd", "66", 2, 0x58, w=0, vvvv=False, feat="avx2", ops="Vv Wd")
op("pbroadcastq", "vpbroadcastq", "66", 2, 0x59, w=0, vvvv=False, feat="avx2", ops="Vv Wq")
op("blendps", "vblendps", "66", 3, 0x0C, feat="avx", ops="Vv Hv Wv I")
op("blendpd", "vblendpd", "66", 3, 0x0D, feat="avx", ops="Vv Hv Wv I")
op("blendvps", "vblendvps", "66", 3, 0x4A, w=0, feat="avx", ops="Vv Hv Wv Lv")
op("blendvpd", "vblendvpd", "66", 3, 0x4B, w=0, feat="avx", ops="Vv Hv Wv Lv")

# ---------------------------------------------------------------- masked moves, gathers
op("maskmovpsLd", "vmaskmovps", "66", 2, 0x2C, w=0, kind="mem", feat="avx", ops="Vv Hv Mv")
op("maskmovpdLd", "vmaskmovpd", "66", 2, 0x2D, w=0, kind="mem", feat="avx", ops="Vv Hv Mv")
op("maskmovpsSt", "vmaskmovps", "66", 2, 0x2E, w=0, kind="mem", feat="avx", ops="Mv Hv Vv")
op("maskmovpdSt", "vmaskmovpd", "66", 2, 0x2F, w=0, kind="mem", feat="avx", ops="Mv Hv Vv")
op("pmaskmovLd", "vpmaskmov", "66", 2, 0x8C, kind="mem", feat="avx2", ops="Vv Hv Mv")
op("pmaskmovSt", "vpmaskmov", "66", 2, 0x8E, kind="mem", feat="avx2", ops="Mv Hv Vv")
op("pgatherd", "vpgatherd", "66", 2, 0x90, kind="mem", feat="avx2", ops="Vg VSIBd Hg")
op("pgatherq", "vpgatherq", "66", 2, 0x91, kind="mem", feat="avx2", ops="Vg VSIBq Hg")
op("gatherd", "vgatherd", "66", 2, 0x92, kind="mem", feat="avx2", ops="Vg VSIBd Hg")
op("gatherq", "vgatherq", "66", 2, 0x93, kind="mem", feat="avx2", ops="Vg VSIBq Hg")

op("zeroupper", "vzeroupper", "", 1, 0x77, l=0, kind="none", vvvv=False, feat="avx", ops="")
op("zeroall", "vzeroall", "", 1, 0x77, l=1, kind="none", vvvv=False, feat="avx", ops="")

# ---------------------------------------------------------------- floating point
for name, opc in [("add", 0x58), ("mul", 0x59), ("sub", 0x5C), ("min", 0x5D), ("div", 0x5E),
                  ("max", 0x5F)]:
    op(name + "ps", "v" + name + "ps", "", 1, opc, feat="avx")
    op(name + "pd", "v" + name + "pd", "66", 1, opc, feat="avx")
    op(name + "ss", "v" + name + "ss", "F3", 1, opc, feat="avx", ops="Vx Hx Wd")
    op(name + "sd", "v" + name + "sd", "F2", 1, opc, feat="avx", ops="Vx Hx Wq")
for name, opc in [("and", 0x54), ("andn", 0x55), ("or", 0x56), ("xor", 0x57),
                  ("unpckl", 0x14), ("unpckh", 0x15)]:
    op(name + "ps", "v" + name + "ps", "", 1, opc, feat="avx")
    op(name + "pd", "v" + name + "pd", "66", 1, opc, feat="avx")
op("addsubps", "vaddsubps", "F2", 1, 0xD0, feat="avx")
op("addsubpd", "vaddsubpd", "66", 1, 0xD0, feat="avx")
op("haddps", "vhaddps", "F2", 1, 0x7C, feat="avx")
op("haddpd", "vhaddpd", "66", 1, 0x7C, feat="avx")
op("hsubps", "vhsubps", "F2", 1, 0x7D, feat="avx")
op("hsubpd", "vhsubpd", "66", 1, 0x7D, feat="avx")
op("shufps", "vshufps", "", 1, 0xC6, feat="avx", ops="Vv Hv Wv I")
op("shufpd", "vshufpd", "66", 1, 0xC6, feat="avx", ops="Vv Hv Wv I")
op("cmpps", "vcmpps", "", 1, 0xC2, feat="avx", ops="Vv Hv Wv I")
op("cmppd", "vcmppd", "66", 1, 0xC2, feat="avx", ops="Vv Hv Wv I")
op("cmpss", "vcmpss", "F3", 1, 0xC2, feat="avx", ops="Vx Hx Wd I")
op("cmpsd", "vcmpsd", "F2", 1, 0xC2, feat="avx", ops="Vx Hx Wq I")
op("sqrtps", "vsqrtps", "", 1, 0x51, vvvv=False, feat="avx", ops="Vv Wv")
op("sqrtpd", "vsqrtpd", "66", 1, 0x51, vvvv=False, feat="avx", ops="Vv Wv")
op("sqrtss", "vsqrtss", "F3", 1, 0x51, feat="avx", ops="Vx Hx Wd")
op("sqrtsd", "vsqrtsd", "F2", 1, 0x51, feat="avx", ops="Vx Hx Wq")
op("roundps", "vroundps", "66", 3, 0x08, vvvv=False, feat="avx", ops="Vv Wv I")
op("roundpd", "vroundpd", "66", 3, 0x09, vvvv=False, feat="avx", ops="Vv Wv I")
op("roundss", "vroundss", "66", 3, 0x0A, feat="avx", ops="Vx Hx Wd I")
op("roundsd", "vroundsd", "66", 3, 0x0B, feat="avx", ops="Vx Hx Wq I")
op("cvtss2sd", "vcvtss2sd", "F3", 1, 0x5A, feat="avx", ops="Vx Hx Wd")
op("cvtsd2ss", "vcvtsd2ss", "F2", 1, 0x5A, feat="avx", ops="Vx Hx Wq")
op("cvtsi2ss", "vcvtsi2ss", "F3", 1, 0x2A, feat="avx", ops="Vx Hx Ey")   # W0 r/m32, W1 r/m64
op("cvtsi2sd", "vcvtsi2sd", "F2", 1, 0x2A, feat="avx", ops="Vx Hx Ey")
op("cvttss2si", "vcvttss2si", "F3", 1, 0x2C, vvvv=False, feat="avx", ops="Gy Wd")
op("cvtss2si", "vcvtss2si", "F3", 1, 0x2D, vvvv=False, feat="avx", ops="Gy Wd")
op("cvttsd2si", "vcvttsd2si", "F2", 1, 0x2C, vvvv=False, feat="avx", ops="Gy Wq")
op("cvtsd2si", "vcvtsd2si", "F2", 1, 0x2D, vvvv=False, feat="avx", ops="Gy Wq")
op("ucomiss", "vucomiss", "", 1, 0x2E, vvvv=False, feat="avx", ops="Vx Wd")
op("comiss", "vcomiss", "", 1, 0x2F, vvvv=False, feat="avx", ops="Vx Wd")
op("ucomisd", "vucomisd", "66", 1, 0x2E, vvvv=False, feat="avx", ops="Vx Wq")
op("comisd", "vcomisd", "66", 1, 0x2F, vvvv=False, feat="avx", ops="Vx Wq")
op("cvtdq2ps", "vcvtdq2ps", "", 1, 0x5B, vvvv=False, feat="avx", ops="Vv Wv")
op("cvtps2dq", "vcvtps2dq", "66", 1, 0x5B, vvvv=False, feat="avx", ops="Vv Wv")
op("cvttps2dq", "vcvttps2dq", "F3", 1, 0x5B, vvvv=False, feat="avx", ops="Vv Wv")
op("cvtps2pd", "vcvtps2pd", "", 1, 0x5A, vvvv=False, feat="avx", ops="Vv Wh")
op("cvtpd2ps", "vcvtpd2ps", "66", 1, 0x5A, vvvv=False, feat="avx", ops="Vx Wv")
op("cvtdq2pd", "vcvtdq2pd", "F3", 1, 0xE6, vvvv=False, feat="avx", ops="Vv Wh")
op("cvtpd2dq", "vcvtpd2dq", "F2", 1, 0xE6, vvvv=False, feat="avx", ops="Vx Wv")
op("cvttpd2dq", "vcvttpd2dq", "66", 1, 0xE6, vvvv=False, feat="avx", ops="Vx Wv")

# ---------------------------------------------------------------- FMA3 (W0 single, W1 double)
for order, base in [("132", 0x90), ("213", 0xA0), ("231", 0xB0)]:
    for kind, off in [("fmaddsub", 6), ("fmsubadd", 7), ("fmaddP", 8), ("fmaddS", 9),
                      ("fmsubP", 10), ("fmsubS", 11), ("fnmaddP", 12), ("fnmaddS", 13),
                      ("fnmsubP", 14), ("fnmsubS", 15)]:
        scalar = kind.endswith("S")
        stem = kind[:-1] if kind[-1] in "PS" else kind
        op(kind + order, "v" + stem + order + ("s" if scalar else "p"), "66", 2, base + off,
           feat="fma", ops="Vx Hx Wsc" if scalar else "Vv Hv Wv")

# ---------------------------------------------------------------- F16C
op("cvtph2ps", "vcvtph2ps", "66", 2, 0x13, w=0, vvvv=False, feat="f16c", ops="Vv Wh")
op("cvtps2ph", "vcvtps2ph", "66", 3, 0x1D, w=0, vvvv=False, feat="f16c", ops="Wh Vv I")


if __name__ == "__main__":
    print(len(ROWS))
