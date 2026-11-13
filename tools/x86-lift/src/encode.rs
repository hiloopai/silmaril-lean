//! A Rust port of `Silmaril.X86.Ext.encode` (`toRaw` in
//! `Silmaril/X86/Ext/Encoding.lean`, `Raw.bytes` in `Silmaril/X86/Ext/Raw.lean`).
//!
//! `Ext.decode` accepts a byte string only if it is the *canonical* encoding
//! of the instruction read (it re-encodes and compares). iced-x86 accepts many
//! more spellings — redundant prefixes, non-minimal displacements, the `8B`
//! register form. The lifter therefore re-encodes every instruction it maps
//! with this port and refuses any whose bytes differ, naming the address. This
//! is a fast pre-check that keeps a failure out of the (slow) Lean build; the
//! kernel check of a Lean module that states the listing is what actually
//! decides.

use crate::ext::*;

#[derive(Clone, Copy)]
enum Pfx {
    None,
    Opsize,
    Rep,
    NopPad(u8),
}

#[derive(Clone, Copy)]
enum Opc {
    One(u8),
    Two(u8),
}

#[derive(Clone, Copy)]
enum Disp {
    None,
    D8(u8),
    D32(u32),
}

#[derive(Clone, Copy)]
enum Imm {
    None,
    I8(u8),
    I16(u16),
    I32(u32),
    I64(u64),
}

#[derive(Clone, Copy)]
struct ModrmPart {
    md: u8,
    reg: u8,
    rm: u8,
    sib: Option<(u8, u8, u8)>,
    disp: Disp,
}

struct Raw {
    fs: bool,
    pfx: Pfx,
    rex: Option<(bool, bool, bool, bool)>,
    opc: Opc,
    modrm: Option<ModrmPart>,
    imm: Imm,
}

impl Raw {
    fn bytes(&self) -> Vec<u8> {
        let mut v = Vec::new();
        if self.fs {
            v.push(0x64);
        }
        match self.pfx {
            Pfx::None => {}
            Pfx::Opsize => v.push(0x66),
            Pfx::Rep => v.push(0xF3),
            Pfx::NopPad(n) => {
                v.extend(std::iter::repeat_n(0x66, n as usize + 1));
                v.push(0x2E);
            }
        }
        if let Some((w, r, x, b)) = self.rex {
            v.push(0x40 | (w as u8) << 3 | (r as u8) << 2 | (x as u8) << 1 | b as u8);
        }
        match self.opc {
            Opc::One(b) => v.push(b),
            Opc::Two(b) => v.extend([0x0F, b]),
        }
        if let Some(m) = self.modrm {
            v.push(m.md << 6 | m.reg << 3 | m.rm);
            if let Some((s, i, b)) = m.sib {
                v.push(s << 6 | i << 3 | b);
            }
            match m.disp {
                Disp::None => {}
                Disp::D8(d) => v.push(d),
                Disp::D32(d) => v.extend(d.to_le_bytes()),
            }
        }
        match self.imm {
            Imm::None => {}
            Imm::I8(i) => v.push(i),
            Imm::I16(i) => v.extend(i.to_le_bytes()),
            Imm::I32(i) => v.extend(i.to_le_bytes()),
            Imm::I64(i) => v.extend(i.to_le_bytes()),
        }
        v
    }
}

fn mk_rex(w: bool, r: bool, x: bool, b: bool, force: bool) -> Option<(bool, bool, bool, bool)> {
    (w || r || x || b || force).then_some((w, r, x, b))
}

fn fits8(d: u32) -> bool {
    (d as u8 as i8 as i32 as u32) == d
}

fn disp_choice(base: Reg, d: u32) -> (u8, Disp) {
    if d == 0 && base.lo() != 5 {
        (0, Disp::None)
    } else if fits8(d) {
        (1, Disp::D8(d as u8))
    } else {
        (2, Disp::D32(d))
    }
}

/// `EncRM`: (x, b, mod, rm, sib, disp).
struct EncRM {
    x: bool,
    b: bool,
    md: u8,
    rm: u8,
    sib: Option<(u8, u8, u8)>,
    disp: Disp,
}

fn encode_mem(m: &Mem) -> EncRM {
    match m.base {
        Base::Rip => EncRM {
            x: false,
            b: false,
            md: 0,
            rm: 5,
            sib: None,
            disp: Disp::D32(m.disp),
        },
        Base::None | Base::Fs => match m.index {
            None => EncRM {
                x: false,
                b: false,
                md: 0,
                rm: 4,
                sib: Some((0, 4, 5)),
                disp: Disp::D32(m.disp),
            },
            Some(i) => EncRM {
                x: i.reg.hi(),
                b: false,
                md: 0,
                rm: 4,
                sib: Some((i.scale, i.reg.lo(), 5)),
                disp: Disp::D32(m.disp),
            },
        },
        Base::Reg(base) => {
            let (md, disp) = disp_choice(base, m.disp);
            match m.index {
                None if base.lo() == 4 => EncRM {
                    x: false,
                    b: base.hi(),
                    md,
                    rm: 4,
                    sib: Some((0, 4, 4)),
                    disp,
                },
                None => EncRM {
                    x: false,
                    b: base.hi(),
                    md,
                    rm: base.lo(),
                    sib: None,
                    disp,
                },
                Some(i) => EncRM {
                    x: i.reg.hi(),
                    b: base.hi(),
                    md,
                    rm: 4,
                    sib: Some((i.scale, i.reg.lo(), base.lo())),
                    disp,
                },
            }
        }
    }
}

fn encode_rm(op: &RM) -> EncRM {
    match op {
        RM::Reg(r) => EncRM {
            x: false,
            b: r.hi(),
            md: 3,
            rm: r.lo(),
            sib: None,
            disp: Disp::None,
        },
        RM::Mem(m) => encode_mem(m),
    }
}

#[allow(clippy::too_many_arguments)]
fn rm_raw(pfx: Pfx, w: bool, opc: Opc, reg: u8, r_hi: bool, op: RM, force: bool, imm: Imm) -> Raw {
    let e = encode_rm(&op);
    Raw {
        fs: op.is_fs(),
        pfx,
        rex: mk_rex(w, r_hi, e.x, e.b, force),
        opc,
        modrm: Some(ModrmPart {
            md: e.md,
            reg,
            rm: e.rm,
            sib: e.sib,
            disp: e.disp,
        }),
        imm,
    }
}

fn plain_raw(w: bool, b_hi: bool, opc: Opc, imm: Imm) -> Raw {
    Raw {
        fs: false,
        pfx: Pfx::None,
        rex: mk_rex(w, false, false, b_hi, false),
        opc,
        modrm: None,
        imm,
    }
}

fn nop_raw(len: u8) -> Raw {
    let m = |md, rm, sib: Option<(u8, u8, u8)>, disp| ModrmPart {
        md,
        reg: 0,
        rm,
        sib,
        disp,
    };
    let m0 = m(0, 0, None, Disp::None);
    let m1 = m(1, 0, None, Disp::D8(0));
    let m2 = m(1, 4, Some((0, 0, 0)), Disp::D8(0));
    let m3 = m(2, 0, None, Disp::D32(0));
    let m4 = m(2, 4, Some((0, 0, 0)), Disp::D32(0));
    let f = |pfx, mp| Raw {
        fs: false,
        pfx,
        rex: None,
        opc: Opc::Two(0x1F),
        modrm: Some(mp),
        imm: Imm::None,
    };
    match len {
        0 => Raw {
            fs: false,
            pfx: Pfx::None,
            rex: None,
            opc: Opc::One(0x90),
            modrm: None,
            imm: Imm::None,
        },
        1 => Raw {
            fs: false,
            pfx: Pfx::Opsize,
            rex: None,
            opc: Opc::One(0x90),
            modrm: None,
            imm: Imm::None,
        },
        2 => f(Pfx::None, m0),
        3 => f(Pfx::None, m1),
        4 => f(Pfx::None, m2),
        5 => f(Pfx::Opsize, m2),
        6 => f(Pfx::None, m3),
        7 => f(Pfx::None, m4),
        8 => f(Pfx::Opsize, m4),
        9..=13 => f(Pfx::NopPad(len - 9), m4),
        _ => f(Pfx::NopPad(5), m4),
    }
}

fn movx_opcode(sx: bool, n: Narrow) -> u8 {
    match (sx, n) {
        (false, Narrow::B) => 0xB6,
        (false, Narrow::W) => 0xB7,
        (true, Narrow::B) => 0xBE,
        (true, Narrow::W) => 0xBF,
    }
}

fn to_raw(i: &Instr) -> Raw {
    use Instr::*;
    let one = Opc::One;
    let two = Opc::Two;
    match *i {
        Mov(sz, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x89),
            src.lo(),
            src.hi(),
            dst,
            false,
            Imm::None,
        ),
        MovI(sz, dst, imm) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xC7),
            0,
            false,
            dst,
            false,
            Imm::I32(imm),
        ),
        MovI16(dst, imm) => rm_raw(
            Pfx::Opsize,
            false,
            one(0xC7),
            0,
            false,
            dst,
            false,
            Imm::I16(imm),
        ),
        Mov8(dst, src) => rm_raw(
            Pfx::None,
            false,
            one(0x8A),
            dst.lo(),
            dst.hi(),
            src,
            dst.needs_rex_byte() || src.rex_byte(),
            Imm::None,
        ),
        MovI8(dst, imm) => rm_raw(
            Pfx::None,
            false,
            one(0xC6),
            0,
            false,
            dst,
            dst.rex_byte(),
            Imm::I8(imm),
        ),
        MovI32(dst, imm) => plain_raw(false, dst.hi(), one(0xB8 | dst.lo()), Imm::I32(imm)),
        Movabs(dst, imm) => plain_raw(true, dst.hi(), one(0xB8 | dst.lo()), Imm::I64(imm)),
        Load(sz, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x8B),
            dst.lo(),
            dst.hi(),
            RM::Mem(src),
            false,
            Imm::None,
        ),
        Store(Narrow::B, dst, src) => rm_raw(
            Pfx::None,
            false,
            one(0x88),
            src.lo(),
            src.hi(),
            dst,
            src.needs_rex_byte() || dst.rex_byte(),
            Imm::None,
        ),
        Store(Narrow::W, dst, src) => rm_raw(
            Pfx::Opsize,
            false,
            one(0x89),
            src.lo(),
            src.hi(),
            dst,
            false,
            Imm::None,
        ),
        Movx(sx, sz, n, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            two(movx_opcode(sx, n)),
            dst.lo(),
            dst.hi(),
            src,
            n == Narrow::B && src.rex_byte(),
            Imm::None,
        ),
        Movsxd(dst, src) => rm_raw(
            Pfx::None,
            true,
            one(0x63),
            dst.lo(),
            dst.hi(),
            src,
            false,
            Imm::None,
        ),
        Lea(sz, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x8D),
            dst.lo(),
            dst.hi(),
            RM::Mem(src),
            false,
            Imm::None,
        ),
        Alu(sz, op, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(op.opcode()),
            src.lo(),
            src.hi(),
            dst,
            false,
            Imm::None,
        ),
        AluR(sz, op, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(op.opcode_r()),
            dst.lo(),
            dst.hi(),
            src,
            false,
            Imm::None,
        ),
        AluI(sz, op, dst, imm) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x81),
            op.digit(),
            false,
            dst,
            false,
            Imm::I32(imm),
        ),
        AluI8(sz, op, dst, imm) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x83),
            op.digit(),
            false,
            dst,
            false,
            Imm::I8(imm),
        ),
        AluA(sz, op, imm) => plain_raw(sz.w(), false, one(op.opcode_a()), Imm::I32(imm)),
        CmpI8(dst, imm) => rm_raw(
            Pfx::None,
            false,
            one(0x80),
            7,
            false,
            dst,
            dst.rex_byte(),
            Imm::I8(imm),
        ),
        CmpA8(imm) => plain_raw(false, false, one(0x3C), Imm::I8(imm)),
        Test(sz, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0x85),
            src.lo(),
            src.hi(),
            dst,
            false,
            Imm::None,
        ),
        Test8(dst, src) => rm_raw(
            Pfx::None,
            false,
            one(0x84),
            src.lo(),
            src.hi(),
            dst,
            src.needs_rex_byte() || dst.rex_byte(),
            Imm::None,
        ),
        TestI8(dst, imm) => rm_raw(
            Pfx::None,
            false,
            one(0xF6),
            0,
            false,
            dst,
            dst.rex_byte(),
            Imm::I8(imm),
        ),
        TestA8(imm) => plain_raw(false, false, one(0xA8), Imm::I8(imm)),
        TestA(sz, imm) => plain_raw(sz.w(), false, one(0xA9), Imm::I32(imm)),
        Incdec(sz, dec, dst) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xFF),
            dec as u8,
            false,
            dst,
            false,
            Imm::None,
        ),
        PushRM(src) => rm_raw(Pfx::None, false, one(0xFF), 6, false, src, false, Imm::None),
        Bswap(sz, dst) => plain_raw(sz.w(), dst.hi(), two(0xC8 | dst.lo()), Imm::None),
        Unary(sz, op, dst) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xF7),
            op.digit(),
            false,
            dst,
            false,
            Imm::None,
        ),
        Imul(sz, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            two(0xAF),
            dst.lo(),
            dst.hi(),
            src,
            false,
            Imm::None,
        ),
        Shift(sz, op, dst, Count::Cl) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xD3),
            op.digit(),
            false,
            dst,
            false,
            Imm::None,
        ),
        Shift(sz, op, dst, Count::One) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xD1),
            op.digit(),
            false,
            dst,
            false,
            Imm::None,
        ),
        Shift(sz, op, dst, Count::Imm(n)) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xC1),
            op.digit(),
            false,
            dst,
            false,
            Imm::I8(n),
        ),
        Cxd(sz) => plain_raw(sz.w(), false, one(0x99), Imm::None),
        Cxe(sz) => plain_raw(sz.w(), false, one(0x98), Imm::None),
        Mul(sz, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xF7),
            4,
            false,
            src,
            false,
            Imm::None,
        ),
        Div(sz, signed, src) => rm_raw(
            Pfx::None,
            sz.w(),
            one(0xF7),
            if signed { 7 } else { 6 },
            false,
            src,
            false,
            Imm::None,
        ),
        Setcc(c, dst) => rm_raw(
            Pfx::None,
            false,
            two(0x90 | c.code()),
            0,
            false,
            dst,
            dst.rex_byte(),
            Imm::None,
        ),
        Cmov(sz, c, dst, src) => rm_raw(
            Pfx::None,
            sz.w(),
            two(0x40 | c.code()),
            dst.lo(),
            dst.hi(),
            src,
            false,
            Imm::None,
        ),
        Jmp(rel) => plain_raw(false, false, one(0xE9), Imm::I32(rel)),
        Jmp8(rel) => plain_raw(false, false, one(0xEB), Imm::I8(rel)),
        Jcc(c, rel) => plain_raw(false, false, two(0x80 | c.code()), Imm::I32(rel)),
        Jcc8(c, rel) => plain_raw(false, false, one(0x70 | c.code()), Imm::I8(rel)),
        Call(rel) => plain_raw(false, false, one(0xE8), Imm::I32(rel)),
        Ret => plain_raw(false, false, one(0xC3), Imm::None),
        Leave => plain_raw(false, false, one(0xC9), Imm::None),
        Endbr64 => Raw {
            fs: false,
            pfx: Pfx::Rep,
            rex: None,
            opc: two(0x1E),
            modrm: Some(ModrmPart {
                md: 3,
                reg: 7,
                rm: 2,
                sib: None,
                disp: Disp::None,
            }),
            imm: Imm::None,
        },
        Push(r) => plain_raw(false, r.hi(), one(0x50 | r.lo()), Imm::None),
        Pop(r) => plain_raw(false, r.hi(), one(0x58 | r.lo()), Imm::None),
        Ud2 => plain_raw(false, false, two(0x0B), Imm::None),
        Nop(len) => nop_raw(len),
        Bitcount(op, sz, dst, src) => rm_raw(
            Pfx::Rep,
            sz.w(),
            two(op.opcode()),
            dst.lo(),
            dst.hi(),
            src,
            false,
            Imm::None,
        ),
    }
}

/// `Ext.encode`: the canonical encoding of an instruction of the model.
pub fn encode(i: &Instr) -> Vec<u8> {
    to_raw(i).bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hexs(v: &[u8]) -> String {
        v.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn known_encodings() {
        // Canonical encodings of instructions of the model, as compilers emit
        // them.
        let rsp_disp = |d: u32| Mem {
            base: Base::Reg(Reg::Rsp),
            index: None,
            disp: d,
        };
        let cases: Vec<(Instr, &str)> = vec![
            (Instr::Push(Reg::Rbp), "55"),
            (Instr::Push(Reg::R15), "4157"),
            (
                Instr::AluI(Sz::Q, AluOp::Sub, RM::Reg(Reg::Rsp), 0xa8),
                "4881eca8000000",
            ),
            (
                Instr::Alu(Sz::D, AluOp::Xor, RM::Reg(Reg::Rax), Reg::Rax),
                "31c0",
            ),
            (Instr::Nop(12), "666666662e0f1f840000000000"),
            (Instr::Nop(4), "0f1f440000"),
            (Instr::AluA(Sz::Q, AluOp::Cmp, 0x100), "483d00010000"),
            (Instr::MovI32(Reg::Rax, 0x10), "b810000000"),
            (Instr::Bswap(Sz::D, Reg::Rcx), "0fc9"),
            (Instr::Incdec(Sz::Q, false, RM::Reg(Reg::Rax)), "48ffc0"),
            (Instr::Jcc8(Cond::Ne, 0xee), "75ee"),
            (
                Instr::Lea(
                    Sz::Q,
                    Reg::Rcx,
                    Mem {
                        base: Base::Rip,
                        index: None,
                        disp: 0,
                    },
                ),
                "488d0d00000000",
            ),
            (
                Instr::Load(Sz::D, Reg::Rdx, rsp_disp(0xffffffa0)),
                "8b5424a0",
            ),
            (
                Instr::Mov8(
                    Reg::Rdx,
                    RM::Mem(Mem {
                        base: Base::Reg(Reg::Rax),
                        index: Some(Index {
                            reg: Reg::Rcx,
                            scale: 0,
                        }),
                        disp: 0,
                    }),
                ),
                "8a1408",
            ),
            (Instr::Store(Narrow::B, RM::Reg(Reg::Rdx), Reg::Rax), "88c2"),
            (Instr::Jmp(0xFFFFFFD2), "e9d2ffffff"),
            (Instr::Ret, "c3"),
        ];
        for (i, want) in cases {
            assert_eq!(hexs(&encode(&i)), want, "{i:?}");
        }
    }
}
