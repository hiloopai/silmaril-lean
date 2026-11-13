//! A Rust mirror of `Silmaril.X86.Ext.Instr` (`Silmaril/X86/Ext/Syntax.lean`).
//!
//! Every type and constructor here corresponds one-for-one, in name and in
//! argument order, to the Lean syntax, and [`Instr::lean`] prints the Lean
//! term. Immediates and displacements are stored at their Lean bit width
//! (`BitVec 8/16/32/64` become `u8/u16/u32/u64`, raw bits, no sign).
//!
//! If the Lean syntax changes, this file and `encode.rs` must change with it;
//! a Lean module that checks a listing printed from these terms against the
//! model's decoder fails otherwise, so drift cannot go unnoticed.

use std::fmt::Write;

/// `Silmaril.X86.Reg`, in hardware-number order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[allow(missing_docs)]
pub enum Reg {
    Rax,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl Reg {
    /// All sixteen, by hardware number.
    pub const ALL: [Reg; 16] = [
        Reg::Rax,
        Reg::Rcx,
        Reg::Rdx,
        Reg::Rbx,
        Reg::Rsp,
        Reg::Rbp,
        Reg::Rsi,
        Reg::Rdi,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
        Reg::R12,
        Reg::R13,
        Reg::R14,
        Reg::R15,
    ];

    /// The four-bit hardware number (`Reg.toBitVec`).
    pub fn num(self) -> u8 {
        self as u8
    }

    /// The REX extension bit (`hiBit`).
    pub fn hi(self) -> bool {
        self.num() & 8 != 0
    }

    /// The low three bits (`Reg.lo`).
    pub fn lo(self) -> u8 {
        self.num() & 7
    }

    /// SPL/BPL/SIL/DIL need a REX prefix to be addressed as bytes
    /// (`Ext.needsRexByte`).
    pub fn needs_rex_byte(self) -> bool {
        !self.hi() && self.lo() >= 4
    }

    /// The Lean constructor name.
    pub fn lean(self) -> &'static str {
        [
            "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11",
            "r12", "r13", "r14", "r15",
        ][self as usize]
    }
}

/// `Ext.Sz`: 32-bit (`d`) or 64-bit (`q`) operand size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Sz {
    D,
    Q,
}

impl Sz {
    /// REX.W.
    pub fn w(self) -> bool {
        self == Sz::Q
    }
    fn lean(self) -> &'static str {
        match self {
            Sz::D => ".d",
            Sz::Q => ".q",
        }
    }
}

/// `Ext.Narrow`: 8-bit (`b`) or 16-bit (`w`) access.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Narrow {
    B,
    W,
}

impl Narrow {
    fn lean(self) -> &'static str {
        match self {
            Narrow::B => ".b",
            Narrow::W => ".w",
        }
    }
}

/// `Ext.Index`: a scaled index register (never RSP); multiplier `2^scale`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Index {
    /// The index register.
    pub reg: Reg,
    /// The SIB scale field, 0..=3.
    pub scale: u8,
}

/// `Ext.Base`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Base {
    /// A base register.
    Reg(Reg),
    /// No base: `[index*2^s + disp32]` or `[disp32]`.
    None,
    /// `[rip + disp32]`, relative to the next instruction.
    Rip,
    /// `fs:[index*2^s + disp32]`.
    Fs,
}

/// `Ext.Mem`: `[base + index * 2^scale + disp]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mem {
    /// The base.
    pub base: Base,
    /// The optional index.
    pub index: Option<Index>,
    /// The displacement (raw 32 bits, sign-extended by the machine).
    pub disp: u32,
}

/// `Ext.RM`: a register or memory operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum RM {
    Reg(Reg),
    Mem(Mem),
}

impl RM {
    fn needs_rex_byte(self) -> bool {
        matches!(self, RM::Reg(r) if r.needs_rex_byte())
    }
    pub(crate) fn is_fs(self) -> bool {
        matches!(self, RM::Mem(Mem { base: Base::Fs, .. }))
    }
    pub(crate) fn rex_byte(self) -> bool {
        self.needs_rex_byte()
    }
}

/// `X86.AluOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum AluOp {
    Add,
    Or,
    And,
    Sub,
    Xor,
    Cmp,
}

impl AluOp {
    /// `AluOp.opcode` (direction 0, `op r/m, reg`).
    pub fn opcode(self) -> u8 {
        [0x01, 0x09, 0x21, 0x29, 0x31, 0x39][self as usize]
    }
    /// `aluOpcodeR` (direction 1, `op reg, r/m`).
    pub fn opcode_r(self) -> u8 {
        [0x03, 0x0B, 0x23, 0x2B, 0x33, 0x3B][self as usize]
    }
    /// `aluOpcodeA` (accumulator, imm32).
    pub fn opcode_a(self) -> u8 {
        [0x05, 0x0D, 0x25, 0x2D, 0x35, 0x3D][self as usize]
    }
    /// `AluOp.digit` (`81 /digit`, `83 /digit`).
    pub fn digit(self) -> u8 {
        [0, 1, 4, 5, 6, 7][self as usize]
    }
    fn lean(self) -> &'static str {
        [".add", ".or", ".and", ".sub", ".xor", ".cmp"][self as usize]
    }
}

/// `Ext.UnOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum UnOp {
    Neg,
    Not,
}

impl UnOp {
    /// `UnOp.digit`.
    pub fn digit(self) -> u8 {
        match self {
            UnOp::Not => 2,
            UnOp::Neg => 3,
        }
    }
    fn lean(self) -> &'static str {
        match self {
            UnOp::Neg => ".neg",
            UnOp::Not => ".not",
        }
    }
}

/// `Ext.ShiftOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum ShiftOp {
    Rol,
    Ror,
    Shl,
    Shr,
    Sar,
}

impl ShiftOp {
    /// `ShiftOp.digit`.
    pub fn digit(self) -> u8 {
        [0, 1, 4, 5, 7][self as usize]
    }
    fn lean(self) -> &'static str {
        [".rol", ".ror", ".shl", ".shr", ".sar"][self as usize]
    }
}

/// `Ext.Count`: CL, the implicit 1, or an imm8.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Count {
    Cl,
    One,
    Imm(u8),
}

/// `Ext.BitCountOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum BitCountOp {
    Lzcnt,
    Tzcnt,
    Popcnt,
}

impl BitCountOp {
    /// `BitCountOp.opcode` (after `F3 0F`).
    pub fn opcode(self) -> u8 {
        [0xBD, 0xBC, 0xB8][self as usize]
    }
    fn lean(self) -> &'static str {
        [".lzcnt", ".tzcnt", ".popcnt"][self as usize]
    }
}

/// `Ext.Cond`, in encoding order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Cond {
    O,
    No,
    B,
    Ae,
    E,
    Ne,
    Be,
    A,
    S,
    Ns,
    P,
    Np,
    L,
    Ge,
    Le,
    G,
}

impl Cond {
    /// `Cond.code`.
    pub fn code(self) -> u8 {
        self as u8
    }
    /// `Cond.ofCode`.
    pub fn of_code(c: u8) -> Cond {
        use Cond::*;
        [O, No, B, Ae, E, Ne, Be, A, S, Ns, P, Np, L, Ge, Le, G][(c & 15) as usize]
    }
    fn lean(self) -> &'static str {
        [
            ".o", ".no", ".b", ".ae", ".e", ".ne", ".be", ".a", ".s", ".ns", ".p", ".np", ".l",
            ".ge", ".le", ".g",
        ][self as usize]
    }
}

/// `Ext.Instr`. Constructor names are the Lean ones in CamelCase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Instr {
    Mov(Sz, RM, Reg),
    MovI(Sz, RM, u32),
    MovI16(RM, u16),
    Mov8(Reg, RM),
    MovI8(RM, u8),
    MovI32(Reg, u32),
    Movabs(Reg, u64),
    Load(Sz, Reg, Mem),
    Store(Narrow, RM, Reg),
    Movx(bool, Sz, Narrow, Reg, RM),
    Movsxd(Reg, RM),
    Lea(Sz, Reg, Mem),
    Alu(Sz, AluOp, RM, Reg),
    AluR(Sz, AluOp, Reg, RM),
    AluI(Sz, AluOp, RM, u32),
    AluI8(Sz, AluOp, RM, u8),
    AluA(Sz, AluOp, u32),
    CmpI8(RM, u8),
    CmpA8(u8),
    Test(Sz, RM, Reg),
    Test8(RM, Reg),
    TestI8(RM, u8),
    TestA8(u8),
    TestA(Sz, u32),
    Incdec(Sz, bool, RM),
    PushRM(RM),
    Bswap(Sz, Reg),
    Unary(Sz, UnOp, RM),
    Imul(Sz, Reg, RM),
    Shift(Sz, ShiftOp, RM, Count),
    Cxd(Sz),
    Cxe(Sz),
    Mul(Sz, RM),
    Div(Sz, bool, RM),
    Setcc(Cond, RM),
    Cmov(Sz, Cond, Reg, RM),
    Jmp(u32),
    Jmp8(u8),
    Jcc(Cond, u32),
    Jcc8(Cond, u8),
    Call(u32),
    Ret,
    Leave,
    Endbr64,
    Push(Reg),
    Pop(Reg),
    Ud2,
    /// A canonical NOP of `len + 1` bytes, `len < 15`.
    Nop(u8),
    Bitcount(BitCountOp, Sz, Reg, RM),
}

fn reg(r: Reg) -> String {
    format!(".{}", r.lean())
}

fn hex(v: u64) -> String {
    format!("{v:#x}")
}

fn index(i: &Option<Index>) -> String {
    match i {
        None => "none".into(),
        Some(i) => format!("(some (ix .{} {}))", i.reg.lean(), i.scale),
    }
}

impl Mem {
    /// The Lean term, using the smart constructors `Mem.ofReg`, `Mem.ofIndex`,
    /// `Mem.ofRip`, `Mem.ofFs` and the `Lift.ix` index helper.
    pub fn lean(&self) -> String {
        match self.base {
            Base::Reg(r) => format!(
                "Mem.ofReg {} {} {}",
                reg(r),
                index(&self.index),
                hex(self.disp.into())
            ),
            Base::None => format!(
                "Mem.ofIndex {} {}",
                index(&self.index),
                hex(self.disp.into())
            ),
            Base::Rip => format!("Mem.ofRip {}", hex(self.disp.into())),
            Base::Fs => format!("Mem.ofFs {} {}", index(&self.index), hex(self.disp.into())),
        }
    }
}

impl RM {
    /// The Lean term, parenthesised.
    pub fn lean(&self) -> String {
        match self {
            RM::Reg(r) => format!("(.reg {})", reg(*r)),
            RM::Mem(m) => format!("(.mem ({}))", m.lean()),
        }
    }
}

fn count(c: Count) -> String {
    match c {
        Count::Cl => ".cl".into(),
        Count::One => ".one".into(),
        Count::Imm(n) => format!("(.imm {})", hex(n.into())),
    }
}

impl Instr {
    /// The Lean term of type `Silmaril.X86.Ext.Instr`, written with leading-dot
    /// constructors (the expected type is always known where it is used).
    pub fn lean(&self) -> String {
        use Instr::*;
        let mut s = String::new();
        let _ = match *self {
            Mov(sz, d, r) => write!(s, ".mov {} {} {}", sz.lean(), d.lean(), reg(r)),
            MovI(sz, d, i) => write!(s, ".movI {} {} {}", sz.lean(), d.lean(), hex(i.into())),
            MovI16(d, i) => write!(s, ".movI16 {} {}", d.lean(), hex(i.into())),
            Mov8(r, src) => write!(s, ".mov8 {} {}", reg(r), src.lean()),
            MovI8(d, i) => write!(s, ".movI8 {} {}", d.lean(), hex(i.into())),
            MovI32(r, i) => write!(s, ".movI32 {} {}", reg(r), hex(i.into())),
            Movabs(r, i) => write!(s, ".movabs {} {}", reg(r), hex(i)),
            Load(sz, r, m) => write!(s, ".load {} {} ({})", sz.lean(), reg(r), m.lean()),
            Store(n, d, r) => write!(s, ".store {} {} {}", n.lean(), d.lean(), reg(r)),
            Movx(sx, sz, n, r, src) => {
                write!(
                    s,
                    ".movx {} {} {} {} {}",
                    sx,
                    sz.lean(),
                    n.lean(),
                    reg(r),
                    src.lean()
                )
            }
            Movsxd(r, src) => write!(s, ".movsxd {} {}", reg(r), src.lean()),
            Lea(sz, r, m) => write!(s, ".lea {} {} ({})", sz.lean(), reg(r), m.lean()),
            Alu(sz, op, d, r) => write!(
                s,
                ".alu {} {} {} {}",
                sz.lean(),
                op.lean(),
                d.lean(),
                reg(r)
            ),
            AluR(sz, op, r, src) => {
                write!(
                    s,
                    ".aluR {} {} {} {}",
                    sz.lean(),
                    op.lean(),
                    reg(r),
                    src.lean()
                )
            }
            AluI(sz, op, d, i) => {
                write!(
                    s,
                    ".aluI {} {} {} {}",
                    sz.lean(),
                    op.lean(),
                    d.lean(),
                    hex(i.into())
                )
            }
            AluI8(sz, op, d, i) => {
                write!(
                    s,
                    ".aluI8 {} {} {} {}",
                    sz.lean(),
                    op.lean(),
                    d.lean(),
                    hex(i.into())
                )
            }
            AluA(sz, op, i) => write!(s, ".aluA {} {} {}", sz.lean(), op.lean(), hex(i.into())),
            CmpI8(d, i) => write!(s, ".cmpI8 {} {}", d.lean(), hex(i.into())),
            CmpA8(i) => write!(s, ".cmpA8 {}", hex(i.into())),
            Test(sz, d, r) => write!(s, ".test {} {} {}", sz.lean(), d.lean(), reg(r)),
            Test8(d, r) => write!(s, ".test8 {} {}", d.lean(), reg(r)),
            TestI8(d, i) => write!(s, ".testI8 {} {}", d.lean(), hex(i.into())),
            TestA8(i) => write!(s, ".testA8 {}", hex(i.into())),
            TestA(sz, i) => write!(s, ".testA {} {}", sz.lean(), hex(i.into())),
            Incdec(sz, dec, d) => write!(s, ".incdec {} {} {}", sz.lean(), dec, d.lean()),
            PushRM(src) => write!(s, ".pushRM {}", src.lean()),
            Bswap(sz, r) => write!(s, ".bswap {} {}", sz.lean(), reg(r)),
            Unary(sz, op, d) => write!(s, ".unary {} {} {}", sz.lean(), op.lean(), d.lean()),
            Imul(sz, r, src) => write!(s, ".imul {} {} {}", sz.lean(), reg(r), src.lean()),
            Shift(sz, op, d, c) => {
                write!(
                    s,
                    ".shift {} {} {} {}",
                    sz.lean(),
                    op.lean(),
                    d.lean(),
                    count(c)
                )
            }
            Cxd(sz) => write!(s, ".cxd {}", sz.lean()),
            Cxe(sz) => write!(s, ".cxe {}", sz.lean()),
            Mul(sz, src) => write!(s, ".mul {} {}", sz.lean(), src.lean()),
            Div(sz, signed, src) => write!(s, ".div {} {} {}", sz.lean(), signed, src.lean()),
            Setcc(c, d) => write!(s, ".setcc {} {}", c.lean(), d.lean()),
            Cmov(sz, c, r, src) => write!(
                s,
                ".cmov {} {} {} {}",
                sz.lean(),
                c.lean(),
                reg(r),
                src.lean()
            ),
            Jmp(r) => write!(s, ".jmp {}", hex(r.into())),
            Jmp8(r) => write!(s, ".jmp8 {}", hex(r.into())),
            Jcc(c, r) => write!(s, ".jcc {} {}", c.lean(), hex(r.into())),
            Jcc8(c, r) => write!(s, ".jcc8 {} {}", c.lean(), hex(r.into())),
            Call(r) => write!(s, ".call {}", hex(r.into())),
            Ret => write!(s, ".ret"),
            Leave => write!(s, ".leave"),
            Endbr64 => write!(s, ".endbr64"),
            Push(r) => write!(s, ".push {}", reg(r)),
            Pop(r) => write!(s, ".pop {}", reg(r)),
            Ud2 => write!(s, ".ud2"),
            Nop(n) => write!(s, ".nop {n}"),
            Bitcount(op, sz, r, src) => {
                write!(
                    s,
                    ".bitcount {} {} {} {}",
                    op.lean(),
                    sz.lean(),
                    reg(r),
                    src.lean()
                )
            }
        };
        s
    }

    /// The model's mnemonic class, for statistics.
    pub fn form(&self) -> &'static str {
        use Instr::*;
        match self {
            Mov(..) => "mov",
            MovI(..) => "movI",
            MovI16(..) => "movI16",
            Mov8(..) => "mov8",
            MovI8(..) => "movI8",
            MovI32(..) => "movI32",
            Movabs(..) => "movabs",
            Load(..) => "load",
            Store(..) => "store",
            Movx(..) => "movx",
            Movsxd(..) => "movsxd",
            Lea(..) => "lea",
            Alu(..) => "alu",
            AluR(..) => "aluR",
            AluI(..) => "aluI",
            AluI8(..) => "aluI8",
            AluA(..) => "aluA",
            CmpI8(..) => "cmpI8",
            CmpA8(..) => "cmpA8",
            Test(..) => "test",
            Test8(..) => "test8",
            TestI8(..) => "testI8",
            TestA8(..) => "testA8",
            TestA(..) => "testA",
            Incdec(..) => "incdec",
            PushRM(..) => "pushRM",
            Bswap(..) => "bswap",
            Unary(..) => "unary",
            Imul(..) => "imul",
            Shift(..) => "shift",
            Cxd(..) => "cxd",
            Cxe(..) => "cxe",
            Mul(..) => "mul",
            Div(..) => "div",
            Setcc(..) => "setcc",
            Cmov(..) => "cmov",
            Jmp(..) => "jmp",
            Jmp8(..) => "jmp8",
            Jcc(..) => "jcc",
            Jcc8(..) => "jcc8",
            Call(..) => "call",
            Ret => "ret",
            Leave => "leave",
            Endbr64 => "endbr64",
            Push(..) => "push",
            Pop(..) => "pop",
            Ud2 => "ud2",
            Nop(..) => "nop",
            Bitcount(..) => "bitcount",
        }
    }
}
