//! Mapping iced-x86's decoded instructions into [`crate::ext::Instr`].
//!
//! iced names each instruction form by a `Code` such as `Add_rm32_imm8`: the
//! mnemonic followed by the operand forms. The mapping reads that name — so it
//! selects on exactly the opcode form iced decoded, including direction
//! (`Add_rm32_r32` is `01 /r`, `Add_r32_rm32` is `03 /r`) and immediate width
//! (`imm8` is `83`, `imm32` is `81`) — and takes the operands from iced's
//! operand accessors. Forms the Lean model does not have are rejected with
//! their name; nothing is approximated.
//!
//! A successful mapping is necessary but not sufficient: the Lean decoder only
//! accepts canonical encodings, so [`crate::lift`] re-encodes every mapped
//! instruction with [`crate::encode`] and compares bytes.

use anyhow::{Result, anyhow, bail, ensure};
use iced_x86::{Instruction, OpKind, Register};

use crate::ext::*;

/// A general-purpose register of the model.
pub fn gpr(r: Register) -> Result<Reg> {
    use Register as R;
    if matches!(r, R::AH | R::CH | R::DH | R::BH) {
        bail!("high-byte register {r:?} is not in the model");
    }
    let full = r.full_register();
    let i = match full {
        R::RAX => 0,
        R::RCX => 1,
        R::RDX => 2,
        R::RBX => 3,
        R::RSP => 4,
        R::RBP => 5,
        R::RSI => 6,
        R::RDI => 7,
        R::R8 => 8,
        R::R9 => 9,
        R::R10 => 10,
        R::R11 => 11,
        R::R12 => 12,
        R::R13 => 13,
        R::R14 => 14,
        R::R15 => 15,
        _ => bail!("register {r:?} is not a general-purpose register of the model"),
    };
    Ok(Reg::ALL[i])
}

/// The memory operand of an instruction.
pub fn mem(ins: &Instruction) -> Result<Mem> {
    let next = ins.next_ip();
    let seg = ins.segment_prefix();
    let index = match ins.memory_index() {
        Register::None => None,
        r => {
            let reg = gpr(r)?;
            ensure!(reg != Reg::Rsp, "RSP cannot be an index");
            let scale = match ins.memory_index_scale() {
                1 => 0,
                2 => 1,
                4 => 2,
                8 => 3,
                s => bail!("bad scale {s}"),
            };
            Some(Index { reg, scale })
        }
    };
    let disp64 = ins.memory_displacement64();
    let (base, disp) = match ins.memory_base() {
        Register::RIP => {
            ensure!(index.is_none(), "RIP-relative operand with an index");
            (Base::Rip, disp64.wrapping_sub(next) as u32)
        }
        Register::EIP => bail!("32-bit address size (EIP-relative) is not in the model"),
        Register::None if seg == Register::FS => (Base::Fs, disp64 as u32),
        Register::None => (Base::None, disp64 as u32),
        r => {
            ensure!(
                r.is_gpr64(),
                "address-size override ({r:?} base) is not in the model"
            );
            (Base::Reg(gpr(r)?), disp64 as u32)
        }
    };
    if ins.memory_index() != Register::None {
        ensure!(
            ins.memory_index().is_gpr64(),
            "32-bit index register is not in the model"
        );
    }
    match seg {
        Register::None => {}
        Register::FS => ensure!(
            base == Base::Fs,
            "fs: override with a base register is not in the model"
        ),
        s => bail!("segment override {s:?} is not in the model"),
    }
    Ok(Mem { base, index, disp })
}

/// Operand `i` as an r/m.
pub fn rm(ins: &Instruction, i: u32) -> Result<RM> {
    Ok(match ins.op_kind(i) {
        OpKind::Register => RM::Reg(gpr(ins.op_register(i))?),
        OpKind::Memory => RM::Mem(mem(ins)?),
        k => bail!("operand {i} is {k:?}, expected r/m"),
    })
}

/// Operand `i` as a register.
pub fn reg(ins: &Instruction, i: u32) -> Result<Reg> {
    ensure!(
        ins.op_kind(i) == OpKind::Register,
        "operand {i} is not a register"
    );
    gpr(ins.op_register(i))
}

fn memop(ins: &Instruction, i: u32) -> Result<Mem> {
    ensure!(
        ins.op_kind(i) == OpKind::Memory,
        "operand {i} is not memory"
    );
    mem(ins)
}

/// Immediate operand `i`.
pub fn imm(ins: &Instruction, i: u32) -> u64 {
    ins.immediate(i)
}

/// The operand size named by an iced form fragment.
pub fn sz(form: &str) -> Result<Sz> {
    let digits: String = form.chars().filter(|c| c.is_ascii_digit()).collect();
    match digits.as_str() {
        "32" => Ok(Sz::D),
        "64" => Ok(Sz::Q),
        _ => bail!("operand size `{form}` is not 32 or 64 bits"),
    }
}

/// A condition-code suffix.
pub fn cond(s: &str) -> Option<Cond> {
    use Cond::*;
    Some(match s {
        "o" => O,
        "no" => No,
        "b" => B,
        "ae" => Ae,
        "e" => E,
        "ne" => Ne,
        "be" => Be,
        "a" => A,
        "s" => S,
        "ns" => Ns,
        "p" => P,
        "np" => Np,
        "l" => L,
        "ge" => Ge,
        "le" => Le,
        "g" => G,
        _ => return None,
    })
}

/// An ALU mnemonic.
pub fn alu(s: &str) -> Option<AluOp> {
    Some(match s {
        "add" => AluOp::Add,
        "or" => AluOp::Or,
        "and" => AluOp::And,
        "sub" => AluOp::Sub,
        "xor" => AluOp::Xor,
        "cmp" => AluOp::Cmp,
        _ => return None,
    })
}

fn shift(s: &str) -> Option<ShiftOp> {
    Some(match s {
        "rol" => ShiftOp::Rol,
        "ror" => ShiftOp::Ror,
        "shl" => ShiftOp::Shl,
        "shr" => ShiftOp::Shr,
        "sar" => ShiftOp::Sar,
        _ => return None,
    })
}

/// The branch displacement.
pub fn rel(ins: &Instruction) -> u64 {
    ins.near_branch_target().wrapping_sub(ins.next_ip())
}

/// Map one decoded instruction. The error names iced's form when the model has
/// no counterpart.
pub fn map(ins: &Instruction) -> Result<Instr> {
    let code = format!("{:?}", ins.code());
    let mut parts = code.split('_');
    let mn = parts.next().unwrap_or("").to_ascii_lowercase();
    let ops: Vec<&str> = parts.collect();
    let unsupported = || anyhow!("`{code}` is not in the Ext model");
    use Instr::*;
    let out = match (mn.as_str(), ops.as_slice()) {
        // ALU
        (m, [a, b]) if alu(m).is_some() => {
            let op = alu(m).unwrap();
            match (*a, *b) {
                ("rm8", "imm8") if op == AluOp::Cmp => CmpI8(rm(ins, 0)?, imm(ins, 1) as u8),
                ("AL", "imm8") if op == AluOp::Cmp => CmpA8(imm(ins, 1) as u8),
                ("rm32" | "rm64", "r32" | "r64") => Alu(sz(a)?, op, rm(ins, 0)?, reg(ins, 1)?),
                ("r32" | "r64", "rm32" | "rm64") => AluR(sz(a)?, op, reg(ins, 0)?, rm(ins, 1)?),
                ("rm32" | "rm64", "imm32") => AluI(sz(a)?, op, rm(ins, 0)?, imm(ins, 1) as u32),
                ("rm32" | "rm64", "imm8") => AluI8(sz(a)?, op, rm(ins, 0)?, imm(ins, 1) as u8),
                ("EAX", "imm32") => AluA(Sz::D, op, imm(ins, 1) as u32),
                ("RAX", "imm32") => AluA(Sz::Q, op, imm(ins, 1) as u32),
                _ => return Err(unsupported()),
            }
        }
        // MOV and friends
        ("mov", [a, b]) => match (*a, *b) {
            ("rm8", "r8") => Store(Narrow::B, rm(ins, 0)?, reg(ins, 1)?),
            ("rm16", "r16") => Store(Narrow::W, rm(ins, 0)?, reg(ins, 1)?),
            ("rm32", "r32") | ("rm64", "r64") => Mov(sz(a)?, rm(ins, 0)?, reg(ins, 1)?),
            ("r8", "rm8") => Mov8(reg(ins, 0)?, rm(ins, 1)?),
            ("r32", "rm32") | ("r64", "rm64") => {
                if ins.op_kind(1) != OpKind::Memory {
                    bail!("`{code}` with a register source (8B /r, mod = 11) is not in the model");
                }
                Load(sz(a)?, reg(ins, 0)?, memop(ins, 1)?)
            }
            ("rm8", "imm8") => MovI8(rm(ins, 0)?, imm(ins, 1) as u8),
            ("rm16", "imm16") => MovI16(rm(ins, 0)?, imm(ins, 1) as u16),
            ("rm32", "imm32") | ("rm64", "imm32") => MovI(sz(a)?, rm(ins, 0)?, imm(ins, 1) as u32),
            ("r32", "imm32") => MovI32(reg(ins, 0)?, imm(ins, 1) as u32),
            ("r64", "imm64") => Movabs(reg(ins, 0)?, imm(ins, 1)),
            _ => return Err(unsupported()),
        },
        ("movzx" | "movsx", [a, b]) => {
            let n = match *b {
                "rm8" => Narrow::B,
                "rm16" => Narrow::W,
                _ => return Err(unsupported()),
            };
            Movx(mn == "movsx", sz(a)?, n, reg(ins, 0)?, rm(ins, 1)?)
        }
        ("movsxd", ["r64", "rm32"]) => Movsxd(reg(ins, 0)?, rm(ins, 1)?),
        ("lea", [a @ ("r32" | "r64"), "m"]) => Lea(sz(a)?, reg(ins, 0)?, memop(ins, 1)?),
        ("test", [a, b]) => match (*a, *b) {
            ("rm8", "r8") => Test8(rm(ins, 0)?, reg(ins, 1)?),
            ("rm8", "imm8") => TestI8(rm(ins, 0)?, imm(ins, 1) as u8),
            ("AL", "imm8") => TestA8(imm(ins, 1) as u8),
            ("rm32" | "rm64", "r32" | "r64") => Test(sz(a)?, rm(ins, 0)?, reg(ins, 1)?),
            ("EAX", "imm32") => TestA(Sz::D, imm(ins, 1) as u32),
            ("RAX", "imm32") => TestA(Sz::Q, imm(ins, 1) as u32),
            _ => return Err(unsupported()),
        },
        ("inc" | "dec", [a @ ("rm32" | "rm64")]) => Incdec(sz(a)?, mn == "dec", rm(ins, 0)?),
        ("push", ["rm64"]) => PushRM(rm(ins, 0)?),
        ("push", ["r64"]) => Push(reg(ins, 0)?),
        ("pop", ["r64"]) => Pop(reg(ins, 0)?),
        ("bswap", [a @ ("r32" | "r64")]) => Bswap(sz(a)?, reg(ins, 0)?),
        ("neg", [a @ ("rm32" | "rm64")]) => Unary(sz(a)?, UnOp::Neg, rm(ins, 0)?),
        ("not", [a @ ("rm32" | "rm64")]) => Unary(sz(a)?, UnOp::Not, rm(ins, 0)?),
        ("imul", [a @ ("r32" | "r64"), "rm32" | "rm64"]) => Imul(sz(a)?, reg(ins, 0)?, rm(ins, 1)?),
        (m, [a @ ("rm32" | "rm64"), c]) if shift(m).is_some() => {
            let count = match *c {
                "CL" => Count::Cl,
                "1" => Count::One,
                "imm8" => Count::Imm(imm(ins, 1) as u8),
                _ => return Err(unsupported()),
            };
            Shift(sz(a)?, shift(m).unwrap(), rm(ins, 0)?, count)
        }
        ("cdq", []) => Cxd(Sz::D),
        ("cqo", []) => Cxd(Sz::Q),
        ("cwde", []) => Cxe(Sz::D),
        ("cdqe", []) => Cxe(Sz::Q),
        ("mul", [a @ ("rm32" | "rm64")]) => Mul(sz(a)?, rm(ins, 0)?),
        ("div" | "idiv", [a @ ("rm32" | "rm64")]) => Div(sz(a)?, mn == "idiv", rm(ins, 0)?),
        (m, ["rm8"]) if m.starts_with("set") && cond(&m[3..]).is_some() => {
            Setcc(cond(&m[3..]).unwrap(), rm(ins, 0)?)
        }
        (m, [a @ ("r32" | "r64"), "rm32" | "rm64"])
            if m.starts_with("cmov") && cond(&m[4..]).is_some() =>
        {
            Cmov(sz(a)?, cond(&m[4..]).unwrap(), reg(ins, 0)?, rm(ins, 1)?)
        }
        ("jmp", ["rel32", "64"]) => Jmp(rel(ins) as u32),
        ("jmp", ["rel8", "64"]) => Jmp8(rel(ins) as u8),
        (m, ["rel32", "64"]) if m.starts_with('j') && cond(&m[1..]).is_some() => {
            Jcc(cond(&m[1..]).unwrap(), rel(ins) as u32)
        }
        (m, ["rel8", "64"]) if m.starts_with('j') && cond(&m[1..]).is_some() => {
            Jcc8(cond(&m[1..]).unwrap(), rel(ins) as u8)
        }
        ("call", ["rel32", "64"]) => Call(rel(ins) as u32),
        ("retnq", []) => Ret,
        ("leaveq", []) => Leave,
        ("endbr64", []) => Endbr64,
        ("ud2", []) => Ud2,
        (m, _) if m.starts_with("nop") => {
            let len = ins.len();
            ensure!((1..=15).contains(&len), "NOP of length {len}");
            Nop((len - 1) as u8)
        }
        ("lzcnt" | "tzcnt" | "popcnt", [a @ ("r32" | "r64"), "rm32" | "rm64"]) => {
            let op = match mn.as_str() {
                "lzcnt" => BitCountOp::Lzcnt,
                "tzcnt" => BitCountOp::Tzcnt,
                _ => BitCountOp::Popcnt,
            };
            Bitcount(op, sz(a)?, reg(ins, 0)?, rm(ins, 1)?)
        }
        _ => return Err(unsupported()),
    };
    Ok(out)
}
