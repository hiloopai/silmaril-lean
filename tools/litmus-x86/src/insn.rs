//! The instruction subset of the corpus: a small IR, parsers for herd's two x86 dialects,
//! and the canonical gas (AT&T) text that the assembler turns into bytes.
//!
//! Every cell of a program table is parsed into an [`Insn`]; the bytes are assembled from
//! [`Insn::gas`], never from the cell text, so the checker's reading of an instruction and
//! the assembled bytes come from the same IR value. Memory operands name a location plus a
//! constant byte offset (`(x)`, `(x+4)`, `[x]`); the layout turns them into absolute
//! 32-bit addresses (ModRM + SIB with no base and no index, so no relocations).

use std::collections::BTreeMap;

use crate::litmus::{Arch, Error};

/// A general-purpose register, numbered as in the hardware encoding (System V names).
pub const GPR64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const GPR32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const GPR16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
const GPR8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];

/// A register operand: hardware number and width in bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reg {
    pub num: u8,
    pub size: u64,
}

impl Reg {
    /// Parse a register name (any case, with or without `%`).
    pub fn parse(s: &str) -> Option<Reg> {
        let l = s.trim().trim_start_matches('%').to_ascii_lowercase();
        for (size, table) in [(8, &GPR64), (4, &GPR32), (2, &GPR16), (1, &GPR8)] {
            if let Some(i) = table.iter().position(|r| *r == l) {
                return Some(Reg { num: i as u8, size });
            }
        }
        None
    }

    /// The AT&T name.
    pub fn att(self) -> String {
        let t = match self.size {
            8 => &GPR64,
            4 => &GPR32,
            2 => &GPR16,
            _ => &GPR8,
        };
        format!("%{}", t[self.num as usize])
    }
}

/// A memory operand: a location and a byte offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemRef {
    pub loc: String,
    pub off: u64,
}

/// A source operand of a store or ALU instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Src {
    Imm(i64),
    Reg(Reg),
}

/// Locked ALU operations with an immediate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Alu {
    Add,
    Or,
    And,
    Sub,
    Xor,
}

impl Alu {
    fn name(self) -> &'static str {
        match self {
            Alu::Add => "add",
            Alu::Or => "or",
            Alu::And => "and",
            Alu::Sub => "sub",
            Alu::Xor => "xor",
        }
    }
    /// Apply the operation.
    pub fn apply(self, a: u64, b: u64) -> u64 {
        match self {
            Alu::Add => a.wrapping_add(b),
            Alu::Or => a | b,
            Alu::And => a & b,
            Alu::Sub => a.wrapping_sub(b),
            Alu::Xor => a ^ b,
        }
    }
}

/// A fence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fence {
    M,
    L,
    S,
}

/// An instruction of the corpus subset. `size` is the access width in bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Insn {
    /// `mov reg, imm`.
    MovRI { dst: Reg, imm: i64 },
    /// `mov reg, reg`.
    MovRR { dst: Reg, src: Reg },
    /// A load `mov reg, [m]`.
    Load { dst: Reg, mem: MemRef },
    /// A store `mov [m], src`.
    Store { size: u64, mem: MemRef, src: Src },
    /// `mfence`, `lfence`, `sfence`.
    Fence(Fence),
    /// `xchg [m], reg` (implicitly locked).
    Xchg { mem: MemRef, reg: Reg },
    /// `[lock] xadd [m], reg`.
    Xadd { lock: bool, mem: MemRef, reg: Reg },
    /// `[lock] cmpxchg [m], reg` (compares with the accumulator of the same width).
    Cmpxchg { lock: bool, mem: MemRef, reg: Reg },
    /// `[lock] op [m], imm`.
    AluMI {
        lock: bool,
        op: Alu,
        size: u64,
        mem: MemRef,
        imm: i64,
    },
    /// `[lock] inc/dec [m]`.
    IncDec {
        lock: bool,
        dec: bool,
        size: u64,
        mem: MemRef,
    },
    /// `movnti [m], reg` (non-temporal store; 4 or 8 bytes).
    Movnti { mem: MemRef, reg: Reg },
    /// `rep stosb` (stores `al` to `[rdi]`, `rcx` times).
    RepStosb,
    /// `lea disp(base), dst`: register arithmetic only, no memory access. Not in the herd
    /// corpus; it comes from compiled code (`c11` mode, `src/ingest.rs`).
    Lea { dst: Reg, base: Reg, disp: i64 },
}

/// The kind of a memory event, as `Silmaril.X86.MemEvent.Kind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvKind {
    Load,
    Store,
    Rmw,
    Fence(Fence),
}

/// A memory event in the shape of `Silmaril.X86.MemEvent.Event`: kind, first byte
/// address, size in bytes (`0` for fences) and the `locked` tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemEv {
    pub kind: EvKind,
    pub addr: u64,
    pub size: u64,
    pub locked: bool,
}

fn suffix(size: u64) -> &'static str {
    match size {
        1 => "b",
        2 => "w",
        4 => "l",
        _ => "q",
    }
}

impl Insn {
    /// Canonical AT&T text, with memory operands resolved to absolute addresses.
    pub fn gas(&self, addr: &BTreeMap<String, u64>) -> Result<String, Error> {
        let m = |r: &MemRef| -> Result<String, Error> {
            let base = addr
                .get(&r.loc)
                .ok_or_else(|| Error(format!("unknown location `{}`", r.loc)))?;
            Ok(format!("0x{:x}", base + r.off))
        };
        let lk = |l: bool| if l { "lock " } else { "" };
        Ok(match self {
            Insn::MovRI { dst, imm } => format!("mov{} ${imm}, {}", suffix(dst.size), dst.att()),
            Insn::MovRR { dst, src } => {
                format!("mov{} {}, {}", suffix(dst.size), src.att(), dst.att())
            }
            Insn::Load { dst, mem } => {
                format!("mov{} {}, {}", suffix(dst.size), m(mem)?, dst.att())
            }
            Insn::Store { size, mem, src } => match src {
                Src::Imm(i) => format!("mov{} ${i}, {}", suffix(*size), m(mem)?),
                Src::Reg(r) => format!("mov{} {}, {}", suffix(*size), r.att(), m(mem)?),
            },
            Insn::Fence(Fence::M) => "mfence".into(),
            Insn::Fence(Fence::L) => "lfence".into(),
            Insn::Fence(Fence::S) => "sfence".into(),
            Insn::Xchg { mem, reg } => {
                format!("xchg{} {}, {}", suffix(reg.size), reg.att(), m(mem)?)
            }
            Insn::Xadd { lock, mem, reg } => {
                format!(
                    "{}xadd{} {}, {}",
                    lk(*lock),
                    suffix(reg.size),
                    reg.att(),
                    m(mem)?
                )
            }
            Insn::Cmpxchg { lock, mem, reg } => {
                format!(
                    "{}cmpxchg{} {}, {}",
                    lk(*lock),
                    suffix(reg.size),
                    reg.att(),
                    m(mem)?
                )
            }
            Insn::AluMI {
                lock,
                op,
                size,
                mem,
                imm,
            } => {
                format!(
                    "{}{}{} ${imm}, {}",
                    lk(*lock),
                    op.name(),
                    suffix(*size),
                    m(mem)?
                )
            }
            Insn::IncDec {
                lock,
                dec,
                size,
                mem,
            } => {
                let o = if *dec { "dec" } else { "inc" };
                format!("{}{o}{} {}", lk(*lock), suffix(*size), m(mem)?)
            }
            Insn::Movnti { mem, reg } => {
                format!("movnti{} {}, {}", suffix(reg.size), reg.att(), m(mem)?)
            }
            Insn::RepStosb => "rep stosb %al, %es:(%rdi)".into(),
            Insn::Lea { dst, base, disp } => format!(
                "lea{} {disp}({}), {}",
                suffix(dst.size),
                Reg {
                    num: base.num,
                    size: 8
                }
                .att(),
                dst.att()
            ),
        })
    }

    /// The memory events of the instruction, computed from the IR in the shape of
    /// `MemEvent.atomic9Accesses` (one `rmw` event for a read-modify-write; `locked` for a
    /// `lock` prefix or `xchg` with memory; a fence is one size-0 event). `None` for forms that
    /// have no `MemEvent` counterpart today (`movnti`, `rep stosb`). The checker reads its
    /// events from this list, and the Lean corpus proves (by `decide`) that the assembled bytes
    /// decode to exactly these events, so the checked events are the bytes' events.
    pub fn events(&self, addr: &BTreeMap<String, u64>) -> Result<Option<Vec<MemEv>>, Error> {
        let a = |r: &MemRef| -> Result<u64, Error> {
            addr.get(&r.loc)
                .map(|b| b + r.off)
                .ok_or_else(|| Error(format!("unknown location `{}`", r.loc)))
        };
        let ev = |kind, r: &MemRef, size, locked| -> Result<Option<Vec<MemEv>>, Error> {
            Ok(Some(vec![MemEv {
                kind,
                addr: a(r)?,
                size,
                locked,
            }]))
        };
        match self {
            Insn::MovRI { .. } | Insn::MovRR { .. } | Insn::Lea { .. } => Ok(Some(vec![])),
            Insn::Load { dst, mem } => ev(EvKind::Load, mem, dst.size, false),
            Insn::Store { size, mem, .. } => ev(EvKind::Store, mem, *size, false),
            Insn::Fence(f) => Ok(Some(vec![MemEv {
                kind: EvKind::Fence(*f),
                addr: 0,
                size: 0,
                locked: false,
            }])),
            Insn::Xchg { mem, reg } => ev(EvKind::Rmw, mem, reg.size, true),
            Insn::Xadd { lock, mem, reg } | Insn::Cmpxchg { lock, mem, reg } => {
                ev(EvKind::Rmw, mem, reg.size, *lock)
            }
            Insn::AluMI {
                lock, size, mem, ..
            }
            | Insn::IncDec {
                lock, size, mem, ..
            } => ev(EvKind::Rmw, mem, *size, *lock),
            Insn::Movnti { .. } | Insn::RepStosb => Ok(None),
        }
    }

    /// The general-purpose registers the instruction may write (hardware numbers). The
    /// hardware harness observes these, plus the registers of the final condition.
    pub fn writes(&self) -> Vec<u8> {
        match self {
            Insn::MovRI { dst, .. }
            | Insn::MovRR { dst, .. }
            | Insn::Load { dst, .. }
            | Insn::Lea { dst, .. } => {
                vec![dst.num]
            }
            Insn::Xchg { reg, .. } | Insn::Xadd { reg, .. } => vec![reg.num],
            Insn::Cmpxchg { .. } => vec![0],
            Insn::RepStosb => vec![1, 7],
            Insn::Store { .. }
            | Insn::Fence(_)
            | Insn::AluMI { .. }
            | Insn::IncDec { .. }
            | Insn::Movnti { .. } => vec![],
        }
    }

    /// The memory operand, if any.
    pub fn mem(&self) -> Option<&MemRef> {
        match self {
            Insn::Load { mem, .. }
            | Insn::Store { mem, .. }
            | Insn::Xchg { mem, .. }
            | Insn::Xadd { mem, .. }
            | Insn::Cmpxchg { mem, .. }
            | Insn::AluMI { mem, .. }
            | Insn::IncDec { mem, .. }
            | Insn::Movnti { mem, .. } => Some(mem),
            _ => None,
        }
    }

    /// The width of the memory access in bytes (0 if none).
    pub fn mem_size(&self) -> u64 {
        match self {
            Insn::Load { dst, .. } => dst.size,
            Insn::Store { size, .. } | Insn::AluMI { size, .. } | Insn::IncDec { size, .. } => {
                *size
            }
            Insn::Xchg { reg, .. }
            | Insn::Xadd { reg, .. }
            | Insn::Cmpxchg { reg, .. }
            | Insn::Movnti { reg, .. } => reg.size,
            _ => 0,
        }
    }
}

fn err<T>(msg: impl Into<String>) -> Result<T, Error> {
    Err(Error(msg.into()))
}

/// Parse a memory operand body `x`, `x+4` (inside brackets or parentheses).
fn mem_body(s: &str) -> Result<MemRef, Error> {
    let s = s.trim();
    let (loc, off) = match s.split_once('+') {
        Some((l, o)) => (l.trim(), crate::litmus::parse_int(o)? as u64),
        None => (s, 0),
    };
    if loc.is_empty() || !loc.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return err(format!("bad memory operand `{s}`"));
    }
    Ok(MemRef {
        loc: loc.to_string(),
        off,
    })
}

/// Split operands at top-level commas.
fn operands(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let (mut depth, mut cur) = (0i32, String::new());
    for c in s.chars() {
        match c {
            '(' | '[' => {
                depth += 1;
                cur.push(c)
            }
            ')' | ']' => {
                depth -= 1;
                cur.push(c)
            }
            ',' if depth == 0 => out.push(std::mem::take(&mut cur)),
            _ => cur.push(c),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur);
    }
    out.into_iter().map(|o| o.trim().to_string()).collect()
}

#[derive(Debug)]
enum Op {
    Imm(i64),
    Reg(Reg),
    Mem(MemRef),
}

fn intel_op(s: &str) -> Result<Op, Error> {
    if let Some(i) = s.strip_prefix('$') {
        return Ok(Op::Imm(crate::litmus::parse_int(i)? as i64));
    }
    if let Some(b) = s.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
        return Ok(Op::Mem(mem_body(b)?));
    }
    if let Some(r) = Reg::parse(s) {
        return Ok(Op::Reg(r));
    }
    err(format!("bad operand `{s}`"))
}

fn att_op(s: &str) -> Result<Op, Error> {
    if let Some(i) = s.strip_prefix('$') {
        return Ok(Op::Imm(crate::litmus::parse_int(i)? as i64));
    }
    if let Some(b) = s.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        return Ok(Op::Mem(mem_body(b)?));
    }
    if let Some(r) = s.starts_with('%').then(|| Reg::parse(s)).flatten() {
        return Ok(Op::Reg(r));
    }
    err(format!("bad operand `{s}`"))
}

/// Strip an AT&T size suffix: the mnemonic stem and the size, if the full word is not
/// itself a known stem.
fn att_size(m: &str, stems: &[&str]) -> Option<(String, Option<u64>)> {
    if stems.contains(&m) {
        return Some((m.to_string(), None));
    }
    let (stem, sfx) = m.split_at(m.len().checked_sub(1)?);
    let size = match sfx {
        "b" => 1,
        "w" => 2,
        "l" => 4,
        "q" => 8,
        _ => return None,
    };
    stems
        .contains(&stem)
        .then(|| (stem.to_string(), Some(size)))
}

fn alu(stem: &str) -> Option<Alu> {
    Some(match stem {
        "add" => Alu::Add,
        "or" => Alu::Or,
        "and" => Alu::And,
        "sub" => Alu::Sub,
        "xor" => Alu::Xor,
        _ => return None,
    })
}

fn check_size(given: Option<u64>, reg: u64, cell: &str) -> Result<(), Error> {
    match given {
        Some(s) if s != reg => err(format!("size suffix disagrees with register in `{cell}`")),
        _ => Ok(()),
    }
}

/// Parse one program-table cell.
pub fn parse(arch: Arch, cell: &str) -> Result<Insn, Error> {
    let cell = cell.trim();
    let lower = cell.to_ascii_lowercase();
    let mut words = lower.split_whitespace().peekable();
    let mut lock = false;
    let mut rep = false;
    loop {
        match words.peek() {
            Some(&"lock") => lock = true,
            Some(&"rep") => rep = true,
            _ => break,
        }
        words.next();
    }
    let mnem = words
        .next()
        .ok_or_else(|| Error(format!("empty instruction `{cell}`")))?;
    let rest_start = cell.to_ascii_lowercase().find(mnem).unwrap_or(0) + mnem.len();
    let ops = operands(&cell[rest_start..]);
    let stems = [
        "mov", "xchg", "xadd", "cmpxchg", "add", "or", "and", "sub", "xor", "inc", "dec", "movnti",
        "mfence", "lfence", "sfence", "stosb",
    ];
    let (stem, size) = match arch {
        Arch::X86 => (mnem.to_string(), None),
        Arch::X86_64 => {
            att_size(mnem, &stems).ok_or_else(|| Error(format!("unsupported mnemonic `{mnem}`")))?
        }
    };
    // Operands in (destination, source) order.
    let parsed: Vec<Op> = match arch {
        Arch::X86 => ops.iter().map(|o| intel_op(o)).collect::<Result<_, _>>()?,
        Arch::X86_64 => {
            let mut v: Vec<Op> = ops.iter().map(|o| att_op(o)).collect::<Result<_, _>>()?;
            v.reverse();
            v
        }
    };
    if rep && stem != "stosb" {
        return err(format!("`rep` is only supported on stosb: `{cell}`"));
    }
    let locked_ok = matches!(
        stem.as_str(),
        "xchg" | "xadd" | "cmpxchg" | "add" | "or" | "and" | "sub" | "xor" | "inc" | "dec"
    );
    if lock && !locked_ok {
        return err(format!("`lock` is not allowed on `{cell}`"));
    }
    let default = |s: Option<u64>| s.unwrap_or(4);
    let insn = match (stem.as_str(), parsed.as_slice()) {
        ("mfence", []) => Insn::Fence(Fence::M),
        ("lfence", []) => Insn::Fence(Fence::L),
        ("sfence", []) => Insn::Fence(Fence::S),
        ("stosb", []) if rep => Insn::RepStosb,
        ("mov", [Op::Reg(d), Op::Imm(i)]) => {
            check_size(size, d.size, cell)?;
            Insn::MovRI { dst: *d, imm: *i }
        }
        ("mov", [Op::Reg(d), Op::Reg(s)]) if d.size == s.size => {
            check_size(size, d.size, cell)?;
            Insn::MovRR { dst: *d, src: *s }
        }
        ("mov", [Op::Reg(d), Op::Mem(m)]) => {
            check_size(size, d.size, cell)?;
            Insn::Load {
                dst: *d,
                mem: m.clone(),
            }
        }
        ("mov", [Op::Mem(m), Op::Imm(i)]) => Insn::Store {
            size: default(size),
            mem: m.clone(),
            src: Src::Imm(*i),
        },
        ("mov", [Op::Mem(m), Op::Reg(r)]) => {
            check_size(size, r.size, cell)?;
            Insn::Store {
                size: r.size,
                mem: m.clone(),
                src: Src::Reg(*r),
            }
        }
        ("xchg", [Op::Mem(m), Op::Reg(r)]) | ("xchg", [Op::Reg(r), Op::Mem(m)]) => {
            check_size(size, r.size, cell)?;
            Insn::Xchg {
                mem: m.clone(),
                reg: *r,
            }
        }
        ("xadd", [Op::Mem(m), Op::Reg(r)]) => {
            check_size(size, r.size, cell)?;
            Insn::Xadd {
                lock,
                mem: m.clone(),
                reg: *r,
            }
        }
        ("cmpxchg", [Op::Mem(m), Op::Reg(r)]) => {
            check_size(size, r.size, cell)?;
            Insn::Cmpxchg {
                lock,
                mem: m.clone(),
                reg: *r,
            }
        }
        ("movnti", [Op::Mem(m), Op::Reg(r)]) if r.size >= 4 => {
            check_size(size, r.size, cell)?;
            Insn::Movnti {
                mem: m.clone(),
                reg: *r,
            }
        }
        ("inc" | "dec", [Op::Mem(m)]) => Insn::IncDec {
            lock,
            dec: stem == "dec",
            size: default(size),
            mem: m.clone(),
        },
        (s, [Op::Mem(m), Op::Imm(i)]) if alu(s).is_some() => Insn::AluMI {
            lock,
            op: alu(s).unwrap_or(Alu::Add),
            size: default(size),
            mem: m.clone(),
            imm: *i,
        },
        _ => return err(format!("unsupported instruction `{cell}`")),
    };
    Ok(insn)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn addrs() -> BTreeMap<String, u64> {
        [("x".to_string(), 0x10000u64), ("y".to_string(), 0x10040)]
            .into_iter()
            .collect()
    }

    #[test]
    fn memory_events() {
        let a = addrs();
        let ev = |arch, cell: &str| parse(arch, cell).unwrap().events(&a).unwrap();
        let one = |kind, addr, size, locked| {
            Some(vec![MemEv {
                kind,
                addr,
                size,
                locked,
            }])
        };
        assert_eq!(
            ev(Arch::X86_64, "lock xaddl %eax,(y)"),
            one(EvKind::Rmw, 0x10040, 4, true)
        );
        assert_eq!(
            ev(Arch::X86_64, "xaddl %eax,(y)"),
            one(EvKind::Rmw, 0x10040, 4, false)
        );
        assert_eq!(
            ev(Arch::X86, "XCHG [x],EAX"),
            one(EvKind::Rmw, 0x10000, 4, true)
        );
        assert_eq!(
            ev(Arch::X86_64, "incl (x)"),
            one(EvKind::Rmw, 0x10000, 4, false)
        );
        assert_eq!(
            ev(Arch::X86_64, "movl (x+4),%ebx"),
            one(EvKind::Load, 0x10004, 4, false)
        );
        assert_eq!(
            ev(Arch::X86, "MFENCE"),
            one(EvKind::Fence(Fence::M), 0, 0, false)
        );
        assert_eq!(ev(Arch::X86, "MOV EAX,$1"), Some(vec![]));
        assert_eq!(ev(Arch::X86_64, "movnti %eax,(x)"), None);
        assert_eq!(ev(Arch::X86_64, "rep stosb"), None);
    }

    #[test]
    fn intel_forms() {
        let a = addrs();
        let i = parse(Arch::X86, "MOV [x],$1").unwrap();
        assert_eq!(i.gas(&a).unwrap(), "movl $1, 0x10000");
        let i = parse(Arch::X86, "MOV EAX,[y]").unwrap();
        assert_eq!(i.gas(&a).unwrap(), "movl 0x10040, %eax");
        assert_eq!(parse(Arch::X86, "MFENCE").unwrap(), Insn::Fence(Fence::M));
        let i = parse(Arch::X86, "XCHG [x],EAX").unwrap();
        assert_eq!(i.gas(&a).unwrap(), "xchgl %eax, 0x10000");
    }

    #[test]
    fn att_forms() {
        let a = addrs();
        let g = |s: &str| parse(Arch::X86_64, s).unwrap().gas(&a).unwrap();
        assert_eq!(g("movb $2,(x)"), "movb $2, 0x10000");
        assert_eq!(g("movq $-1,(x+4)"), "movq $-1, 0x10004");
        assert_eq!(g("mov (y),%eax"), "movl 0x10040, %eax");
        assert_eq!(g("xchgl (y),%eax"), "xchgl %eax, 0x10040");
        assert_eq!(g("lock xaddl %eax,(x)"), "lock xaddl %eax, 0x10000");
        assert_eq!(g("lock cmpxchgl %ecx,(x)"), "lock cmpxchgl %ecx, 0x10000");
        assert_eq!(g("lock addl $0,(y)"), "lock addl $0, 0x10040");
        assert_eq!(g("lock incl (x)"), "lock incl 0x10000");
        assert_eq!(g("movnti %eax,(x)"), "movntil %eax, 0x10000");
        assert_eq!(g("rep stosb"), "rep stosb %al, %es:(%rdi)");
        assert_eq!(g("movl $2,%eax"), "movl $2, %eax");
    }

    #[test]
    fn rejects() {
        assert!(parse(Arch::X86_64, "movl (x),%al").is_err());
        assert!(parse(Arch::X86_64, "lock movl $1,(x)").is_err());
        assert!(parse(Arch::X86_64, "rep movsb").is_err());
        assert!(parse(Arch::X86_64, "jmp L0").is_err());
        assert!(parse(Arch::X86, "MOV [x],[y]").is_err());
    }
}
