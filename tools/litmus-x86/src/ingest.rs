//! Ingesting thread functions from a compiled ELF object into the litmus corpus form.
//!
//! Given a relocatable object and its C11 specification (`src/cspec.rs`):
//!
//! 1. **Data.** Every defined data object (`STT_OBJECT`) must be a location of the
//!    specification, and every location must be defined. Locations are placed on the fixed
//!    data page exactly as the herd corpus places them (`model::BASE`, one 64-byte slot each,
//!    in specification order). Initial values come from the object (`.bss` is zero). Data
//!    sections with relocations (pointer initialisers) are rejected.
//! 2. **Code.** Thread `k`'s function is copied out of its section and relocated to
//!    `CODE_BASE + CODE_STRIDE * k` (the Lean `Litmus` layout's `codeBase k`). Only
//!    `R_X86_64_PC32`/`PLT32` relocations against the data objects are accepted; their value
//!    is `S + A - P` with `S` the data page address and `P` the fixed code address.
//! 3. **Disassembly.** The relocated bytes are disassembled with GNU `objdump` (binary input
//!    at the fixed address). The function must end in its only `ret`, which is dropped (a
//!    litmus thread ends when `rip` reaches the end of its bytes), and contain no other
//!    control transfer.
//! 4. **Lifting.** Each instruction is read into the corpus IR (`src/insn.rs`). A
//!    `disp(%rip)` operand is resolved to the location containing its target; a `disp(%rsp)`
//!    operand (the compilers' `lock or $0, (%rsp)` fence idiom) becomes a thread-private
//!    stack slot, a location the checker sees but the export does not. Every register an
//!    instruction reads must have been written earlier in the function, so the result does
//!    not depend on the harness's initial registers.
//! 5. **Model.** The IR program, the layout and the specification's final condition form a
//!    [`Model`], which `checker.rs` runs under SC and x86-TSO.
//!
//! The bytes in the output are the compiler's bytes after relocation, never re-assembled.
//! The IR is read from `objdump`'s text, so it is only as faithful as that reading; the Lean
//! side (`c11 cir`) is expected to decode the same bytes itself, as `Corpus.events_match`
//! does for the herd corpus. That cross-check is not done here.

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use crate::cspec::{AKind, Access, Mode, Role, Spec, Variant};
use crate::elf::{self, Object};
use crate::insn::{self, EvKind, Fence, Insn, Reg, Src};
use crate::litmus::{Arch, Error, Quant, parse_int};
use crate::model::{self, Atom, Cond, Loc, Model};

/// Code address of thread 0 (`Litmus.codeBase 0`).
pub const CODE_BASE: u64 = 0x40_0000;
/// Distance between threads' code (`Litmus.codeBase k = CODE_BASE + CODE_STRIDE * k`).
pub const CODE_STRIDE: u64 = 0x1000;
/// Synthetic addresses of the stack slots, for the checker only (never exported).
pub const STACK_BASE: u64 = 0x1_f000;

/// One machine instruction of a thread.
#[derive(Clone, Debug)]
pub struct MInsn {
    /// Offset from the thread's code base.
    pub off: u64,
    pub bytes: Vec<u8>,
    /// `objdump`'s AT&T text, comment removed, whitespace collapsed.
    pub asm: String,
    /// The text the IR was read from: `asm` with its memory operand named (`(x)`,
    /// `(sp0_m40)`).
    pub lifted: String,
    /// The lifted IR instruction.
    pub ir: Insn,
}

/// One ingested thread.
#[derive(Clone, Debug)]
pub struct IThread {
    pub func: String,
    pub code_base: u64,
    /// The section the function came from.
    pub section: String,
    /// The function's size in the object, including the final `ret`.
    pub size: u64,
    /// The instructions, without the final `ret`.
    pub insns: Vec<MInsn>,
    /// The relocations applied: (offset in the function, symbol, type, addend, value).
    pub relocs: Vec<(u64, String, u32, i64, i32)>,
}

/// An ingested object.
#[derive(Clone, Debug)]
pub struct Ingested {
    /// Data objects in specification order, with their source section: the first
    /// `layout.len()` locations of `model.locs`.
    pub layout: Vec<(Loc, String, Role)>,
    pub threads: Vec<IThread>,
    /// The checker's model: layout locations, then the stack slots.
    pub model: Model,
}

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

/// Registers an IR instruction reads (hardware numbers), for the def-before-use check.
fn reads(i: &Insn) -> Vec<u8> {
    match i {
        Insn::MovRR { src, .. } => vec![src.num],
        Insn::Store {
            src: Src::Reg(r), ..
        } => vec![r.num],
        Insn::Xchg { reg, .. } | Insn::Xadd { reg, .. } | Insn::Movnti { reg, .. } => {
            vec![reg.num]
        }
        Insn::Cmpxchg { reg, .. } => vec![reg.num, 0],
        Insn::Lea { base, .. } => vec![base.num],
        Insn::RepStosb => vec![0, 1, 7],
        _ => vec![],
    }
}

/// Parse `objdump -D -b binary -w` output into (address, bytes, text) rows.
fn parse_objdump(out: &str) -> Result<Vec<(u64, Vec<u8>, String)>, Error> {
    let mut rows = Vec::new();
    for line in out.lines() {
        let mut parts = line.split('\t');
        let (Some(a), Some(b), Some(t)) = (parts.next(), parts.next(), parts.next()) else {
            continue;
        };
        let Some(a) = a.trim().strip_suffix(':') else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(a, 16) else {
            continue;
        };
        let bytes = b
            .split_whitespace()
            .map(|h| u8::from_str_radix(h, 16).map_err(|_| Error(format!("bad byte `{h}`"))))
            .collect::<Result<Vec<_>, _>>()?;
        let text = t.split('#').next().unwrap_or("");
        let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
        rows.push((addr, bytes, text));
    }
    Ok(rows)
}

/// Disassemble `bytes` placed at `vma` with GNU objdump.
fn disassemble(
    objdump: &Path,
    bytes: &[u8],
    vma: u64,
    tmp: &Path,
) -> Result<Vec<(u64, Vec<u8>, String)>, Error> {
    let f = tmp.join(format!("code-{vma:x}.bin"));
    std::fs::write(&f, bytes).map_err(|e| Error(format!("{}: {e}", f.display())))?;
    let out = Command::new(objdump)
        .args(["-D", "-z", "-w", "-b", "binary", "-m", "i386:x86-64"])
        .arg(format!("--adjust-vma=0x{vma:x}"))
        .arg(&f)
        .output()
        .map_err(|e| Error(format!("{}: {e}", objdump.display())))?;
    let _ = std::fs::remove_file(&f);
    if !out.status.success() {
        return err(format!(
            "objdump failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    parse_objdump(&String::from_utf8_lossy(&out.stdout))
}

/// The memory operand of an AT&T operand list, if any: (start, end) byte range in `ops`.
fn mem_span(ops: &str) -> Option<(usize, usize)> {
    let close = ops.find(')')?;
    let open = ops[..close].rfind('(')?;
    // The displacement runs back to the previous comma or the start.
    let start = ops[..open].rfind(',').map_or(0, |c| c + 1);
    Some((start, close + 1))
}

/// Rewrite one instruction's memory operand to a named location (`(x+4)`), returning the
/// rewritten text and, for a stack operand, the slot's name.
fn rewrite_mem(
    text: &str,
    next: u64,
    layout: &[(Loc, String, Role)],
    thread: usize,
) -> Result<(String, Option<String>), Error> {
    let (mnem, ops) = match text.find(' ') {
        Some(_) if text.starts_with("lock ") => match text[5..].find(' ') {
            Some(j) => (&text[..5 + j], &text[5 + j + 1..]),
            None => (text, ""),
        },
        Some(i) => (&text[..i], &text[i + 1..]),
        None => (text, ""),
    };
    let Some((s, e)) = mem_span(ops) else {
        return Ok((text.to_string(), None));
    };
    let operand = ops[s..e].trim();
    let open = operand.find('(').unwrap_or(0);
    let disp = operand[..open].trim();
    let disp = if disp.is_empty() {
        0
    } else {
        parse_int(disp)? as i64
    };
    let inner = &operand[open + 1..operand.len() - 1];
    let (name, stack) = match inner {
        "%rip" => {
            let target = next.wrapping_add(disp as u64);
            let (l, _, _) = layout
                .iter()
                .find(|(l, _, _)| l.addr <= target && target < l.addr + l.size)
                .ok_or_else(|| {
                    Error(format!(
                        "`{text}`: rip-relative target 0x{target:x} is not a data object"
                    ))
                })?;
            let off = target - l.addr;
            (
                if off == 0 {
                    l.name.clone()
                } else {
                    format!("{}+{off}", l.name)
                },
                None,
            )
        }
        "%rsp" => {
            let n = if disp < 0 {
                format!("sp{thread}_m{:x}", -disp)
            } else {
                format!("sp{thread}_p{disp:x}")
            };
            (n.clone(), Some(n))
        }
        _ => return err(format!("`{text}`: unsupported memory operand `{operand}`")),
    };
    let new_ops = format!("{}({name}){}", &ops[..s], &ops[e..]);
    Ok((format!("{mnem} {new_ops}"), stack))
}

/// Lift one instruction's (rewritten) text.
fn lift(text: &str) -> Result<Insn, Error> {
    if let Some(ops) = text.strip_prefix("lea ") {
        // lea disp(%base),%dst
        let (m, d) = ops
            .rsplit_once(',')
            .ok_or_else(|| Error(format!("bad lea `{text}`")))?;
        let open = m
            .find('(')
            .ok_or_else(|| Error(format!("bad lea `{text}`")))?;
        let disp = if open == 0 {
            0
        } else {
            parse_int(&m[..open])? as i64
        };
        let base = Reg::parse(m[open + 1..].trim_end_matches(')'))
            .filter(|r| r.size == 8 && r.num != 4)
            .ok_or_else(|| Error(format!("unsupported lea `{text}`")))?;
        let dst = Reg::parse(d)
            .filter(|r| r.size >= 4)
            .ok_or_else(|| Error(format!("unsupported lea `{text}`")))?;
        return Ok(Insn::Lea { dst, base, disp });
    }
    insn::parse(Arch::X86_64, text).map_err(|e| Error(format!("cannot lift `{text}`: {}", e.0)))
}

fn is_control(text: &str) -> bool {
    let m = text.split(' ').next().unwrap_or("");
    m.starts_with('j')
        || m.starts_with("call")
        || m.starts_with("ret")
        || m.starts_with("loop")
        || m == "syscall"
        || m == "ud2"
        || m == "hlt"
}

/// Ingest the specification's thread functions from an object.
pub fn ingest(obj: &Object, spec: &Spec, objdump: &Path, tmp: &Path) -> Result<Ingested, Error> {
    // 1. Data.
    let objects: Vec<&elf::Symbol> = obj
        .symbols
        .iter()
        .filter(|s| s.kind == elf::STT_OBJECT && s.shndx != 0)
        .collect();
    for s in &objects {
        if !spec.locs.iter().any(|(n, _)| *n == s.name) {
            return err(format!(
                "data object `{}` is not a location of the specification",
                s.name
            ));
        }
    }
    let mut layout = Vec::new();
    let mut next = model::BASE;
    for (name, role) in &spec.locs {
        let s = obj
            .defined(name, elf::STT_OBJECT)
            .ok_or_else(|| Error(format!("location `{name}` is not defined in the object")))?;
        let sec_i = s.shndx as usize;
        let sec = obj
            .sections
            .get(sec_i)
            .ok_or_else(|| Error(format!("`{name}`: bad section index")))?;
        if sec.flags & (elf::SHF_ALLOC | elf::SHF_WRITE) != elf::SHF_ALLOC | elf::SHF_WRITE
            || sec.flags & elf::SHF_EXECINSTR != 0
        {
            return err(format!("`{name}` is not in a writable data section"));
        }
        if !obj.relas[sec_i].is_empty() {
            return err(format!("data section {} has relocations", sec.name));
        }
        if s.size == 0 || s.size > 8 {
            return err(format!("`{name}`: size {} not in 1..=8", s.size));
        }
        let init = match obj.section_bytes(sec_i)? {
            None => 0u128,
            Some(b) => b
                .get(s.value as usize..(s.value + s.size) as usize)
                .ok_or_else(|| Error(format!("`{name}` outside its section")))?
                .iter()
                .rev()
                .fold(0u128, |a, x| (a << 8) | u128::from(*x)),
        };
        layout.push((
            Loc {
                name: name.clone(),
                addr: next,
                size: s.size,
                init,
            },
            sec.name.clone(),
            *role,
        ));
        next += model::LINE;
    }
    let addr_of = |sym: &elf::Symbol| -> Option<u64> {
        (sym.kind == elf::STT_OBJECT)
            .then(|| layout.iter().find(|(l, _, _)| l.name == sym.name))
            .flatten()
            .map(|(l, _, _)| l.addr)
    };
    // 2–4. Code.
    let mut threads = Vec::new();
    let mut stack: Vec<(String, u64)> = Vec::new();
    for (k, (func, _)) in spec.threads.iter().enumerate() {
        let f = obj
            .defined(func, elf::STT_FUNC)
            .ok_or_else(|| Error(format!("function `{func}` is not defined")))?;
        let sec_i = f.shndx as usize;
        let sec = &obj.sections[sec_i];
        if sec.flags & elf::SHF_EXECINSTR == 0 || sec.kind != elf::SHT_PROGBITS {
            return err(format!("`{func}` is not in a code section"));
        }
        let all = obj.section_bytes(sec_i)?.unwrap_or(&[]);
        let mut code = all
            .get(f.value as usize..(f.value + f.size) as usize)
            .ok_or_else(|| Error(format!("`{func}` outside its section")))?
            .to_vec();
        if code.len() as u64 >= CODE_STRIDE {
            return err(format!("`{func}` is longer than one code slot"));
        }
        let base = CODE_BASE + CODE_STRIDE * k as u64;
        let mut relocs = Vec::new();
        for r in &obj.relas[sec_i] {
            if r.offset < f.value || r.offset >= f.value + f.size {
                continue;
            }
            let sym = &obj.symbols[r.sym];
            if r.kind != elf::R_X86_64_PC32 && r.kind != elf::R_X86_64_PLT32 {
                return err(format!(
                    "`{func}`: relocation type {} against `{}` is not supported",
                    r.kind, sym.name
                ));
            }
            let s = addr_of(sym).ok_or_else(|| {
                Error(format!(
                    "`{func}`: relocation against `{}`, which is not a data location (calls and section-relative references are not supported)",
                    sym.name
                ))
            })?;
            let off = r.offset - f.value;
            if off + 4 > code.len() as u64 {
                return err(format!("`{func}`: relocation past the function end"));
            }
            let p = base + off;
            let v = (s as i64) + r.addend - (p as i64);
            let v32 = i32::try_from(v)
                .map_err(|_| Error(format!("`{func}`: relocation overflows 32 bits")))?;
            code[off as usize..off as usize + 4].copy_from_slice(&v32.to_le_bytes());
            relocs.push((off, sym.name.clone(), r.kind, r.addend, v32));
        }
        let rows = disassemble(objdump, &code, base, tmp)?;
        let mut pos = base;
        let mut joined = Vec::new();
        for (a, b, _) in &rows {
            if *a != pos {
                return err(format!(
                    "`{func}`: objdump rows are not contiguous at 0x{a:x}"
                ));
            }
            pos += b.len() as u64;
            joined.extend_from_slice(b);
        }
        if joined != code {
            return err(format!("`{func}`: objdump bytes differ from the function"));
        }
        let Some((last, body)) = rows.split_last() else {
            return err(format!("`{func}` is empty"));
        };
        if last.1 != [0xc3] {
            return err(format!(
                "`{func}` does not end in `ret` (last: `{}`)",
                last.2
            ));
        }
        let mut insns = Vec::new();
        let mut defined = [false; 16];
        defined[4] = true;
        for (a, b, text) in body {
            if is_control(text) {
                return err(format!(
                    "`{func}`: control transfer `{text}` (only straight-line code is supported)"
                ));
            }
            let next_pc = a + b.len() as u64;
            // `lea` computes an address without accessing memory: no operand to resolve.
            let (rewritten, slot) = if text.starts_with("lea ") {
                (text.clone(), None)
            } else {
                rewrite_mem(text, next_pc, &layout, k)?
            };
            let ir = lift(&rewritten)?;
            if let Some(n) = slot {
                let size = ir.mem_size();
                match stack.iter().find(|(m, _)| *m == n) {
                    Some((_, s)) if *s != size => {
                        return err(format!("stack slot {n} used with two sizes"));
                    }
                    Some(_) => {}
                    None => stack.push((n, size)),
                }
            }
            for r in reads(&ir) {
                if !defined[r as usize] {
                    return err(format!(
                        "`{func}`: `{text}` reads {} before writing it",
                        insn::GPR64[r as usize]
                    ));
                }
            }
            for w in ir.writes() {
                if w == 4 {
                    return err(format!("`{func}`: `{text}` writes rsp"));
                }
                defined[w as usize] = true;
            }
            insns.push(MInsn {
                off: a - base,
                bytes: b.clone(),
                asm: text.clone(),
                lifted: rewritten,
                ir,
            });
        }
        threads.push(IThread {
            func: func.clone(),
            code_base: base,
            section: sec.name.clone(),
            size: f.size,
            insns,
            relocs,
        });
    }
    // 5. Model.
    let mut locs: Vec<Loc> = layout.iter().map(|(l, _, _)| l.clone()).collect();
    for (i, (n, size)) in stack.iter().enumerate() {
        locs.push(Loc {
            name: n.clone(),
            addr: STACK_BASE + model::LINE * i as u64,
            size: *size,
            init: 0,
        });
    }
    let mut cond = Cond::True;
    for (n, v) in spec.exists.iter().rev() {
        let l = locs.iter().find(|l| l.name == *n).expect("checked by Spec");
        let a = Cond::Atom(Atom::Mem {
            addr: l.addr,
            size: l.size,
            value: u128::from(*v) & ((1u128 << (8 * l.size)) - 1),
        });
        cond = match cond {
            Cond::True => a,
            c => Cond::And(Box::new(a), Box::new(c)),
        };
    }
    let model = Model {
        name: spec.name.clone(),
        doc: None,
        locs,
        threads: threads
            .iter()
            .map(|t| (t.insns.iter().map(|i| i.ir.clone()).collect(), Vec::new()))
            .collect(),
        quant: Quant::Exists,
        cond,
    };
    for (t, (insns, _)) in model.threads.iter().enumerate() {
        for i in insns {
            if let Some(m) = i.mem() {
                let l = model.loc(&m.loc).expect("named by rewrite_mem");
                if m.off + i.mem_size() > l.size {
                    return err(format!(
                        "thread {t}: access to {}+{} overruns the location",
                        m.loc, m.off
                    ));
                }
            }
        }
    }
    Ok(Ingested {
        layout,
        threads,
        model,
    })
}

/// A machine access slot used to match C accesses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotKind {
    R,
    W,
    /// `xchg` with a data location: the seq_cst store idiom.
    Swap,
    /// Another locked read-modify-write of a data location (`lock xadd/add/inc/cmpxchg`).
    LockedRmw,
    /// An unlocked read-modify-write (covers one plain load and one plain store).
    PlainRmw,
    /// `mfence`, or a locked RMW of a stack slot.
    Fence,
}

/// How one C access was compiled.
#[derive(Clone, Debug)]
pub struct Mapped {
    pub access: Access,
    /// Indices into the thread's instructions; empty if the access has no counterpart.
    pub insns: Vec<usize>,
    /// A short description of the x86 form ("xchg", "mov (store); mfence", ...).
    pub form: String,
    /// `false` if the counterpart was found only out of program order.
    pub in_order: bool,
}

/// The C-to-x86 access map of one thread.
#[derive(Clone, Debug)]
pub struct ThreadMap {
    pub accesses: Vec<Mapped>,
    /// Instructions with a memory access or fence that no C access accounts for.
    pub extra: Vec<usize>,
}

fn form_of(i: &Insn, stack: bool, asm: &str) -> String {
    let lk = |l: bool| if l { "lock " } else { "" };
    match i {
        Insn::Load { .. } => "mov (load)".into(),
        Insn::Store { .. } => "mov (store)".into(),
        Insn::Xchg { .. } => "xchg".into(),
        Insn::Xadd { lock, .. } => format!("{}xadd", lk(*lock)),
        Insn::Cmpxchg { lock, .. } => format!("{}cmpxchg", lk(*lock)),
        Insn::AluMI { .. } if stack => asm.to_string(),
        Insn::AluMI { lock, op, .. } => {
            let name = format!("{op:?}").to_ascii_lowercase();
            format!("{}{name}", lk(*lock))
        }
        Insn::IncDec { lock, dec, .. } => {
            format!("{}{}", lk(*lock), if *dec { "dec" } else { "inc" })
        }
        Insn::Fence(Fence::M) => "mfence".into(),
        Insn::Fence(Fence::L) => "lfence".into(),
        Insn::Fence(Fence::S) => "sfence".into(),
        Insn::Movnti { .. } => "movnti".into(),
        Insn::RepStosb => "rep stosb".into(),
        Insn::MovRI { .. } | Insn::MovRR { .. } | Insn::Lea { .. } => "(register)".into(),
    }
}

/// Match each thread's C11 accesses (under `variant`) with its machine accesses.
///
/// Atomic accesses (mode other than `na`) and fences must each have a counterpart, in program
/// order: a load a `mov` load of the same location; a store a `mov` store or an `xchg` of
/// it; an RMW another locked RMW of it (`lock xadd/add/inc/...`); a fence an `mfence` or a locked RMW of a stack
/// slot. Otherwise matching fails: the compiled code does not have the expected shape. Plain
/// accesses are matched when possible (a plain load and store may share one unlocked RMW
/// instruction) and are recorded as elided or out of order otherwise: the compilers may
/// merge, reorder or drop them. An `mfence`/stack RMW next to a seq_cst store or load that no
/// C fence accounts for becomes part of that access's form (the `mov; mfence` mapping).
///
/// Then: a seq_cst store must be an `xchg` or a `mov` followed by a fence (the
/// trailing-fence mapping, which is what makes a seq_cst load a plain `mov`); an atomic store
/// or `fetch_add` of a constant must write that constant (registers tracked through
/// `mov $imm`/`mov reg, reg`); and in an atomic variant every memory instruction must be
/// accounted for by a C access.
pub fn map_accesses(spec: &Spec, v: Variant, ing: &Ingested) -> Result<Vec<ThreadMap>, Error> {
    let m = &ing.model;
    let addrs = m.addrs();
    let nlayout = ing.layout.len();
    let mut out = Vec::new();
    for (t, th) in ing.threads.iter().enumerate() {
        // Slots: (insn index, kind, location name).
        let mut slots: Vec<(usize, SlotKind, Option<String>)> = Vec::new();
        for (i, mi) in th.insns.iter().enumerate() {
            let evs = mi
                .ir
                .events(&addrs)?
                .ok_or_else(|| Error(format!("`{}`: no event form", mi.asm)))?;
            for e in evs {
                let loc = m
                    .locs
                    .iter()
                    .position(|l| l.addr <= e.addr && e.addr < l.addr + l.size.max(1));
                let is_stack = loc.is_some_and(|p| p >= nlayout);
                let name = loc.map(|p| m.locs[p].name.clone());
                let k = match e.kind {
                    EvKind::Fence(Fence::M) => Some(SlotKind::Fence),
                    EvKind::Fence(_) => None,
                    EvKind::Rmw if is_stack && e.locked => Some(SlotKind::Fence),
                    _ if is_stack => {
                        return err(format!("`{}`: unexpected stack access", mi.asm));
                    }
                    EvKind::Load => Some(SlotKind::R),
                    EvKind::Store => Some(SlotKind::W),
                    EvKind::Rmw if matches!(mi.ir, Insn::Xchg { .. }) => Some(SlotKind::Swap),
                    EvKind::Rmw if e.locked => Some(SlotKind::LockedRmw),
                    EvKind::Rmw => Some(SlotKind::PlainRmw),
                };
                if let Some(k) = k {
                    slots.push((i, k, if k == SlotKind::Fence { None } else { name }));
                }
            }
        }
        // Per slot: used as a read, used as a write.
        let mut used = vec![(false, false); slots.len()];
        let mut cursor = 0usize;
        let mut mapped = Vec::new();
        for a in spec.accesses(t, v) {
            let fits = |s: &(usize, SlotKind, Option<String>),
                        u: (bool, bool)|
             -> Option<(bool, bool)> {
                let same = s.2.as_deref() == a.loc.as_deref();
                match (a.kind, s.1) {
                    (AKind::Fence, SlotKind::Fence) if !u.0 => Some((true, true)),
                    (AKind::Load, SlotKind::R) if same && !u.0 => Some((true, true)),
                    (AKind::Store, SlotKind::W) if same && !u.1 => Some((true, true)),
                    (AKind::Store, SlotKind::Swap) if same && !u.1 && a.mode != Mode::Na => {
                        Some((true, true))
                    }
                    (AKind::Rmw, SlotKind::LockedRmw) if same && !u.0 => Some((true, true)),
                    (AKind::Load, SlotKind::PlainRmw) if same && a.mode == Mode::Na && !u.0 => {
                        Some((true, u.1))
                    }
                    (AKind::Store, SlotKind::PlainRmw) if same && a.mode == Mode::Na && !u.1 => {
                        Some((u.0, true))
                    }
                    _ => None,
                }
            };
            let strict = a.mode != Mode::Na || a.kind == AKind::Fence;
            let mut hit = None;
            if a.result {
                hit = (0..slots.len()).find_map(|j| fits(&slots[j], used[j]).map(|u| (j, u)));
            } else {
                hit = (cursor..slots.len())
                    .find_map(|j| fits(&slots[j], used[j]).map(|u| (j, u)))
                    .or(hit);
            }
            let mut in_order = true;
            if hit.is_none() && !strict && !a.result {
                hit = (0..cursor).find_map(|j| fits(&slots[j], used[j]).map(|u| (j, u)));
                in_order = false;
            }
            match hit {
                Some((j, u)) => {
                    used[j] = u;
                    if !a.result && in_order {
                        cursor = j;
                    }
                    let i = slots[j].0;
                    mapped.push(Mapped {
                        access: a,
                        insns: vec![i],
                        form: String::new(),
                        in_order,
                    });
                }
                None if strict => {
                    return err(format!(
                        "thread {}: C access {} {} {} has no x86 counterpart in program order",
                        th.func,
                        a.kind.name(),
                        a.loc.as_deref().unwrap_or("-"),
                        a.mode.name()
                    ));
                }
                None => mapped.push(Mapped {
                    access: a,
                    insns: vec![],
                    form: "elided".into(),
                    in_order: true,
                }),
            }
        }
        // Unclaimed fences next to a seq_cst store (after) or load (before).
        for j in 0..slots.len() {
            if slots[j].1 != SlotKind::Fence || used[j].0 {
                continue;
            }
            let i = slots[j].0;
            let owner = mapped.iter_mut().find(|x| {
                x.access.mode == Mode::Sc
                    && ((x.access.kind == AKind::Store
                        && x.insns.last() == Some(&(i.wrapping_sub(1))))
                        || (x.access.kind == AKind::Load && x.insns.first() == Some(&(i + 1))))
            });
            if let Some(x) = owner {
                if x.access.kind == AKind::Store {
                    x.insns.push(i);
                } else {
                    x.insns.insert(0, i);
                }
                used[j] = (true, true);
            }
        }
        // Mode check: on x86-TSO a plain `mov` implements rlx/acq/rel loads and
        // stores, but a seq_cst store needs the store-side mapping both compilers use: an
        // `xchg`, or a `mov` followed by a fence (attached above). Without it the C11
        // seq_cst guarantee is lost (SB+sc with plain stores is TSO-allowed). The other
        // valid mapping (fence before every seq_cst load) is used by neither compiler and is
        // rejected here.
        for x in &mapped {
            if x.access.kind == AKind::Store && x.access.mode == Mode::Sc {
                let fenced = x.insns.iter().any(|&i| {
                    slots
                        .iter()
                        .any(|s| s.0 == i && matches!(s.1, SlotKind::Swap | SlotKind::Fence))
                });
                if !fenced {
                    return err(format!(
                        "thread {}: seq_cst store of {} is a plain store without a fence \
                         (needs xchg or mov; fence)",
                        th.func,
                        x.access.loc.as_deref().unwrap_or("-")
                    ));
                }
            }
        }
        // Value check: an atomic store of a constant, or an atomic `fetch_add` of a
        // constant, must write that constant. Registers are tracked through `mov $imm` and
        // `mov reg, reg`; anything else that writes a register makes it unknown, and an
        // unknown value is rejected.
        let mut consts: Vec<Option<i64>> = Vec::with_capacity(th.insns.len());
        let mut regs: BTreeMap<u8, i64> = BTreeMap::new();
        for mi in &th.insns {
            consts.push(match &mi.ir {
                Insn::Store {
                    src: Src::Imm(v), ..
                } => Some(*v),
                Insn::Store {
                    src: Src::Reg(r), ..
                }
                | Insn::Xchg { reg: r, .. }
                | Insn::Xadd { reg: r, .. } => regs.get(&r.num).copied(),
                Insn::AluMI {
                    op: crate::insn::Alu::Add,
                    imm,
                    ..
                } => Some(*imm),
                Insn::IncDec { dec: false, .. } => Some(1),
                _ => None,
            });
            match &mi.ir {
                Insn::MovRI { dst, imm } if dst.size >= 4 => {
                    regs.insert(dst.num, *imm);
                }
                Insn::MovRR { dst, src } if dst.size >= 4 && regs.contains_key(&src.num) => {
                    let v = regs[&src.num];
                    regs.insert(dst.num, v);
                }
                Insn::MovRI { dst, .. }
                | Insn::MovRR { dst, .. }
                | Insn::Load { dst, .. }
                | Insn::Lea { dst, .. } => {
                    regs.remove(&dst.num);
                }
                Insn::Xchg { reg, .. } | Insn::Xadd { reg, .. } => {
                    regs.remove(&reg.num);
                }
                Insn::Cmpxchg { .. } => {
                    regs.remove(&0);
                }
                Insn::RepStosb => {
                    regs.remove(&1);
                    regs.remove(&7);
                }
                _ => {}
            }
        }
        for x in &mapped {
            let (Some(want), Some(&i)) = (x.access.value, x.insns.first()) else {
                continue;
            };
            if x.access.mode == Mode::Na || x.access.result {
                continue;
            }
            let ok = match x.access.kind {
                AKind::Store => {
                    matches!(th.insns[i].ir, Insn::Store { .. } | Insn::Xchg { .. })
                        && consts[i] == Some(want)
                }
                AKind::Rmw => {
                    matches!(
                        th.insns[i].ir,
                        Insn::Xadd { .. } | Insn::AluMI { .. } | Insn::IncDec { .. }
                    ) && consts[i] == Some(want)
                }
                _ => true,
            };
            if !ok {
                return err(format!(
                    "thread {}: {} {} {} does not write the value {want} (`{}`)",
                    th.func,
                    x.access.kind.name(),
                    x.access.loc.as_deref().unwrap_or("-"),
                    x.access.mode.name(),
                    th.insns[i].asm
                ));
            }
        }
        for x in &mut mapped {
            if x.insns.is_empty() {
                continue;
            }
            let parts: Vec<String> = x
                .insns
                .iter()
                .map(|&i| {
                    let mi = &th.insns[i];
                    let stack = mi
                        .ir
                        .mem()
                        .is_some_and(|r| m.loc(&r.loc).is_some_and(|l| l.addr >= STACK_BASE));
                    form_of(&mi.ir, stack, &mi.asm)
                })
                .collect();
            x.form = parts.join("; ");
            if !x.in_order {
                x.form.push_str(" (out of order)");
            }
        }
        let mut extra: Vec<usize> = slots
            .iter()
            .zip(&used)
            .filter(|(s, u)| match s.1 {
                SlotKind::PlainRmw => !(u.0 && u.1),
                _ => !u.0,
            })
            .map(|(s, _)| s.0)
            .collect();
        extra.dedup();
        // In an atomic variant every memory instruction must be accounted for by a
        // C access (an unexplained store or RMW of a shared location would otherwise pass).
        if v != Variant::Na
            && let Some(&i) = extra.first()
        {
            return err(format!(
                "thread {}: `{}` is not accounted for by any C access",
                th.func, th.insns[i].asm
            ));
        }
        out.push(ThreadMap {
            accesses: mapped,
            extra,
        });
    }
    Ok(out)
}

/// The (store, load, RMW) mode names of a variant, for documentation.
pub fn variant_modes(v: Variant) -> [&'static str; 3] {
    let (a, b, c) = v.modes();
    [a.name(), b.name(), c.name()]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn layout() -> Vec<(Loc, String, Role)> {
        ["x", "y"]
            .iter()
            .enumerate()
            .map(|(i, n)| {
                (
                    Loc {
                        name: n.to_string(),
                        addr: model::BASE + 64 * i as u64,
                        size: 4,
                        init: 0,
                    },
                    ".bss".into(),
                    Role::Shared,
                )
            })
            .collect()
    }

    #[test]
    fn rewrite_and_lift() {
        let l = layout();
        // movl $1, x(%rip) at 0x400000, 10 bytes: disp = 0x10000 - 0x40000a.
        let d = 0x10000i64 - 0x40000a;
        let (t, s) = rewrite_mem(&format!("movl $0x1,{d}(%rip)"), 0x40000a, &l, 0).unwrap();
        assert_eq!((t.as_str(), s), ("movl $0x1,(x)", None));
        let (t, s) = rewrite_mem("lock orl $0x0,-0x40(%rsp)", 0, &l, 1).unwrap();
        assert_eq!(t, "lock orl $0x0,(sp1_m40)");
        assert_eq!(s.as_deref(), Some("sp1_m40"));
        let (t, _) = rewrite_mem("xchg %eax,0x3a(%rip)", 0x10040 - 0x3a + 2, &l, 0).unwrap();
        assert_eq!(t, "xchg %eax,(y+2)");
        assert!(rewrite_mem("mov (%rax),%eax", 0, &l, 0).is_err());
        assert!(matches!(
            lift("lea 0x1(%rax),%edx").unwrap(),
            Insn::Lea { disp: 1, .. }
        ));
        assert!(matches!(
            lift("lock xadd %eax,(x)").unwrap(),
            Insn::Xadd { lock: true, .. }
        ));
        assert!(matches!(
            lift("lock incl (x)").unwrap(),
            Insn::IncDec { lock: true, .. }
        ));
        assert!(matches!(lift("mov %eax,%edx").unwrap(), Insn::MovRR { .. }));
        assert!(is_control("jne 0x400010") && is_control("ret") && !is_control("mov %eax,(x)"));
    }

    #[test]
    fn objdump_rows() {
        let out = "\n  400000:\tc7 05 f6 ff c0 ff 01 00 00 00 \tmovl   $0x1,-0x3f000a(%rip)        # 0x10000\n  40000a:\tc3                   \tret\n";
        let r = parse_objdump(out).unwrap();
        assert_eq!(r.len(), 2);
        assert_eq!(r[0].0, 0x400000);
        assert_eq!(r[0].1.len(), 10);
        assert_eq!(r[0].2, "movl $0x1,-0x3f000a(%rip)");
        assert_eq!(r[1].2, "ret");
    }
}
