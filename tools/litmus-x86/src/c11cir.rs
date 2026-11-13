//! `c11cir`: the **untrusted** proposer that translation-validates
//! the compiled C11 litmus objects (`c11 ingest`) into CIR **with the C11 modes of their source**.
//!
//! Input: `export/c11.json` (per test: locations, the relocated thread bytes, the witness, the
//! x86 verdicts) and `export/c11-meta.json` (per thread: every C11 access with its mode and the
//! indices of the x86 instructions the `c11 ingest` matcher assigned it; the expected C11 verdict).
//!
//! Output: the Lean modules `Silmaril/X86/Concurrency/Cir/C11/Corpus/Defs.lean` (one
//! `Cir.C11.C11Test` per object) and `Silmaril/Proofs/X86/Concurrency/Cir/C11Corpus.lean` (one
//! kernel `decide` of `C11Test.check` per test). Every CIR statement comes from decoding the
//! instruction's **bytes** here; its mode is the mode of the C11 access the sidecar maps to that
//! instruction. Nothing is trusted: Lean's `tvRun` re-decodes the bytes and checks the
//! operations, `modesOk` checks the modes against the x86 mapping, and `C11Test.check` computes
//! the RC11 verdict.
//!
//! Choices:
//!
//! * A thread that uses its stack (`lock or $0, d(%rsp)`, the seq_cst fence idiom) gets a
//!   private 8-byte slot in the data page, at `0x10800 + 0x40 * k`, and `rsp = slot - d`. The slot
//!   is not a location of the test, which is what makes the locked `or` an SC fence in RC11.
//! * Instructions no C11 access accounts for, or accesses of the `na` variant, get mode `na`.
//! * `stronger` (x86 strictly stronger than RC11) is predicted from the hand-recorded C11
//!   verdict and the x86 TSO verdict; Lean checks it.
//!
//! Objects with a form outside the table (the unlocked `addl $1, m` of `Counter+na@gcc`) are
//! skipped and listed in the generated module.

use std::fmt::Write as _;

use crate::json::{self, Value};
use crate::litmus::Error;

const REGS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const SCRATCH: [u8; 8] = [11, 10, 9, 8, 15, 14, 13, 12];
const RSP: u8 = 4;
const SLOT_BASE: u64 = 0x10800;
const SLOT_STRIDE: u64 = 0x40;

/// A memory operand: RIP-relative (resolved to an absolute address) or `[rsp + disp]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Opd {
    Abs(u64),
    Rsp(i64),
}

/// A decoded instruction of the supported subset (sizes in bytes).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Insn {
    StoreR {
        size: u8,
        a: Opd,
        src: u8,
    },
    StoreI {
        size: u8,
        a: Opd,
        val: u64,
    },
    Load {
        size: u8,
        a: Opd,
        dst: u8,
    },
    Xchg {
        size: u8,
        a: Opd,
        src: u8,
    },
    Xadd {
        size: u8,
        a: Opd,
        src: u8,
    },
    LockAlu {
        size: u8,
        a: Opd,
        op: &'static str,
        val: u64,
    },
    LockInc {
        size: u8,
        a: Opd,
    },
    Inc {
        size: u8,
        a: Opd,
    },
    MovRI {
        dst: u8,
        val: u64,
    },
    MovRR {
        size: u8,
        dst: u8,
        src: u8,
    },
    Lea {
        size: u8,
        dst: u8,
        base: u8,
        disp: i64,
    },
}

fn err<T>(m: &str, bytes: &[u8]) -> Result<T, Error> {
    let h: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    Err(Error(format!("c11cir: {m} in {h}")))
}

fn le(b: &[u8], at: usize, n: usize) -> Option<u64> {
    let s = b.get(at..at + n)?;
    Some(s.iter().rev().fold(0u64, |a, &x| (a << 8) | u64::from(x)))
}

fn sext(v: u64, bits: u32) -> i64 {
    let sh = 64 - bits;
    ((v << sh) as i64) >> sh
}

/// Decode a ModRM memory operand at `at` (no REX.B/X): RIP-relative or `rsp`-based (SIB 0x24).
/// Returns the operand, the `reg` field and the length of ModRM + SIB + displacement.
fn modrm(b: &[u8], at: usize, next_of: &dyn Fn(usize) -> u64) -> Result<(Opd, u8, usize), Error> {
    let m = *b.get(at).ok_or_else(|| Error("c11cir: truncated".into()))?;
    let (md, reg, rm) = (m >> 6, (m >> 3) & 7, m & 7);
    match (md, rm) {
        (0, 5) => {
            let d = le(b, at + 1, 4).ok_or_else(|| Error("c11cir: truncated".into()))?;
            let len = 5;
            // the absolute address needs the instruction's full length; filled in by the caller
            Ok((
                Opd::Abs(next_of(at + len).wrapping_add(sext(d, 32) as u64)),
                reg,
                len,
            ))
        }
        (0, 4) if b.get(at + 1) == Some(&0x24) => Ok((Opd::Rsp(0), reg, 2)),
        (1, 4) if b.get(at + 1) == Some(&0x24) => {
            let d = *b
                .get(at + 2)
                .ok_or_else(|| Error("c11cir: truncated".into()))?;
            Ok((Opd::Rsp(sext(u64::from(d), 8)), reg, 3))
        }
        _ => err("unsupported operand", b),
    }
}

/// Decode one instruction at code address `pc` from its bytes `b` (exactly one instruction).
fn decode(b: &[u8], pc: u64) -> Result<Insn, Error> {
    let total = b.len();
    let end = pc + total as u64;
    // RIP-relative operands are relative to the end of the instruction (all of `b`).
    let next = |_: usize| end;
    let mut i = 0;
    let lock = b.first() == Some(&0xf0);
    if lock {
        i += 1;
    }
    let mut size = 4u8;
    if b.get(i) == Some(&0x48) {
        size = 8;
        i += 1;
    }
    let op = *b.get(i).ok_or_else(|| Error("c11cir: empty".into()))?;
    let fin = |used: usize, ins: Insn| -> Result<Insn, Error> {
        if used == total {
            Ok(ins)
        } else {
            err("length mismatch", b)
        }
    };
    match (lock, op) {
        (false, 0xc7) => {
            let (a, reg, l) = modrm(b, i + 1, &next)?;
            if reg != 0 {
                return err("c7 /r", b);
            }
            let v = le(b, i + 1 + l, 4).ok_or_else(|| Error("c11cir: truncated".into()))?;
            let val = if size == 8 { sext(v, 32) as u64 } else { v };
            fin(i + 1 + l + 4, Insn::StoreI { size, a, val })
        }
        (false, 0x89) if b.get(i + 1).is_some_and(|m| m >> 6 == 3) => {
            let m = b[i + 1];
            fin(
                i + 2,
                Insn::MovRR {
                    size,
                    dst: m & 7,
                    src: (m >> 3) & 7,
                },
            )
        }
        (false, 0x89) => {
            let (a, src, l) = modrm(b, i + 1, &next)?;
            fin(i + 1 + l, Insn::StoreR { size, a, src })
        }
        (false, 0x8b) => {
            let (a, dst, l) = modrm(b, i + 1, &next)?;
            fin(i + 1 + l, Insn::Load { size, a, dst })
        }
        (false, 0x87) => {
            let (a, src, l) = modrm(b, i + 1, &next)?;
            fin(i + 1 + l, Insn::Xchg { size, a, src })
        }
        (true, 0x0f) if b.get(i + 1) == Some(&0xc1) => {
            let (a, src, l) = modrm(b, i + 2, &next)?;
            fin(i + 2 + l, Insn::Xadd { size, a, src })
        }
        (true, 0x83) => {
            let (a, reg, l) = modrm(b, i + 1, &next)?;
            let ops = ["add", "or", "", "", "and", "sub", "xor", ""];
            let o = ops[usize::from(reg)];
            if o.is_empty() {
                return err("lock 83 /r", b);
            }
            let v = u64::from(
                *b.get(i + 1 + l)
                    .ok_or_else(|| Error("c11cir: truncated".into()))?,
            );
            let val = sext(v, 8) as u64 & if size == 8 { u64::MAX } else { 0xffff_ffff };
            fin(
                i + 1 + l + 1,
                Insn::LockAlu {
                    size,
                    a,
                    op: o,
                    val,
                },
            )
        }
        (true, 0xff) => {
            let (a, reg, l) = modrm(b, i + 1, &next)?;
            if reg != 0 {
                return err("lock ff /r", b);
            }
            fin(i + 1 + l, Insn::LockInc { size, a })
        }
        (false, 0xff) => {
            let (a, reg, l) = modrm(b, i + 1, &next)?;
            if reg != 0 {
                return err("ff /r", b);
            }
            fin(i + 1 + l, Insn::Inc { size, a })
        }
        (false, 0xb8..=0xbf) if size == 4 => {
            let v = le(b, i + 1, 4).ok_or_else(|| Error("c11cir: truncated".into()))?;
            fin(
                i + 5,
                Insn::MovRI {
                    dst: op - 0xb8,
                    val: v,
                },
            )
        }
        (false, 0x8d) => {
            let m = *b
                .get(i + 1)
                .ok_or_else(|| Error("c11cir: truncated".into()))?;
            if m >> 6 != 1 || m & 7 == 4 {
                return err("lea form", b);
            }
            let d = u64::from(
                *b.get(i + 2)
                    .ok_or_else(|| Error("c11cir: truncated".into()))?,
            );
            fin(
                i + 3,
                Insn::Lea {
                    size,
                    dst: (m >> 3) & 7,
                    base: m & 7,
                    disp: sext(d, 8),
                },
            )
        }
        _ => err("unsupported instruction", b),
    }
}

fn reg(n: u8) -> String {
    format!(".{}", REGS[usize::from(n)])
}

fn addr(a: Opd) -> String {
    match a {
        Opd::Abs(v) => format!("(.lit 0x{v:x})"),
        Opd::Rsp(d) => format!("(.bin .add (.reg .rsp) (.lit 0x{:x}))", d as u64),
    }
}

fn mode(m: &str) -> Result<&'static str, Error> {
    Ok(match m {
        "na" => ".na",
        "rlx" => ".rlx",
        "acq" => ".acq",
        "rel" => ".rel",
        "sc" => ".sc",
        "acq_rel" => ".acqRel",
        _ => return Err(Error(format!("c11cir: mode `{m}`"))),
    })
}

/// The CIR statements of one instruction, with the modes of its C11 accesses.
fn lift(i: &Insn, modes: &[&'static str], scratch: Option<u8>) -> Result<Vec<String>, Error> {
    let m = |k: usize| modes.get(k).copied().unwrap_or(".na");
    let sc = || scratch.ok_or_else(|| Error("c11cir: no scratch register".into()));
    Ok(match *i {
        Insn::StoreR { size, a, src } => vec![format!(
            ".store {} {size} .wb {} (.reg {})",
            m(0),
            addr(a),
            reg(src)
        )],
        Insn::StoreI { size, a, val } => vec![format!(
            ".store {} {size} .wb {} (.lit 0x{val:x})",
            m(0),
            addr(a)
        )],
        Insn::Load { size, a, dst } => {
            vec![format!(
                ".load {} {} {size} .wb {}",
                reg(dst),
                m(0),
                addr(a)
            )]
        }
        Insn::Xchg { size, a, src } => vec![format!(
            ".rmw {} {} {size} .xchg {} (.reg {})",
            reg(src),
            m(0),
            addr(a),
            reg(src)
        )],
        Insn::Xadd { size, a, src } => vec![format!(
            ".rmw {} {} {size} .fadd {} (.reg {})",
            reg(src),
            m(0),
            addr(a),
            reg(src)
        )],
        Insn::LockAlu { size, a, op, val } => vec![format!(
            ".rmw {} {} {size} (.op .{op}) {} (.lit 0x{val:x})",
            reg(sc()?),
            m(0),
            addr(a)
        )],
        Insn::LockInc { size, a } => vec![format!(
            ".rmw {} {} {size} (.op .add) {} (.lit 1)",
            reg(sc()?),
            m(0),
            addr(a)
        )],
        Insn::Inc { size, a } => {
            let d = reg(sc()?);
            vec![
                format!(".load {d} {} {size} .wb {}", m(0), addr(a)),
                format!(
                    ".store {} {size} .wb {} (.bin .add (.reg {d}) (.lit 1))",
                    m(1),
                    addr(a)
                ),
            ]
        }
        Insn::MovRI { dst, val } => vec![format!(".assign {} (.lit 0x{val:x})", reg(dst))],
        Insn::MovRR { size, dst, src } => vec![if size == 8 {
            format!(".assign {} (.reg {})", reg(dst), reg(src))
        } else {
            format!(
                ".assign {} (.bin .and (.reg {}) (.lit 0xffffffff))",
                reg(dst),
                reg(src)
            )
        }],
        Insn::Lea {
            size,
            dst,
            base,
            disp,
        } => {
            let e = format!(
                "(.bin .add (.reg {}) (.lit 0x{:x}))",
                reg(base),
                disp as u64
            );
            vec![if size == 8 {
                format!(".assign {} {e}", reg(dst))
            } else {
                format!(".assign {} (.bin .and {e} (.lit 0xffffffff))", reg(dst))
            }]
        }
    })
}

impl Insn {
    fn regs(&self) -> Vec<u8> {
        match *self {
            Insn::StoreR { src, .. } | Insn::Xchg { src, .. } | Insn::Xadd { src, .. } => vec![src],
            Insn::Load { dst, .. } | Insn::MovRI { dst, .. } => vec![dst],
            Insn::MovRR { dst, src, .. } => vec![dst, src],
            Insn::Lea { dst, base, .. } => vec![dst, base],
            _ => vec![],
        }
    }
    fn opd(&self) -> Option<Opd> {
        match *self {
            Insn::StoreR { a, .. }
            | Insn::StoreI { a, .. }
            | Insn::Load { a, .. }
            | Insn::Xchg { a, .. }
            | Insn::Xadd { a, .. }
            | Insn::LockAlu { a, .. }
            | Insn::LockInc { a, .. }
            | Insn::Inc { a, .. } => Some(a),
            _ => None,
        }
    }
    fn needs_scratch(&self) -> bool {
        matches!(
            self,
            Insn::LockAlu { .. } | Insn::LockInc { .. } | Insn::Inc { .. }
        )
    }
}

fn verdict(v: &str) -> Result<&'static str, Error> {
    Ok(match v {
        "allowed" => ".allowed",
        "forbidden" => ".forbidden",
        "racy" => ".racy",
        _ => return Err(Error(format!("c11cir: verdict `{v}`"))),
    })
}

fn lean_str(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

fn bytes_lit(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(|x| format!("0x{x:02x}")).collect();
    format!("[{}]", v.join(", "))
}

/// The witness as a litmus `Cond`.
fn cond(w: &Value) -> Result<String, Error> {
    if let Ok(a) = w.get("and") {
        let parts: Vec<String> = a.arr()?.iter().map(cond).collect::<Result<_, _>>()?;
        let mut it = parts.into_iter().rev();
        let last = it
            .next()
            .ok_or_else(|| Error("c11cir: empty conjunction".into()))?;
        Ok(it.fold(last, |acc, p| format!("(.and {p} {acc})")))
    } else if let Ok(m) = w.get("mem") {
        let m = m.arr()?;
        let (Some(a), Some(n), Some(v)) = (m.first(), m.get(1), m.get(2)) else {
            return Err(Error("c11cir: bad mem atom".into()));
        };
        Ok(format!(
            "(.atom (.mem 0x{:x} {} 0x{:x}))",
            a.uint()?,
            n.uint()?,
            v.uint()?
        ))
    } else {
        Err(Error("c11cir: unsupported witness".into()))
    }
}

/// One rendered test, or the reason it was skipped.
enum Out {
    Test(String),
    Skip(String),
}

fn render_test(t: &Value, meta: &Value) -> Result<Out, Error> {
    let name = t.get("name")?.str()?;
    let id = format!("«{name}»");
    let tso = t.get("tso")?.str()?;
    let sc = t.get("sc")?.str()?;
    let xl = t.get("xl")?.str()?;
    let expected = meta.get("c11_expected")?.get("verdict")?.str()?;
    // Predicted: some RC11-consistent execution satisfies the witness while x86 forbids it.
    // For the racy (plain) variants this is the shape's RC11 behaviour with non-atomic reads
    // (MP, IRIW and 2+2W allow the witness; LB, CoRR and SB+fences do not). Lean checks it.
    let shape = meta.get("shape")?.str()?;
    let rc_allows = expected == "allowed"
        || (expected == "racy" && matches!(shape, "mp" | "iriw" | "2+2w" | "sb" | "counter"));
    let stronger = rc_allows && tso == "forbidden";
    let mthreads = meta.get("threads")?.arr()?;
    let mut threads_src = Vec::new();
    let mut certs = Vec::new();
    for (k, th) in t.get("threads")?.arr()?.iter().enumerate() {
        let base = u64::try_from(th.get("code_base")?.uint()?)
            .map_err(|_| Error("c11cir: code_base".into()))?;
        let mt = mthreads
            .get(k)
            .ok_or_else(|| Error("c11cir: thread count".into()))?;
        // modes per instruction index, in the order of the C11 accesses
        let code = th.get("code")?.arr()?;
        let mut modes: Vec<Vec<&'static str>> = vec![Vec::new(); code.len()];
        for a in mt.get("c11")?.arr()? {
            let m = mode(a.get("mode")?.str()?)?;
            for j in a.get("x86")?.arr()? {
                let j = usize::try_from(j.uint()?).map_err(|_| Error("c11cir: index".into()))?;
                if let Some(v) = modes.get_mut(j) {
                    v.push(m);
                }
            }
        }
        let mut pc = base;
        let mut decoded = Vec::new();
        for c in code {
            let b = json::hex_bytes(c.get("bytes")?.str()?)?;
            let ins = match decode(&b, pc) {
                Ok(i) => i,
                Err(e) => {
                    return Ok(Out::Skip(format!(
                        "`{name}` thread {k}: `{}`: {}",
                        c.get("asm")?.str()?,
                        e.0
                    )));
                }
            };
            pc += b.len() as u64;
            decoded.push((c.get("asm")?.str()?.to_string(), b, ins));
        }
        // the stack slot
        let rsp_disps: Vec<i64> = decoded
            .iter()
            .filter_map(|d| match d.2.opd() {
                Some(Opd::Rsp(x)) => Some(x),
                _ => None,
            })
            .collect();
        let mut regs: Vec<(u8, u64)> = Vec::new();
        if let Some(&d) = rsp_disps.first() {
            if rsp_disps.iter().any(|&x| x != d) {
                return Err(Error(format!("c11cir: {name}: two stack slots")));
            }
            let slot = SLOT_BASE + SLOT_STRIDE * k as u64;
            regs.push((RSP, slot.wrapping_sub(d as u64)));
        }
        let mut used: Vec<u8> = regs.iter().map(|r| r.0).collect();
        for d in &decoded {
            used.extend(d.2.regs());
        }
        let scratch = if decoded.iter().any(|d| d.2.needs_scratch()) {
            SCRATCH.iter().copied().find(|r| !used.contains(r))
        } else {
            None
        };
        let mut items = Vec::new();
        for (j, (asm, b, ins)) in decoded.iter().enumerate() {
            items.push((asm.clone(), b.len(), lift(ins, &modes[j], scratch)?));
        }
        let insns: Vec<String> = decoded
            .iter()
            .map(|(asm, b, _)| format!("⟨{}, {}, none⟩", lean_str(asm), bytes_lit(b)))
            .collect();
        let regs_l: Vec<String> = regs
            .iter()
            .map(|(r, v)| format!("({}, 0x{v:x})", reg(*r)))
            .collect();
        threads_src.push(format!(
            "⟨[\n        {}],\n      [{}]⟩",
            insns.join(",\n        "),
            regs_l.join(", ")
        ));
        let mut cs = String::new();
        let _ = write!(cs, "-- thread {k}");
        if let Some(s) = scratch {
            let _ = write!(cs, " (scratch {})", REGS[usize::from(s)]);
        }
        let _ = write!(
            cs,
            "\n    {{ pro := [{}],\n      items := [",
            regs_l.join(", ")
        );
        for (j, (asm, len, ops)) in items.iter().enumerate() {
            if j > 0 {
                cs.push(',');
            }
            let _ = write!(
                cs,
                "\n        -- {asm}\n        ⟨{len}, [{}]⟩",
                ops.join(", ")
            );
        }
        cs.push_str("] }");
        certs.push(cs);
    }
    let mut locs = Vec::new();
    for l in t.get("locs")?.arr()? {
        let init = json::hex_bytes(l.get("init")?.str()?)?;
        let v = init
            .iter()
            .rev()
            .fold(0u128, |a, &x| (a << 8) | u128::from(x));
        locs.push(format!(
            "⟨{}, 0x{:x}, {}, 0x{v:x}⟩",
            lean_str(l.get("name")?.str()?),
            l.get("addr")?.uint()?,
            l.get("size")?.uint()?
        ));
    }
    let mut s = String::new();
    let _ = writeln!(
        s,
        "/-- `{name}`: `{}` (`{}`), C11 verdict expected {expected} (hand-recorded). -/",
        t.get("object")?.str()?,
        t.get("path")?.str()?
    );
    let _ = writeln!(s, "def {id} : C11Test where");
    s.push_str("  tv := {\n    test := {\n");
    let _ = writeln!(s, "      name := {}", lean_str(name));
    let _ = writeln!(s, "      source := {}", lean_str(t.get("path")?.str()?));
    let _ = writeln!(
        s,
        "      doc := {}",
        lean_str(&format!(
            "{} compiled by {}",
            t.get("object")?.str()?,
            t.get("compiler")?.str()?
        ))
    );
    let _ = writeln!(s, "      locs := [{}]", locs.join(", "));
    let _ = writeln!(
        s,
        "      threads := [\n      {}]",
        threads_src.join(",\n      ")
    );
    s.push_str("      quant := .exists_\n");
    let _ = writeln!(s, "      cond := {}", cond(t.get("witness")?)?);
    s.push_str("      coverage := .tso\n");
    let _ = writeln!(s, "      tso := some {}", verdict(tso)?);
    let _ = writeln!(s, "      xl := {}", verdict(xl)?);
    let _ = writeln!(s, "      sc := some {}", verdict(sc)?);
    s.push_str(
        "      basis := \"tools/litmus-x86 checker on the lifted IR; checked on CIR here\" }\n",
    );
    let _ = writeln!(s, "    certs := [\n    {}] }}", certs.join(",\n    "));
    let _ = writeln!(s, "  expected := {}", verdict(expected)?);
    let _ = writeln!(s, "  stronger := {stronger}\n");
    Ok(Out::Test(s))
}

/// The Lean module name of a shape's checks.
fn shape_module(shape: &str) -> String {
    match shape {
        "2+2w" => "W22".into(),
        "sb+fences" => "SbFences".into(),
        s => {
            let mut c = s.chars();
            match c.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + c.as_str(),
                None => String::new(),
            }
        }
    }
}

/// The rendered modules: the tests, the per-shape kernel checks and their aggregate.
struct Rendered {
    defs: String,
    shapes: Vec<(String, String)>,
    agg: String,
    n: usize,
}

/// Render the Lean modules.
fn render(export: &Value, meta: &Value) -> Result<Rendered, Error> {
    let tests = export.get("tests")?.arr()?;
    let metas = meta.get("tests")?.arr()?;
    let mut body = String::new();
    let mut names: Vec<(String, String)> = Vec::new();
    let mut skipped = Vec::new();
    for t in tests {
        let name = t.get("name")?.str()?;
        let m = metas
            .iter()
            .find(|m| m.get("name").and_then(Value::str).ok() == Some(name))
            .ok_or_else(|| Error(format!("c11cir: no sidecar entry for {name}")))?;
        match render_test(t, m)? {
            Out::Test(s) => {
                body.push_str(&s);
                names.push((format!("«{name}»"), shape_module(m.get("shape")?.str()?)));
            }
            Out::Skip(r) => skipped.push(r),
        }
    }
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.C11.Defs\n\n");
    s.push_str("/-!\n# C11 litmus objects validated into CIR (generated)\n\n");
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- c11 cir`) from \
         `tools/litmus-x86/export/c11.json` and\n`export/c11-meta.json`; do not edit. \
         `c11 cir --check` regenerates it and compares byte for byte.\n\n",
    );
    s.push_str(
        "Per object of `examples/litmus-c`: the x86 test (relocated \
         bytes, locations,\nthe condition on the result slots, the x86 verdicts of `c11 ingest`) \
         and one certificate per thread whose\nCIR statements carry the modes of the C11 \
         accesses the sidecar maps to each instruction. Lean checks\neverything \
         (`C11Test.check`); see `Silmaril.X86.Concurrency.Cir.C11`.\n",
    );
    if !skipped.is_empty() {
        s.push_str("\nSkipped (a form outside the validated subset):\n\n");
        for r in &skipped {
            let _ = writeln!(s, "* {r}");
        }
    }
    s.push_str(
        "-/\n\n@[expose] public section\n\nnamespace Silmaril.X86.Concurrency.Cir.C11.Corpus\n\n",
    );
    s.push_str("open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv\n");
    s.push_str("open Silmaril.X86.Concurrency.Cir.C11\n\nset_option maxRecDepth 4096\n\n");
    s.push_str(&body);
    s.push_str("/-- Every validated C11 test. -/\ndef all : List C11Test := [\n");
    let ids: Vec<String> = names.iter().map(|p| p.0.clone()).collect();
    let _ = writeln!(s, "  {}]", ids.join(",\n  "));
    s.push_str("\nend Silmaril.X86.Concurrency.Cir.C11.Corpus\n");

    // one module of kernel checks per shape, so that lake can check the shapes in parallel
    let mut shapes: Vec<(String, String)> = Vec::new();
    for (id, sh) in &names {
        if !shapes.iter().any(|p| &p.0 == sh) {
            shapes.push((sh.clone(), String::new()));
        }
        let (_, text) = shapes
            .iter_mut()
            .find(|p| &p.0 == sh)
            .ok_or_else(|| Error("c11cir: shape".into()))?;
        if text.is_empty() {
            text.push_str(
                "module\n\npublic import Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs\n\n",
            );
            let _ = write!(
                text,
                "/-!\n# C11 litmus objects: kernel checks, shape `{sh}` (generated)\n\n\
                 GENERATED by `tools/litmus-x86` (`cargo run --release -- c11 cir`); do not edit.\n\
                 One `decide +kernel` of `C11Test.check` per test (kernel-checked).\n-/\n\n@[expose] public section\n\n\
                 namespace Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus\n\n\
                 open Silmaril.X86.Concurrency.Cir.C11\n\nset_option maxRecDepth 100000\n\n"
            );
        }
        let bare = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(
            text,
            "theorem «ok_{bare}» : Corpus.{id}.check = true := by decide +kernel\n"
        );
    }
    for (_, text) in &mut shapes {
        text.push_str("end Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus\n");
    }
    let mut p = String::new();
    p.push_str("module\n\n");
    for (sh, _) in &shapes {
        let _ = writeln!(
            p,
            "public import Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus.{sh}"
        );
    }
    p.push_str("\n/-!\n# C11 litmus objects: every kernel check (generated)\n\n");
    p.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- c11 cir`); do not edit.\n\n\
         The per-shape modules hold one `decide +kernel` per test; \
         this collects them.\nWhat they give is stated in \
         `Silmaril.X86.Concurrency.Cir.C11.Corpus.Thms`.\n-/\n\n",
    );
    p.push_str(
        "@[expose] public section\n\nnamespace Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus\n\n",
    );
    p.push_str("open Silmaril.X86.Concurrency.Cir.C11\n\n");
    let alts = vec!["rfl"; names.len()].join(" | ");
    p.push_str("/-- Every test passes its check. -/\n");
    p.push_str("theorem all_ok : ∀ c ∈ Corpus.all, c.check = true := by\n  intro c hc\n");
    p.push_str("  simp only [Corpus.all, List.mem_cons, List.not_mem_nil, or_false] at hc\n");
    let _ = writeln!(p, "  rcases hc with {alts}");
    for (id, _) in &names {
        let bare = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(p, "  · exact «ok_{bare}»");
    }
    p.push_str("\nend Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus\n");
    Ok(Rendered {
        defs: s,
        shapes,
        agg: p,
        n: names.len(),
    })
}

/// The files of a rendering, with their paths.
fn files(root: &std::path::Path, r: &Rendered) -> Vec<(std::path::PathBuf, String)> {
    let mut v = vec![
        (
            root.join("../../Silmaril/X86/Concurrency/Cir/C11/Corpus/Defs.lean"),
            r.defs.clone(),
        ),
        (
            root.join("../../Silmaril/Proofs/X86/Concurrency/Cir/C11Corpus.lean"),
            r.agg.clone(),
        ),
    ];
    for (sh, text) in &r.shapes {
        v.push((
            root.join(format!(
                "../../Silmaril/Proofs/X86/Concurrency/Cir/C11Corpus/{sh}.lean"
            )),
            text.clone(),
        ));
    }
    v
}

/// `litmus-x86 c11 cir [--check]`.
pub fn run(check: bool) -> Result<(), Error> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let read = |p: std::path::PathBuf| -> Result<Value, Error> {
        let src =
            std::fs::read_to_string(&p).map_err(|e| Error(format!("{}: {e}", p.display())))?;
        json::parse(&src)
    };
    let export = read(root.join("export/c11.json"))?;
    let meta = read(root.join("export/c11-meta.json"))?;
    let r = render(&export, &meta)?;
    for (path, body) in files(root, &r) {
        if check {
            let old = std::fs::read_to_string(&path)
                .map_err(|e| Error(format!("{}: {e}", path.display())))?;
            if old != body {
                return Err(Error(format!(
                    "{} is out of date; run `cargo run --release -- c11 cir`",
                    path.display()
                )));
            }
        } else {
            if let Some(p) = path.parent() {
                std::fs::create_dir_all(p).map_err(|e| Error(format!("{}: {e}", p.display())))?;
            }
            std::fs::write(&path, body).map_err(|e| Error(format!("{}: {e}", path.display())))?;
        }
    }
    println!(
        "ok: {} tests {}",
        r.n,
        if check { "up to date" } else { "written" }
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_c11_forms() {
        let d = |s: &str, pc: u64| decode(&json::hex_bytes(s).unwrap(), pc).unwrap();
        // movl $1, x(%rip) at 0x400000, 10 bytes: next = 0x40000a, disp = -0x3f000a
        assert_eq!(
            d("c705f6ffc0ff01000000", 0x400000),
            Insn::StoreI {
                size: 4,
                a: Opd::Abs(0x10000),
                val: 1
            }
        );
        assert_eq!(
            d("f048830c2400", 0x40000a),
            Insn::LockAlu {
                size: 8,
                a: Opd::Rsp(0),
                op: "or",
                val: 0
            }
        );
        assert_eq!(
            d("f0834c24c000", 0x40000a),
            Insn::LockAlu {
                size: 4,
                a: Opd::Rsp(-0x40),
                op: "or",
                val: 0
            }
        );
        assert_eq!(
            d("8d4801", 0),
            Insn::Lea {
                size: 4,
                dst: 1,
                base: 0,
                disp: 1
            }
        );
        assert_eq!(
            d("89c2", 0),
            Insn::MovRR {
                size: 4,
                dst: 2,
                src: 0
            }
        );
        // the unlocked `addl $1, m` is refused
        assert!(decode(&json::hex_bytes("8305f9ffc0ff01").unwrap(), 0).is_err());
    }

    /// The generated Lean modules are the proposer's output on the committed exports.
    #[test]
    fn c11_cir_modules_up_to_date() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let rd = |p: &str| json::parse(&std::fs::read_to_string(root.join(p)).unwrap()).unwrap();
        let r = render(&rd("export/c11.json"), &rd("export/c11-meta.json")).unwrap();
        assert_eq!(r.n, 63);
        assert_eq!(r.shapes.len(), 8);
        for (path, body) in files(root, &r) {
            assert_eq!(std::fs::read_to_string(path).unwrap(), body);
        }
    }
}
