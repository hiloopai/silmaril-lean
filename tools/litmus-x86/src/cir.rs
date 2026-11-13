//! `cir`: the **untrusted** proposer for translation validation
//! x86 -> CIR.
//!
//! For every x86-TSO-covered test of `export/corpus.json`, each thread's instructions are
//! decoded **from their bytes** (not from the assembly text) into a small instruction form
//! (`Insn`), and each form is lifted to CIR statements. The result is written as the Lean
//! module `Silmaril/X86/Concurrency/Cir/Tv/Corpus/Defs.lean` (and the per-test kernel checks,
//! `Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean`): one `Cir.Tv.TvTest` per test,
//! whose certificate lists, per thread, the initial registers as CIR assignments and, per
//! instruction, its byte length and its CIR statements. Nothing here is trusted: Lean's
//! `tvRun` re-decodes the bytes with the `Atomic9` decoder and checks every item, and
//! `tvRun_sound` is what makes an accepted certificate mean something.
//!
//! Choices the proposer makes (all checked or irrelevant to the check):
//!
//! * modes: plain loads `acq`, plain stores `rel`, locked read-modify-writes `sc`, the halves of
//!   an unlocked `inc`/`dec` `na`. These are the C11 modes the x86 instructions implement
//!   under the usual mapping (plain `mov` is acquire/release on x86-TSO). The checker ignores
//!   modes (`Stmt.demode`); that an `sc` access really is `sc` needs the C11 mapping check,
//!   which is not done here.
//! * scratch registers: CIR's `rmw` always writes a destination register and CIR has no
//!   unlocked read-modify-write, so `lock add/inc m` and unlocked `inc m` need a scratch
//!   register, which the checker records as clobbered. The proposer picks the first of
//!   `r11, r10, ..., r8, r15, ..., r12` that the thread neither uses, starts with, nor exposes
//!   to the final condition.
//!
//! Supported encodings (absolute `[disp32]` operands only: ModRM `mod = 00, r/m = 100`, SIB
//! `0x25`): `mov m, r` (`89`), `mov r, m` (`8B`), `mov m, imm` (`C7 /0`), `movb m, imm8`
//! (`C6 /0`), `xchg m, r` (`87`), `lock xadd` (`F0 0F C1`), `lock cmpxchg` (`F0 0F B1`),
//! `lock add/or/and/sub/xor m, imm` (`F0 83`/`F0 81`), `[lock] inc/dec m` (`[F0] FF /0`,
//! `/1`), `mov r32, imm32` (`B8+r`), `movabs` (`REX.W B8+r`), and the three fences
//! (`0F AE F0/E8/F8`), with `REX.W` for 64-bit operands. Anything else is refused.

use std::fmt::Write as _;

use crate::json::{self, Value};
use crate::litmus::Error;

/// The System V / x86 register names, by encoding number.
pub const REGS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// Scratch register preference (encoding numbers).
pub const SCRATCH: [u8; 8] = [11, 10, 9, 8, 15, 14, 13, 12];

/// A decoded instruction of the supported subset. Sizes are in bytes; addresses and values are
/// the 64-bit values Lean's checker computes (`addrE`, `immW`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Insn {
    StoreR {
        size: u8,
        addr: u64,
        src: u8,
    },
    StoreI {
        size: u8,
        addr: u64,
        val: u64,
    },
    Load {
        size: u8,
        addr: u64,
        dst: u8,
    },
    Xchg {
        size: u8,
        addr: u64,
        src: u8,
    },
    Xadd {
        size: u8,
        addr: u64,
        src: u8,
    },
    Cmpxchg {
        size: u8,
        addr: u64,
        src: u8,
    },
    LockAlu {
        size: u8,
        addr: u64,
        op: &'static str,
        val: u64,
    },
    LockIncDec {
        size: u8,
        addr: u64,
        dec: bool,
    },
    IncDec {
        size: u8,
        addr: u64,
        dec: bool,
    },
    Fence(&'static str),
    MovRI {
        dst: u8,
        val: u64,
    },
}

impl Insn {
    /// The registers the instruction names.
    pub fn regs(&self) -> Vec<u8> {
        match *self {
            Insn::StoreR { src, .. }
            | Insn::Xchg { src, .. }
            | Insn::Xadd { src, .. }
            | Insn::Cmpxchg { src, .. } => vec![src, 0],
            Insn::Load { dst, .. } | Insn::MovRI { dst, .. } => vec![dst],
            _ => vec![],
        }
    }
    /// Whether the CIR translation needs a scratch register.
    pub fn needs_scratch(&self) -> bool {
        matches!(
            self,
            Insn::LockAlu { .. } | Insn::LockIncDec { .. } | Insn::IncDec { .. }
        )
    }
}

fn err<T>(bytes: &[u8], m: &str) -> Result<T, Error> {
    Err(Error(format!("cir: {m} in {}", hex(bytes))))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn le(bytes: &[u8], at: usize, n: usize) -> Option<u64> {
    let s = bytes.get(at..at + n)?;
    Some(s.iter().rev().fold(0u64, |a, &b| (a << 8) | u64::from(b)))
}

/// Sign-extend the low `bits` bits of `v` to 64 bits.
fn sext(v: u64, bits: u32) -> u64 {
    let sh = 64 - bits;
    (((v << sh) as i64) >> sh) as u64
}

/// The `Ext.immW` value: an immediate sign-extended to the operand size, then zero-extended.
fn imm_w(v32: u64, size: u8) -> u64 {
    let s = sext(v32, 32);
    if size == 4 { s & 0xffff_ffff } else { s }
}

/// An absolute memory operand at `at` (ModRM, SIB `0x25`, disp32): the ModRM `reg` field and
/// the address.
fn abs_operand(bytes: &[u8], at: usize, rex_r: bool) -> Result<(u8, u64), Error> {
    let (Some(&m), Some(&sib)) = (bytes.get(at), bytes.get(at + 1)) else {
        return err(bytes, "truncated operand");
    };
    if m >> 6 != 0 || m & 7 != 4 || sib != 0x25 {
        return err(bytes, "not an absolute [disp32] operand");
    }
    let Some(d) = le(bytes, at + 2, 4) else {
        return err(bytes, "truncated displacement");
    };
    let reg = ((m >> 3) & 7) | if rex_r { 8 } else { 0 };
    Ok((reg, sext(d, 32)))
}

/// **Decode one instruction's bytes** (the whole slice must be one instruction).
pub fn decode(bytes: &[u8]) -> Result<Insn, Error> {
    let mut i = 0;
    let lock = bytes.first() == Some(&0xf0);
    if lock {
        i += 1;
    }
    let mut rex = 0u8;
    if let Some(&b) = bytes.get(i)
        && b & 0xf0 == 0x40
    {
        rex = b;
        i += 1;
    }
    let (w, r, b) = (rex & 8 != 0, rex & 4 != 0, rex & 1 != 0);
    let size: u8 = if w { 8 } else { 4 };
    let Some(&op) = bytes.get(i) else {
        return err(bytes, "empty");
    };
    i += 1;
    let done = |insn: Insn, len: usize| {
        if len == bytes.len() {
            Ok(insn)
        } else {
            err(bytes, "trailing bytes")
        }
    };
    match (lock, op) {
        (false, 0x89) => {
            let (src, addr) = abs_operand(bytes, i, r)?;
            done(Insn::StoreR { size, addr, src }, i + 6)
        }
        (false, 0x8b) => {
            let (dst, addr) = abs_operand(bytes, i, r)?;
            done(Insn::Load { size, addr, dst }, i + 6)
        }
        (false, 0xc7) => {
            let (d, addr) = abs_operand(bytes, i, r)?;
            if d & 7 != 0 {
                return err(bytes, "C7 /digit not 0");
            }
            let Some(v) = le(bytes, i + 6, 4) else {
                return err(bytes, "truncated immediate");
            };
            done(
                Insn::StoreI {
                    size,
                    addr,
                    val: imm_w(v, size),
                },
                i + 10,
            )
        }
        (false, 0xc6) if !w => {
            let (d, addr) = abs_operand(bytes, i, r)?;
            if d & 7 != 0 {
                return err(bytes, "C6 /digit not 0");
            }
            let Some(v) = le(bytes, i + 6, 1) else {
                return err(bytes, "truncated immediate");
            };
            done(
                Insn::StoreI {
                    size: 1,
                    addr,
                    val: v,
                },
                i + 7,
            )
        }
        (false, 0x87) => {
            let (src, addr) = abs_operand(bytes, i, r)?;
            done(Insn::Xchg { size, addr, src }, i + 6)
        }
        (_, 0xff) => {
            let (d, addr) = abs_operand(bytes, i, r)?;
            let dec = match d & 7 {
                0 => false,
                1 => true,
                _ => return err(bytes, "FF /digit not inc/dec"),
            };
            let insn = if lock {
                Insn::LockIncDec { size, addr, dec }
            } else {
                Insn::IncDec { size, addr, dec }
            };
            done(insn, i + 6)
        }
        (true, 0x83 | 0x81) => {
            let (d, addr) = abs_operand(bytes, i, r)?;
            let opn = match d & 7 {
                0 => "add",
                1 => "or",
                4 => "and",
                5 => "sub",
                6 => "xor",
                _ => return err(bytes, "unsupported locked ALU operation"),
            };
            let (n, bits) = if op == 0x83 { (1, 8) } else { (4, 32) };
            let Some(v) = le(bytes, i + 6, n) else {
                return err(bytes, "truncated immediate");
            };
            // `Atomic9` keeps the immediate sign-extended to 32 bits.
            let v32 = sext(v, bits) & 0xffff_ffff;
            done(
                Insn::LockAlu {
                    size,
                    addr,
                    op: opn,
                    val: imm_w(v32, size),
                },
                i + 6 + n,
            )
        }
        (true, 0x0f) | (false, 0x0f) => {
            let Some(&op2) = bytes.get(i) else {
                return err(bytes, "truncated 0F opcode");
            };
            i += 1;
            match (lock, op2) {
                (false, 0xae) if rex == 0 => {
                    let k = match bytes.get(i) {
                        Some(0xf0) => "mfence",
                        Some(0xe8) => "lfence",
                        Some(0xf8) => "sfence",
                        _ => return err(bytes, "0F AE not a fence"),
                    };
                    done(Insn::Fence(k), i + 1)
                }
                (true, 0xc1) => {
                    let (src, addr) = abs_operand(bytes, i, r)?;
                    done(Insn::Xadd { size, addr, src }, i + 6)
                }
                (true, 0xb1) => {
                    let (src, addr) = abs_operand(bytes, i, r)?;
                    done(Insn::Cmpxchg { size, addr, src }, i + 6)
                }
                _ => err(bytes, "unsupported 0F opcode"),
            }
        }
        (false, 0xb8..=0xbf) => {
            let dst = (op - 0xb8) | if b { 8 } else { 0 };
            if w {
                let Some(v) = le(bytes, i, 8) else {
                    return err(bytes, "truncated immediate");
                };
                done(Insn::MovRI { dst, val: v }, i + 8)
            } else {
                let Some(v) = le(bytes, i, 4) else {
                    return err(bytes, "truncated immediate");
                };
                done(Insn::MovRI { dst, val: v }, i + 4)
            }
        }
        _ => err(bytes, "unsupported instruction"),
    }
}

fn reg(n: u8) -> String {
    format!(".{}", REGS[usize::from(n)])
}

/// The CIR statements of one instruction (Lean syntax), given the thread's scratch register.
pub fn lift(insn: &Insn, scratch: Option<u8>) -> Result<Vec<String>, Error> {
    let lit = |v: u64| format!("(.lit 0x{v:x})");
    let need = || scratch.ok_or_else(|| Error("cir: no free scratch register".into()));
    Ok(match *insn {
        Insn::StoreR { size, addr, src } => {
            vec![format!(
                ".store .rel {size} .wb {} (.reg {})",
                lit(addr),
                reg(src)
            )]
        }
        Insn::StoreI { size, addr, val } => {
            vec![format!(".store .rel {size} .wb {} {}", lit(addr), lit(val))]
        }
        Insn::Load { size, addr, dst } => {
            vec![format!(".load {} .acq {size} .wb {}", reg(dst), lit(addr))]
        }
        Insn::Xchg { size, addr, src } => vec![format!(
            ".rmw {} .sc {size} .xchg {} (.reg {})",
            reg(src),
            lit(addr),
            reg(src)
        )],
        Insn::Xadd { size, addr, src } => vec![format!(
            ".rmw {} .sc {size} .fadd {} (.reg {})",
            reg(src),
            lit(addr),
            reg(src)
        )],
        Insn::Cmpxchg { size, addr, src } => vec![format!(
            ".rmw .rax .sc {size} (.cas (.reg .rax)) {} (.reg {})",
            lit(addr),
            reg(src)
        )],
        Insn::LockAlu {
            size,
            addr,
            op,
            val,
        } => vec![format!(
            ".rmw {} .sc {size} (.op .{op}) {} {}",
            reg(need()?),
            lit(addr),
            lit(val)
        )],
        Insn::LockIncDec { size, addr, dec } => vec![format!(
            ".rmw {} .sc {size} (.op .{}) {} (.lit 1)",
            reg(need()?),
            if dec { "sub" } else { "add" },
            lit(addr)
        )],
        Insn::IncDec { size, addr, dec } => {
            let d = reg(need()?);
            vec![
                format!(".load {d} .na {size} .wb {}", lit(addr)),
                format!(
                    ".store .na {size} .wb {} (.bin .{} (.reg {d}) (.lit 1))",
                    lit(addr),
                    if dec { "sub" } else { "add" }
                ),
            ]
        }
        Insn::Fence(k) => vec![format!(".fence .{k}")],
        Insn::MovRI { dst, val } => vec![format!(".assign {} {}", reg(dst), lit(val))],
    })
}

/// One lifted thread: initial registers and, per instruction, (asm, length, statements).
pub struct Lifted {
    pub regs: Vec<(u8, u64)>,
    pub items: Vec<(String, usize, Vec<String>)>,
    pub scratch: Option<u8>,
}

/// Lift one exported thread.
pub fn lift_thread(th: &Value) -> Result<Lifted, Error> {
    let mut regs = Vec::new();
    for r in th.get("regs")?.arr()? {
        let p = r.arr()?;
        let (Some(n), Some(v)) = (p.first(), p.get(1)) else {
            return Err(Error("cir: bad register entry".into()));
        };
        let n = u8::try_from(n.uint()?).map_err(|_| Error("cir: register number".into()))?;
        let v = u64::try_from(v.uint()?).map_err(|_| Error("cir: register value".into()))?;
        regs.push((n, v));
    }
    let mut used: Vec<u8> = regs.iter().map(|p| p.0).collect();
    for o in th.get("observe")?.arr()? {
        used.push(u8::try_from(o.uint()?).map_err(|_| Error("cir: observe".into()))?);
    }
    let mut decoded = Vec::new();
    for c in th.get("code")?.arr()? {
        let bytes = json::hex_bytes(c.get("bytes")?.str()?)?;
        let insn = decode(&bytes)?;
        used.extend(insn.regs());
        decoded.push((c.get("asm")?.str()?.to_string(), bytes.len(), insn));
    }
    let scratch = if decoded.iter().any(|d| d.2.needs_scratch()) {
        SCRATCH.iter().copied().find(|r| !used.contains(r))
    } else {
        None
    };
    let mut items = Vec::new();
    for (asm, len, insn) in &decoded {
        items.push((asm.clone(), *len, lift(insn, scratch)?));
    }
    Ok(Lifted {
        regs,
        items,
        scratch,
    })
}

/// Render the per-test kernel checks (`Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean`).
pub fn render_proofs(names: &[String]) -> String {
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs\n\n");
    s.push_str("/-!\n# Translation-validated corpus: per-test kernel checks (generated)\n\n");
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir`); do not edit.\n\n\
         One `decide +kernel` per test of `TvTest.allOk` (kernel-checked), and\nthe membership \
         of each test in the x86 litmus corpus. What they \
         give is stated in\n`Silmaril.X86.Concurrency.Cir.Tv.Corpus.Thms`.\n-/\n\n",
    );
    s.push_str(
        "@[expose] public section\n\nnamespace Silmaril.Proofs.X86.Concurrency.Cir.TvCorpus\n\n",
    );
    s.push_str("open Silmaril.X86.Concurrency.Cir.Tv\n\nset_option maxRecDepth 100000\n\n");
    for id in names {
        let bare = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(
            s,
            "theorem «ok_{bare}» : Corpus.{id}.allOk = true := by decide +kernel\n"
        );
    }
    let alts = vec!["rfl"; names.len()].join(" | ");
    s.push_str("/-- Every validated test passes `allOk`. -/\n");
    s.push_str("theorem all_ok : ∀ c ∈ Corpus.all, c.allOk = true := by\n  intro c hc\n");
    s.push_str("  simp only [Corpus.all, List.mem_cons, List.not_mem_nil, or_false] at hc\n");
    let _ = writeln!(s, "  rcases hc with {alts}");
    for id in names {
        let bare = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(s, "  · exact «ok_{bare}»");
    }
    s.push_str("\n/-- Every validated test is a test of the x86 litmus corpus. -/\n");
    s.push_str(
        "theorem all_mem : ∀ c ∈ Corpus.all, c.test ∈ Silmaril.X86.MemoryModel.Litmus.Corpus.all := by\n  intro c hc\n",
    );
    s.push_str("  simp only [Corpus.all, List.mem_cons, List.not_mem_nil, or_false] at hc\n");
    let _ = writeln!(s, "  rcases hc with {alts}");
    for id in names {
        let _ = writeln!(
            s,
            "  · show Silmaril.X86.MemoryModel.Litmus.Corpus.{id} ∈ _\n    \
             simp [Silmaril.X86.MemoryModel.Litmus.Corpus.all]"
        );
    }
    s.push_str("\nend Silmaril.Proofs.X86.Concurrency.Cir.TvCorpus\n");
    s
}

/// Render the Lean module from the exported corpus.
pub fn render(corpus: &Value) -> Result<(String, Vec<String>), Error> {
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.Defs\n");
    s.push_str("public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs\n\n");
    s.push_str(
        "/-!\n# Translation-validated CIR programs of the x86-TSO-covered corpus (generated)\n\n",
    );
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir`) from \
         `tools/litmus-x86/export/corpus.json`; do not edit.\n\
         `cargo run --release -- cir --check` regenerates it and compares byte for byte.\n\n",
    );
    s.push_str(
        "Per test: the x86 litmus corpus test and, per thread, the \
         certificate an\n**untrusted** proposer lifted from the thread's **bytes**: the initial \
         registers as CIR assignments,\nthen, per x86 instruction (its text in a comment), its \
         byte length and its CIR statements. The\nCIR thread is `Cert.body`. Lean's `tvRun` \
         checks every item against the bytes; see\n`Silmaril.X86.Concurrency.Cir.Tv`.\n-/\n\n",
    );
    s.push_str("@[expose] public section\n\nnamespace Silmaril.X86.Concurrency.Cir.Tv.Corpus\n\n");
    s.push_str("open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv\n\n");
    s.push_str("set_option maxRecDepth 4096\n\n");
    let mut names = Vec::new();
    for t in json_tests(corpus)? {
        if t.get("coverage")?.str()? != "tso" {
            continue;
        }
        let name = t.get("name")?.str()?;
        let id = format!("«{name}»");
        let _ = writeln!(s, "/-- `{name}`, translation-validated. -/");
        let _ = writeln!(s, "def {id} : TvTest where");
        let _ = writeln!(s, "  test := Silmaril.X86.MemoryModel.Litmus.Corpus.{id}");
        s.push_str("  certs := [");
        let threads = t.get("threads")?.arr()?;
        for (k, th) in threads.iter().enumerate() {
            let l = lift_thread(th).map_err(|e| Error(format!("{name}, thread {k}: {}", e.0)))?;
            if k > 0 {
                s.push(',');
            }
            let pro: Vec<String> = l
                .regs
                .iter()
                .map(|(r, v)| format!("({}, 0x{v:x})", reg(*r)))
                .collect();
            let _ = write!(s, "\n    -- thread {k}");
            if let Some(sc) = l.scratch {
                let _ = write!(s, " (scratch {})", REGS[usize::from(sc)]);
            }
            let _ = write!(s, "\n    {{ pro := [{}],\n      items := [", pro.join(", "));
            for (j, (asm, len, ops)) in l.items.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                let _ = write!(
                    s,
                    "\n        -- {asm}\n        ⟨{len}, [{}]⟩",
                    ops.join(", ")
                );
            }
            s.push_str("] }");
        }
        s.push_str("]\n\n");
        names.push(id);
    }
    s.push_str("/-- Every translation-validated test. -/\ndef all : List TvTest := [\n");
    let _ = writeln!(s, "  {}]", names.join(",\n  "));
    s.push_str("\nend Silmaril.X86.Concurrency.Cir.Tv.Corpus\n");
    Ok((s, names))
}

fn json_tests(corpus: &Value) -> Result<&[Value], Error> {
    corpus.get("tests")?.arr()
}

/// `litmus-x86 cir [--check] [--json FILE] [--out FILE] [--proofs FILE]`.
pub fn run(args: &[String]) -> Result<(), Error> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut json_path = root.join("export/corpus.json");
    let mut out = root.join("../../Silmaril/X86/Concurrency/Cir/Tv/Corpus/Defs.lean");
    let mut proofs = root.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean");
    let mut check = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--check" => check = true,
            "--json" => {
                json_path = it
                    .next()
                    .ok_or_else(|| Error("--json needs a value".into()))?
                    .into();
            }
            "--out" => {
                out = it
                    .next()
                    .ok_or_else(|| Error("--out needs a value".into()))?
                    .into();
            }
            "--proofs" => {
                proofs = it
                    .next()
                    .ok_or_else(|| Error("--proofs needs a value".into()))?
                    .into();
            }
            _ => return Err(Error(format!("unknown argument `{a}`"))),
        }
    }
    let src = std::fs::read_to_string(&json_path)
        .map_err(|e| Error(format!("{}: {e}", json_path.display())))?;
    let corpus = json::parse(&src)?;
    let (text, names) = render(&corpus)?;
    let ptext = render_proofs(&names);
    for (path, body) in [(&out, &text), (&proofs, &ptext)] {
        if check {
            let old = std::fs::read_to_string(path)
                .map_err(|e| Error(format!("{}: {e}", path.display())))?;
            if &old != body {
                return Err(Error(format!(
                    "{} is out of date; run `cargo run --release -- cir`",
                    path.display()
                )));
            }
            println!(
                "ok: {} tests, {} is up to date",
                names.len(),
                path.display()
            );
        } else {
            if let Some(p) = path.parent() {
                std::fs::create_dir_all(p).map_err(|e| Error(format!("{}: {e}", p.display())))?;
            }
            std::fs::write(path, body).map_err(|e| Error(format!("{}: {e}", path.display())))?;
            println!("wrote {} tests to {}", names.len(), path.display());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_corpus_forms() {
        let d = |s: &str| decode(&json::hex_bytes(s).unwrap()).unwrap();
        assert_eq!(
            d("c704250000010001000000"),
            Insn::StoreI {
                size: 4,
                addr: 0x10000,
                val: 1
            }
        );
        assert_eq!(
            d("8b042540000100"),
            Insn::Load {
                size: 4,
                addr: 0x10040,
                dst: 0
            }
        );
        assert_eq!(
            d("8b1c2540000100"),
            Insn::Load {
                size: 4,
                addr: 0x10040,
                dst: 3
            }
        );
        assert_eq!(d("0faef0"), Insn::Fence("mfence"));
        assert_eq!(
            d("87042500000100"),
            Insn::Xchg {
                size: 4,
                addr: 0x10000,
                src: 0
            }
        );
        assert_eq!(
            d("f00fc1042500000100"),
            Insn::Xadd {
                size: 4,
                addr: 0x10000,
                src: 0
            }
        );
        assert_eq!(
            d("f00fb10c2500000100"),
            Insn::Cmpxchg {
                size: 4,
                addr: 0x10000,
                src: 1
            }
        );
        assert_eq!(
            d("f08304258000010000"),
            Insn::LockAlu {
                size: 4,
                addr: 0x10080,
                op: "add",
                val: 0
            }
        );
        assert_eq!(
            d("f0ff042500000100"),
            Insn::LockIncDec {
                size: 4,
                addr: 0x10000,
                dec: false
            }
        );
        assert_eq!(
            d("ff042500000100"),
            Insn::IncDec {
                size: 4,
                addr: 0x10000,
                dec: false
            }
        );
        assert_eq!(d("b802000000"), Insn::MovRI { dst: 0, val: 2 });
        assert_eq!(
            d("48c7042500000100ffffffff"),
            Insn::StoreI {
                size: 8,
                addr: 0x10000,
                val: u64::MAX
            }
        );
        assert_eq!(
            d("c60425000001007f"),
            Insn::StoreI {
                size: 1,
                addr: 0x10000,
                val: 0x7f
            }
        );
    }

    #[test]
    fn refuses() {
        let r = |s: &str| decode(&json::hex_bytes(s).unwrap()).is_err();
        // unlocked xadd, rip-relative operand, trailing byte, movnti, rep stosb
        assert!(r("0fc1042500000100"));
        assert!(r("8b0500000000"));
        assert!(r("8b04254000010000"));
        assert!(r("0fc3042500000100"));
        assert!(r("f3aa"));
    }

    #[test]
    fn lifts_with_scratch() {
        let i = Insn::IncDec {
            size: 4,
            addr: 0x10000,
            dec: false,
        };
        assert!(lift(&i, None).is_err());
        assert_eq!(
            lift(&i, Some(11)).unwrap(),
            vec![
                ".load .r11 .na 4 .wb (.lit 0x10000)".to_string(),
                ".store .na 4 .wb (.lit 0x10000) (.bin .add (.reg .r11) (.lit 1))".to_string()
            ]
        );
    }
}

#[cfg(test)]
mod fresh {
    use super::*;

    /// The generated Lean modules are the proposer's output on the committed export.
    #[test]
    fn cir_modules_up_to_date() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = std::fs::read_to_string(root.join("export/corpus.json")).unwrap();
        let (text, names) = render(&json::parse(&src).unwrap()).unwrap();
        assert_eq!(names.len(), 60);
        let lean = root.join("../../Silmaril/X86/Concurrency/Cir/Tv/Corpus/Defs.lean");
        assert_eq!(std::fs::read_to_string(lean).unwrap(), text);
        let proofs = root.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean");
        assert_eq!(
            std::fs::read_to_string(proofs).unwrap(),
            render_proofs(&names)
        );
    }
}
