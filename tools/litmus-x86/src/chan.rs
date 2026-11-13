//! `chan`: the channel C programs of `examples/litmus-c/chan`
//! (a one-slot mailbox and an SPSC ring of capacity 2), compiled with the pinned compilers,
//! cut into spin-loop pieces and translation-validated into CIR.
//!
//! ```text
//! litmus-x86 chan compile [--check]   # build (or check) <prog>/obj/<variant>.<cc>.o and objects.sha256
//! litmus-x86 chan [--check]           # write (or check) the Lean module and export/chan.json
//! ```
//!
//! Each program is compiled twice: as written (`ok`) and with `-DSWAP` (`swap`, the mutant whose
//! producer publishes before it writes the payload).
//!
//! The proposer (**untrusted**; Lean's `Cir.Tv.stvRun` checks everything it emits) reads each
//! object and ingests `P0` (producer) and `P1` (consumer):
//!
//! * thread `k` is placed at `0x400000 + 0x1000 k`; no relocation is allowed; the final `ret`
//!   is dropped;
//! * the bytes are cut into pieces: a **spin** is `mov m32, r` (absolute), then `test r, r` or
//!   `cmp $k, r` (imm8), then `jne`/`je`/`jbe`/`jb` rel8 back to the load; a **pad** is one
//!   `nop`; everything else must decode as a `cir::decode` form and is lifted with
//!   `cir::lift` into straight **segments**.
//!
//! Outputs: `Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean` (one `Cir.Tv.STest` per
//! (program, variant, compiler)) and `tools/litmus-x86/export/chan.json` for `tools/litmus-run`
//! (hardware runs on the same bytes). The JSON's allowed sets are not computed by a model: for
//! `ok` it is the one in-order outcome (Lean proves it is the only one for CIR with spin bound 0,
//! `Cir.Tv.Chan.Thms`); for `swap` it is every outcome where each message is received fresh or as
//! the previous content of its slot (an over-approximation, so the run only records which
//! occur).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::c11;
use crate::cir;
use crate::elf::{self, Object};
use crate::export::json_str;
use crate::litmus::Error;

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

fn io<T>(p: &Path, r: std::io::Result<T>) -> Result<T, Error> {
    r.map_err(|e| Error(format!("{}: {e}", p.display())))
}

/// One channel program.
pub struct Prog {
    pub name: &'static str,
    pub dir: &'static str,
    /// Locations: name, address (each 4 bytes, initially 0).
    pub locs: &'static [(&'static str, u64)],
    /// The final values of the locations in the in-order outcome.
    pub good: &'static [u64],
    /// The three result cells.
    pub results: [u64; 3],
    /// What a stale read of message `k` returns: the slot's previous content.
    pub stale: [u64; 3],
    /// The plain (non-atomic) cells: payload slots and result cells. Their accesses get CIR
    /// mode `na`; every other plain `mov` gets `acq`/`rel`. Modes are free for the checker
    /// (it compares after `Stmt.demode`), so this only labels the CIR program.
    pub plain: &'static [u64],
}

pub const PROGS: [Prog; 2] = [
    Prog {
        name: "Mailbox",
        dir: "mailbox",
        locs: &[
            ("data", 0x10000),
            ("seq", 0x10040),
            ("ack", 0x10080),
            ("r1", 0x100c0),
            ("r2", 0x10100),
            ("r3", 0x10140),
        ],
        good: &[3, 3, 3, 1, 2, 3],
        results: [0x100c0, 0x10100, 0x10140],
        stale: [0, 1, 2],
        plain: &[0x10000, 0x100c0, 0x10100, 0x10140],
    },
    Prog {
        name: "Ring",
        dir: "ring",
        locs: &[
            ("s0", 0x10000),
            ("s1", 0x10040),
            ("tail", 0x10080),
            ("head", 0x100c0),
            ("r1", 0x10100),
            ("r2", 0x10140),
            ("r3", 0x10180),
        ],
        good: &[3, 2, 3, 3, 1, 2, 3],
        results: [0x10100, 0x10140, 0x10180],
        stale: [0, 0, 1],
        plain: &[0x10000, 0x10040, 0x10100, 0x10140, 0x10180],
    },
];

/// The variants: name and extra compiler flags.
pub const VARIANTS: [(&str, &[&str]); 2] = [("ok", &[]), ("swap", &["-DSWAP"])];

fn toolchains(root: &Path) -> Result<c11::Toolchains, Error> {
    let tp = root.join("../toolchains.txt");
    c11::parse_toolchains(&io(&tp, std::fs::read_to_string(&tp))?)
}

/// Compile every (program, variant, compiler), or with `check` recompile into `tmp` and compare.
pub fn compile(root: &Path, check: bool, tmp: &Path) -> Result<usize, Error> {
    let tc = toolchains(root)?;
    c11::verify_toolchains(&tc)?;
    let mut manifest = String::new();
    let mut n = 0;
    for p in &PROGS {
        for (v, vflags) in VARIANTS {
            for cc in &tc.compilers {
                let rel = format!("{}/obj/{v}.{}.o", p.dir, cc.name);
                let dest = if check {
                    tmp.join(format!("chan-{n}.o"))
                } else {
                    let d = root.join(&rel);
                    if let Some(dd) = d.parent() {
                        io(dd, std::fs::create_dir_all(dd))?;
                    }
                    d
                };
                let dest = if dest.is_absolute() {
                    dest
                } else {
                    io(&dest, std::env::current_dir())?.join(&dest)
                };
                let st = io(
                    &cc.driver,
                    Command::new(&cc.driver)
                        .current_dir(root.join(p.dir))
                        .args(&tc.flags)
                        .args(vflags)
                        .arg("-c")
                        .arg(format!("{}.c", p.dir))
                        .arg("-o")
                        .arg(&dest)
                        .status(),
                )?;
                if !st.success() {
                    return err(format!("{} failed on {rel}", cc.name));
                }
                if check {
                    let a = io(&dest, std::fs::read(&dest))?;
                    let bp = root.join(&rel);
                    let b = io(&bp, std::fs::read(&bp))?;
                    let _ = std::fs::remove_file(&dest);
                    if a != b {
                        return err(format!("{rel}: recompiled object differs"));
                    }
                }
                let h = c11::sha256(&root.join(&rel))?;
                let _ = writeln!(manifest, "{h}  {rel}");
                n += 1;
            }
        }
    }
    let mp = root.join("objects.sha256");
    if check {
        if io(&mp, std::fs::read_to_string(&mp))? != manifest {
            return err("chan/objects.sha256 is out of date");
        }
    } else {
        io(&mp, std::fs::write(&mp, manifest))?;
    }
    Ok(n)
}

/// A piece of a thread.
#[derive(Debug, PartialEq, Eq)]
pub enum Piece {
    /// Straight code: per instruction (asm, length, CIR statements).
    Seg(Vec<(String, usize, Vec<String>)>),
    /// One nop.
    Pad(usize),
    /// A spin loop: length, register, address, CIR condition, asm text.
    Spin {
        len: usize,
        reg: u8,
        addr: u64,
        cond: String,
        asm: String,
    },
}

/// The length of a `nop` at the start of `b` (`90`, or prefixes `66`/`2e` then `0f 1f /0`).
pub fn nop_len(b: &[u8]) -> Option<usize> {
    let mut i = 0;
    while i < b.len() && (b[i] == 0x66 || b[i] == 0x2e) {
        i += 1;
    }
    if b.get(i) == Some(&0x90) {
        return (i <= 1).then_some(i + 1);
    }
    if b.get(i) != Some(&0x0f) || b.get(i + 1) != Some(&0x1f) {
        return None;
    }
    let modrm = *b.get(i + 2)?;
    if (modrm >> 3) & 7 != 0 {
        return None;
    }
    let (md, rm) = (modrm >> 6, modrm & 7);
    let sib = usize::from(md != 3 && rm == 4);
    let disp = match md {
        0 => {
            if rm == 5 {
                4
            } else {
                0
            }
        }
        1 => 1,
        2 => 4,
        _ => return None,
    };
    let n = i + 3 + sib + disp;
    (n <= b.len() && n <= 15).then_some(n)
}

/// A spin loop at the start of `b`: (length, register, address, CIR condition, asm).
pub fn spin_at(b: &[u8]) -> Option<(usize, u8, u64, String, String)> {
    let ld = cir::decode(b.get(..7)?).ok()?;
    let cir::Insn::Load {
        size: 4,
        addr,
        dst: r,
    } = ld
    else {
        return None;
    };
    let rn = cir::REGS[usize::from(r)];
    let (k, m, cmp) = match *b.get(7..9)? {
        [0x85, mr] if mr == 0xc0 | (r << 3) | r && r < 8 => (0u64, 2, format!("test %{rn}")),
        [0x83, mr] if mr == 0xf8 | r && r < 8 => {
            let k = *b.get(9)?;
            if k >= 0x80 {
                return None;
            }
            (u64::from(k), 3, format!("cmp ${k}, %{rn}"))
        }
        _ => return None,
    };
    let j = 7 + m;
    let (op, rel) = (*b.get(j)?, *b.get(j + 1)? as i8);
    if i64::from(rel) != -((j + 2) as i64) {
        return None;
    }
    let reg = format!("(.reg .{rn})");
    let (cond, cc) = match op {
        0x75 => (format!(".bin .ne {reg} (.lit {k})"), "jne"),
        0x74 => (format!(".bin .eq {reg} (.lit {k})"), "je"),
        0x76 => (format!(".bin .ltu {reg} (.lit {})", k + 1), "jbe"),
        0x72 => (format!(".bin .ltu {reg} (.lit {k})"), "jb"),
        _ => return None,
    };
    Some((
        j + 2,
        r,
        addr,
        cond,
        format!("spin: mov 0x{addr:x}, %{rn}; {cmp}; {cc} back"),
    ))
}

/// Give the plain loads and stores of the cells `plain` CIR mode `na` instead of `acq`/`rel`.
fn demote(i: &cir::Insn, ops: Vec<String>, plain: &[u64]) -> Vec<String> {
    let addr = match *i {
        cir::Insn::StoreR { addr, .. }
        | cir::Insn::StoreI { addr, .. }
        | cir::Insn::Load { addr, .. } => addr,
        _ => return ops,
    };
    if !plain.contains(&addr) {
        return ops;
    }
    ops.into_iter()
        .map(|o| {
            o.replacen(".store .rel ", ".store .na ", 1)
                .replacen(" .acq ", " .na ", 1)
        })
        .collect()
}

/// Cut a thread's bytes into pieces.
pub fn pieces(code: &[u8], plain: &[u64]) -> Result<Vec<Piece>, Error> {
    let mut out: Vec<Piece> = Vec::new();
    let mut seg: Vec<(String, usize, Vec<String>)> = Vec::new();
    let mut o = 0;
    while o < code.len() {
        let rest = &code[o..];
        let flush = |seg: &mut Vec<_>, out: &mut Vec<Piece>| {
            if !seg.is_empty() {
                out.push(Piece::Seg(std::mem::take(seg)));
            }
        };
        if let Some((len, reg, addr, cond, asm)) = spin_at(rest) {
            flush(&mut seg, &mut out);
            out.push(Piece::Spin {
                len,
                reg,
                addr,
                cond,
                asm,
            });
            o += len;
        } else if let Some(n) = nop_len(rest) {
            flush(&mut seg, &mut out);
            out.push(Piece::Pad(n));
            o += n;
        } else {
            let found =
                (1..=15.min(rest.len())).find_map(|n| cir::decode(&rest[..n]).ok().map(|i| (n, i)));
            let Some((n, i)) = found else {
                return err(format!(
                    "unsupported instruction at offset {o}: {}",
                    rest.iter()
                        .take(8)
                        .map(|b| format!("{b:02x}"))
                        .collect::<String>()
                ));
            };
            seg.push((format!("{i:?}"), n, demote(&i, cir::lift(&i, None)?, plain)));
            o += n;
        }
    }
    if !seg.is_empty() {
        out.push(Piece::Seg(seg));
    }
    Ok(out)
}

/// The bytes of thread function `name` without its final `ret`; no relocations allowed.
pub fn thread_bytes(obj: &Object, name: &str) -> Result<Vec<u8>, Error> {
    let sym = obj
        .defined(name, elf::STT_FUNC)
        .ok_or_else(|| Error(format!("no function `{name}`")))?;
    let sec = usize::from(sym.shndx);
    let sbytes = obj
        .section_bytes(sec)?
        .ok_or_else(|| Error(format!("`{name}`: no section bytes")))?;
    let lo = usize::try_from(sym.value).map_err(|_| Error("symbol value".into()))?;
    let len = usize::try_from(sym.size).map_err(|_| Error("symbol size".into()))?;
    let relocs = obj.relas.get(sec).map(Vec::as_slice).unwrap_or_default();
    if relocs
        .iter()
        .any(|r| usize::try_from(r.offset).is_ok_and(|o| o >= lo && o < lo + len))
    {
        return err(format!("`{name}` has relocations"));
    }
    let mut code = sbytes
        .get(lo..lo + len)
        .ok_or_else(|| Error(format!("`{name}` past its section")))?
        .to_vec();
    if code.last() != Some(&0xc3) {
        return err(format!("`{name}` does not end with ret"));
    }
    code.pop();
    Ok(code)
}

/// One ingested test.
pub struct Test {
    pub prog: &'static Prog,
    pub variant: &'static str,
    pub cc: String,
    pub threads: Vec<(Vec<u8>, Vec<Piece>)>,
}

impl Test {
    fn id(&self) -> String {
        format!("«{}+{}@{}»", self.prog.name, self.variant, self.cc)
    }
    fn swapped(&self) -> bool {
        self.variant == "swap"
    }
}

/// Ingest every committed object.
pub fn ingest(root: &Path) -> Result<Vec<Test>, Error> {
    let tc = toolchains(root)?;
    let mut out = Vec::new();
    for p in &PROGS {
        for (v, _) in VARIANTS {
            for cc in &tc.compilers {
                let path = root.join(format!("{}/obj/{v}.{}.o", p.dir, cc.name));
                let obj = Object::parse(io(&path, std::fs::read(&path))?)?;
                let mut threads = Vec::new();
                for f in ["P0", "P1"] {
                    let code = thread_bytes(&obj, f)?;
                    let ps = pieces(&code, p.plain).map_err(|e| Error(format!("{f}: {}", e.0)))?;
                    threads.push((code, ps));
                }
                out.push(Test {
                    prog: p,
                    variant: v,
                    cc: cc.name.clone(),
                    threads,
                });
            }
        }
    }
    Ok(out)
}

fn mem_atom(a: u64, v: u64) -> String {
    format!(".atom (.mem 0x{a:x} 4 {v})")
}

/// Render the Lean module.
pub fn render_lean(tests: &[Test]) -> String {
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.Spin.Defs\n\n");
    s.push_str("/-!\n# Channel C programs, translation-validated into CIR (generated)\n\n");
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- chan`) from the objects in\n\
         `examples/litmus-c/chan`; do not edit. `cargo run --release -- chan --check` \
         regenerates it and\ncompares byte for byte.\n\n\
         Per (program, variant, compiler): the locations, the condition \
         (`ok`:\nthe results are `1, 2, 3`, quantifier `forall`; `swap`: the first result is \
         the stale `0`,\nquantifier `exists`), each thread function's bytes (final `ret` \
         dropped), and the **untrusted**\nproposer's spin certificate (pieces: straight \
         segments with one item per instruction, `nop`\npads, spin loops). Lean's `stvRun` \
         checks the certificate against the bytes.\n-/\n\n",
    );
    s.push_str("@[expose] public section\n\nnamespace Silmaril.X86.Concurrency.Cir.Tv.Chan\n\n");
    s.push_str("open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv\n\n");
    s.push_str("set_option maxRecDepth 4096\n\n");
    for t in tests {
        let p = t.prog;
        let _ = writeln!(
            s,
            "/-- `{}` ({}) compiled by {} (`examples/litmus-c/chan/{}`). -/",
            p.name, t.variant, t.cc, p.dir
        );
        let _ = writeln!(s, "def {} : STest where", t.id());
        let _ = writeln!(s, "  test := {{");
        let _ = writeln!(s, "    name := \"{}+{}@{}\"", p.name, t.variant, t.cc);
        let _ = writeln!(
            s,
            "    source := \"examples/litmus-c/chan/{}/{}.c\"",
            p.dir, p.dir
        );
        let _ = writeln!(s, "    doc := \"\"");
        let locs: Vec<String> = p
            .locs
            .iter()
            .map(|(n, a)| format!("⟨\"{n}\", 0x{a:x}, 4, 0⟩"))
            .collect();
        let _ = writeln!(s, "    locs := [{}]", locs.join(", "));
        let _ = writeln!(s, "    threads := []");
        let [a, b, c] = p.results;
        if t.swapped() {
            let _ = writeln!(s, "    quant := .exists_");
            let _ = writeln!(s, "    cond := {}", mem_atom(a, 0));
            let _ = writeln!(s, "    coverage := .tso");
            let _ = writeln!(s, "    tso := some .allowed");
            let _ = writeln!(s, "    xl := .allowed");
            let _ = writeln!(s, "    sc := some .allowed");
        } else {
            let _ = writeln!(s, "    quant := .forall_");
            let _ = writeln!(
                s,
                "    cond := .and ({}) (.and ({}) ({}))",
                mem_atom(a, 1),
                mem_atom(b, 2),
                mem_atom(c, 3)
            );
            let _ = writeln!(s, "    coverage := .tso");
            let _ = writeln!(s, "    tso := some .forbidden");
            let _ = writeln!(s, "    xl := .forbidden");
            let _ = writeln!(s, "    sc := some .forbidden");
        }
        let _ = writeln!(s, "    basis := \"channel C programs\" }}");
        s.push_str("  threads := [");
        for (k, (code, _)) in t.threads.iter().enumerate() {
            if k > 0 {
                s.push(',');
            }
            let bytes: Vec<String> = code.iter().map(|b| format!("0x{b:02x}")).collect();
            let _ = write!(
                s,
                "\n    {{ base := Silmaril.X86.Litmus.codeBase {k}\n      \
                 code := [{}]\n      \
                 regions := Silmaril.X86.Litmus.testRegions 2\n      \
                 init := Silmaril.X86.Litmus.initCore (Silmaril.X86.Litmus.codeBase {k}) [] }}",
                bytes.join(", ")
            );
        }
        s.push_str("]\n  certs := [");
        let mut fuel = 0;
        for (k, (_, ps)) in t.threads.iter().enumerate() {
            if k > 0 {
                s.push(',');
            }
            let _ = write!(
                s,
                "\n    -- thread {k}\n    {{ pro := [],\n      pieces := ["
            );
            for (j, pc) in ps.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                match pc {
                    Piece::Seg(items) => {
                        fuel = fuel.max(items.len());
                        s.push_str("\n        .seg [");
                        for (q, (asm, len, ops)) in items.iter().enumerate() {
                            if q > 0 {
                                s.push(',');
                            }
                            let _ = write!(
                                s,
                                "\n          -- {asm}\n          ⟨{len}, [{}]⟩",
                                ops.join(", ")
                            );
                        }
                        s.push(']');
                    }
                    Piece::Pad(n) => {
                        let _ = write!(s, "\n        .pad {n}");
                    }
                    Piece::Spin {
                        len,
                        reg,
                        addr,
                        cond,
                        asm,
                    } => {
                        let _ = write!(
                            s,
                            "\n        -- {asm}\n        .spin {len} .{} .acq 0x{addr:x} ({cond})",
                            cir::REGS[usize::from(*reg)]
                        );
                    }
                }
            }
            s.push_str("] }");
        }
        s.push_str("]\n");
        let _ = writeln!(s, "  dom := [0, 1, 2, 3]");
        let _ = writeln!(s, "  fuel := {}\n", fuel.max(1) + 1);
    }
    let ids: Vec<String> = tests.iter().map(Test::id).collect();
    s.push_str("/-- Every translation-validated channel test. -/\ndef all : List STest := [\n");
    let _ = writeln!(s, "  {}]", ids.join(",\n  "));
    s.push_str("\nend Silmaril.X86.Concurrency.Cir.Tv.Chan\n");
    s
}

fn hex32(v: u64) -> String {
    v.to_le_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn outcome(mem: &[u64]) -> String {
    let m: Vec<String> = mem.iter().map(|v| format!("\"{}\"", hex32(*v))).collect();
    format!("{{\"regs\": [[], []], \"mem\": [{}]}}", m.join(", "))
}

/// The outcomes a test's hardware run may show (see the module docs).
fn allowed(t: &Test) -> Vec<String> {
    let p = t.prog;
    let n = p.good.len();
    if !t.swapped() {
        return vec![outcome(p.good)];
    }
    let mut out = Vec::new();
    for mask in 0..8u32 {
        let mut m = p.good.to_vec();
        for j in 0..3 {
            if mask & (1 << j) != 0 {
                m[n - 3 + j] = p.stale[j];
            }
        }
        out.push(outcome(&m));
    }
    out
}

/// Render the hardware export for `tools/litmus-run`.
pub fn render_json(tests: &[Test]) -> String {
    let mut s = String::from("{\n\"format\": \"silmaril-litmus-x86-export/1\",\n");
    s.push_str("\"generated_by\": \"tools/litmus-x86 chan (do not edit)\",\n");
    s.push_str("\"allowed_source\": \"ok = the in-order outcome (proved for CIR with spin bound 0 in Silmaril.X86.Concurrency.Cir.Tv.Chan.Thms); swap = an over-approximation (each message received fresh or as the previous content of its slot)\",\n");
    s.push_str("\"lean_module\": \"Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean\",\n");
    s.push_str("\"provenance\": [\"C sources: examples/litmus-c/chan; objects pinned in examples/litmus-c/chan/objects.sha256.\", \"Flags: the c11 pins of examples/litmus-c/toolchains.txt, plus -DSWAP for the swap variant.\", \"Layout: data at fixed addresses (absolute [disp32] operands); thread k's code at 0x400000 + 0x1000*k; the final ret is dropped.\"],\n");
    s.push_str("\"tests\": [");
    for (i, t) in tests.iter().enumerate() {
        s.push_str(if i == 0 { "\n" } else { ",\n" });
        let p = t.prog;
        let name = format!("{}+{}@{}", p.name, t.variant, t.cc);
        let (quant, v) = if t.swapped() {
            ("exists", "allowed")
        } else {
            ("forall", "forbidden")
        };
        let _ = writeln!(
            s,
            "  {{\"name\": {}, \"path\": {}, \"coverage\": \"tso\", \"quant\": \"{quant}\", \"tso\": \"{v}\", \"sc\": \"{v}\", \"xl\": \"{v}\",",
            json_str(&name),
            json_str(&format!("examples/litmus-c/chan/{}/{}.c", p.dir, p.dir))
        );
        let _ = writeln!(
            s,
            "   \"compiler\": {}, \"variant\": {}, \"object\": {},",
            json_str(&t.cc),
            json_str(t.variant),
            json_str(&format!(
                "examples/litmus-c/chan/{}/obj/{}.{}.o",
                p.dir, t.variant, t.cc
            ))
        );
        let locs: Vec<String> = p
            .locs
            .iter()
            .map(|(n, a)| {
                format!(
                    "{{\"name\": {}, \"addr\": \"0x{a:x}\", \"size\": 4, \"init\": \"00000000\"}}",
                    json_str(n)
                )
            })
            .collect();
        let _ = writeln!(s, "   \"locs\": [{}],", locs.join(", "));
        s.push_str("   \"threads\": [");
        for (k, (code, _)) in t.threads.iter().enumerate() {
            s.push_str(if k == 0 { "\n" } else { ",\n" });
            let hex: String = code.iter().map(|b| format!("{b:02x}")).collect();
            let _ = write!(
                s,
                "    {{\"regs\": [], \"observe\": [], \"code_base\": \"0x{:x}\",\n     \"code\": [{{\"asm\": \"function body\", \"bytes\": \"{hex}\"}}]}}",
                0x40_0000 + 0x1000 * k
            );
        }
        s.push_str("],\n");
        let [a, b, c] = p.results;
        let w = if t.swapped() {
            format!("{{\"mem\": [\"0x{a:x}\", 4, \"0x0\"]}}")
        } else {
            format!(
                "{{\"not\": {{\"and\": [{{\"mem\": [\"0x{a:x}\", 4, \"0x1\"]}}, {{\"and\": [{{\"mem\": [\"0x{b:x}\", 4, \"0x2\"]}}, {{\"mem\": [\"0x{c:x}\", 4, \"0x3\"]}}]}}]}}}}"
            )
        };
        let _ = writeln!(s, "   \"witness\": {w},");
        let al = allowed(t).join(",\n      ");
        let _ = write!(
            s,
            "   \"allowed\": {{\n    \"tso\": [\n      {al}],\n    \"sc\": [\n      {al}]}}}}"
        );
    }
    s.push_str("\n]\n}\n");
    s
}

/// `litmus-x86 chan [compile] [--check] [--tmp DIR]`.
pub fn run(args: &[String]) -> Result<(), Error> {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = crate_dir.join("../../examples/litmus-c/chan");
    let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean");
    let jout = crate_dir.join("export/chan.json");
    let mut tmp: PathBuf = std::env::temp_dir();
    let (mut check, mut comp) = (false, false);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "compile" => comp = true,
            "--check" => check = true,
            "--tmp" => {
                tmp = it
                    .next()
                    .ok_or_else(|| Error("--tmp needs a value".into()))?
                    .into();
            }
            _ => return err(format!("unknown argument `{a}`")),
        }
    }
    if comp {
        let n = compile(&root, check, &tmp)?;
        println!(
            "{}: {n} objects",
            if check { "ok, identical" } else { "compiled" }
        );
        return Ok(());
    }
    let tests = ingest(&root)?;
    for (path, body) in [(&out, render_lean(&tests)), (&jout, render_json(&tests))] {
        if check {
            let old = io(path, std::fs::read_to_string(path))?;
            if old != body {
                return err(format!(
                    "{} is out of date; run `cargo run --release -- chan`",
                    path.display()
                ));
            }
            println!(
                "ok: {} tests, {} is up to date",
                tests.len(),
                path.display()
            );
        } else {
            if let Some(d) = path.parent() {
                io(d, std::fs::create_dir_all(d))?;
            }
            io(path, std::fs::write(path, &body))?;
            println!("wrote {} tests to {}", tests.len(), path.display());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nops() {
        assert_eq!(nop_len(&[0x90]), Some(1));
        assert_eq!(nop_len(&[0x66, 0x90]), Some(2));
        assert_eq!(nop_len(&[0x0f, 0x1f, 0x00]), Some(3));
        assert_eq!(nop_len(&[0x0f, 0x1f, 0x80, 0, 0, 0, 0]), Some(7));
        assert_eq!(nop_len(&[0x66, 0x0f, 0x1f, 0x44, 0, 0]), Some(6));
        assert_eq!(
            nop_len(&[0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]),
            Some(11)
        );
        assert_eq!(nop_len(&[0x0f, 0x1f, 0x48, 0]), None);
        assert_eq!(nop_len(&[0xc3]), None);
    }

    #[test]
    fn spins() {
        // mov 0x10080, %eax ; test %eax, %eax ; jne back
        let b = [0x8b, 0x04, 0x25, 0x80, 0, 1, 0, 0x85, 0xc0, 0x75, 0xf5];
        let (len, r, a, c, _) = spin_at(&b).unwrap();
        assert_eq!((len, r, a), (11, 0, 0x10080));
        assert_eq!(c, ".bin .ne (.reg .rax) (.lit 0)");
        // mov 0x10080, %ecx ; cmp $2, %ecx ; jb back
        let b = [
            0x8b, 0x0c, 0x25, 0x80, 0, 1, 0, 0x83, 0xf9, 0x02, 0x72, 0xf4,
        ];
        let (len, r, _, c, _) = spin_at(&b).unwrap();
        assert_eq!((len, r), (12, 1));
        assert_eq!(c, ".bin .ltu (.reg .rcx) (.lit 2)");
        // jbe: loop while r <= 1, i.e. r < 2
        let b = [
            0x8b, 0x04, 0x25, 0x80, 0, 1, 0, 0x83, 0xf8, 0x01, 0x76, 0xf4,
        ];
        assert_eq!(spin_at(&b).unwrap().3, ".bin .ltu (.reg .rax) (.lit 2)");
        // a jump elsewhere is not a spin
        let b = [0x8b, 0x04, 0x25, 0x80, 0, 1, 0, 0x85, 0xc0, 0x75, 0xf0];
        assert!(spin_at(&b).is_none());
        // test of another register is not a spin
        let b = [0x8b, 0x04, 0x25, 0x80, 0, 1, 0, 0x85, 0xc9, 0x75, 0xf5];
        assert!(spin_at(&b).is_none());
    }

    /// The generated module and export are up to date with the committed objects.
    #[test]
    fn outputs_up_to_date() {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = crate_dir.join("../../examples/litmus-c/chan");
        let tests = ingest(&root).unwrap();
        let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean");
        assert_eq!(std::fs::read_to_string(out).unwrap(), render_lean(&tests));
        let j = crate_dir.join("export/chan.json");
        assert_eq!(std::fs::read_to_string(j).unwrap(), render_json(&tests));
    }
}
