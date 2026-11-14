//! `cir-c`: the spawn/join C litmus programs of
//! `examples/litmus-c/spawn`, compiled with the pinned compilers and translation-validated into
//! CIR.
//!
//! ```text
//! litmus-x86 cir-c compile [--check]   # build (or check) <test>/obj/<cc>.o and objects.sha256
//! litmus-x86 cir-c [--check]           # write (or check) the generated Lean modules
//! ```
//!
//! `compile` builds every (program, compiler) object with the compilers and flags pinned in
//! `examples/litmus-c/toolchains.txt` (the `c11` pins) and records their sha256 in
//! `examples/litmus-c/spawn/objects.sha256`.
//!
//! The proposer (**untrusted**; Lean's `Cir.Tv.mtvRun` checks everything it emits) reads each
//! committed object and ingests the thread functions `P0`, `P1`, ... in specification order:
//!
//! * thread `k` is placed at `0x400000 + 0x1000 k` (Lean's `codeBase k`);
//! * the only relocations allowed are `R_X86_64_PLT32` against the marker symbols
//!   `cir_spawn<t>` and `cir_join<t>`. They are resolved against fixed stub addresses
//!   (`0x500000 + 0x10 t` and `0x500800 + 0x10 t`), and the offset of each `call` is a cut;
//! * the function must end with `ret` (dropped). Every other byte must decode as one of the
//!   forms of the `cir` proposer (`cir::decode`), with absolute `[disp32]` operands only;
//! * each segment between cuts is lifted with `cir::lift`.
//!
//! Output: `Silmaril/X86/Concurrency/Cir/Tv/CSpawn/Defs.lean` (one `Cir.Tv.CTest` per
//! (program, compiler) that ingests) and `Silmaril/Proofs/X86/Concurrency/Cir/TvCSpawn.lean`
//! (one `decide +kernel` of `CTest.allOk` per test). A (program, compiler) that does not ingest is
//! listed in the module docstring with the reason (for example gcc's unlocked `addl $1, m`,
//! which is not a `cir::decode` form).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::c11;
use crate::cir;
use crate::elf::{self, Object};
use crate::litmus::Error;

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

fn io<T>(p: &Path, r: std::io::Result<T>) -> Result<T, Error> {
    r.map_err(|e| Error(format!("{}: {e}", p.display())))
}

/// The address of the stub of a marker.
pub fn stub_addr(spawn: bool, t: u32) -> u64 {
    if spawn {
        0x50_0000 + 0x10 * u64::from(t)
    } else {
        0x50_0800 + 0x10 * u64::from(t)
    }
}

/// The marker a symbol names: (`spawn`?, thread).
pub fn marker(sym: &str) -> Option<(bool, u32)> {
    if let Some(t) = sym.strip_prefix("cir_spawn") {
        return t.parse().ok().map(|t| (true, t));
    }
    sym.strip_prefix("cir_join")
        .and_then(|t| t.parse().ok())
        .map(|t| (false, t))
}

/// A location of a specification.
#[derive(Clone, Debug)]
pub struct SLoc {
    pub name: String,
    pub addr: u64,
    pub size: u64,
    pub init: u64,
}

/// A specification (`<test>/litmus.txt`).
#[derive(Clone, Debug)]
pub struct Spec {
    pub name: String,
    pub source: String,
    pub locs: Vec<SLoc>,
    /// Thread functions in order, and whether each is spawned.
    pub threads: Vec<(String, bool)>,
    pub quant: String,
    /// Conjunction of `loc=value` atoms.
    pub cond: Vec<(String, u64)>,
    /// SC, TSO, XL.
    pub verdicts: [String; 3],
    pub dom: Vec<u64>,
}

fn num(s: &str) -> Result<u64, Error> {
    let r = match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16),
        None => s.parse(),
    };
    r.map_err(|_| Error(format!("bad number `{s}`")))
}

impl Spec {
    /// Parse a specification.
    pub fn parse(src: &str) -> Result<Spec, Error> {
        let mut sp = Spec {
            name: String::new(),
            source: String::new(),
            locs: Vec::new(),
            threads: Vec::new(),
            quant: String::new(),
            cond: Vec::new(),
            verdicts: Default::default(),
            dom: Vec::new(),
        };
        for line in src.lines() {
            let l = line.trim();
            if l.is_empty() || l.starts_with('#') {
                continue;
            }
            let w: Vec<&str> = l.split_whitespace().collect();
            match w.as_slice() {
                ["name", n] => sp.name = (*n).to_string(),
                ["source", s] => sp.source = (*s).to_string(),
                ["loc", n, a, z, i] => sp.locs.push(SLoc {
                    name: (*n).to_string(),
                    addr: num(a)?,
                    size: num(z)?,
                    init: num(i)?,
                }),
                ["thread", f] => sp.threads.push(((*f).to_string(), false)),
                ["thread", f, "spawned"] => sp.threads.push(((*f).to_string(), true)),
                ["quant", q @ ("exists" | "forall")] => sp.quant = (*q).to_string(),
                ["cond", rest @ ..] => {
                    for a in rest.join(" ").split("/\\") {
                        let (n, v) = a
                            .trim()
                            .split_once('=')
                            .ok_or_else(|| Error(format!("bad atom `{a}`")))?;
                        sp.cond.push((n.trim().to_string(), num(v.trim())?));
                    }
                }
                ["verdict", a, b, c] => {
                    for v in [a, b, c] {
                        if !matches!(*v, "allowed" | "forbidden") {
                            return err(format!("bad verdict `{v}`"));
                        }
                    }
                    sp.verdicts = [(*a).to_string(), (*b).to_string(), (*c).to_string()];
                }
                ["dom", vs @ ..] => {
                    for v in vs {
                        sp.dom.push(num(v)?);
                    }
                }
                _ => return err(format!("bad specification line `{l}`")),
            }
        }
        if sp.name.is_empty()
            || sp.source.is_empty()
            || sp.threads.is_empty()
            || sp.quant.is_empty()
            || sp.cond.is_empty()
            || sp.verdicts[0].is_empty()
            || sp.dom.is_empty()
        {
            return err("incomplete specification");
        }
        Ok(sp)
    }

    fn loc(&self, n: &str) -> Result<&SLoc, Error> {
        self.locs
            .iter()
            .find(|l| l.name == n)
            .ok_or_else(|| Error(format!("unknown location `{n}`")))
    }
}

/// The test directories of `index.txt`, with their specifications.
pub fn tests(root: &Path) -> Result<Vec<(String, Spec)>, Error> {
    let ip = root.join("index.txt");
    let idx = io(&ip, std::fs::read_to_string(&ip))?;
    let mut out = Vec::new();
    for l in idx.lines() {
        let l = l.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let sp = root.join(l).join("litmus.txt");
        let src = io(&sp, std::fs::read_to_string(&sp))?;
        let spec = Spec::parse(&src).map_err(|e| Error(format!("{}: {}", sp.display(), e.0)))?;
        out.push((l.to_string(), spec));
    }
    Ok(out)
}

/// The pinned toolchains (shared with `c11`).
fn toolchains(root: &Path) -> Result<c11::Toolchains, Error> {
    let tp = root.join("../toolchains.txt");
    c11::parse_toolchains(&io(&tp, std::fs::read_to_string(&tp))?)
}

/// Compile every (program, compiler) into `<dir>/obj/<cc>.o`, or with `check` into `tmp` and
/// compare byte for byte; write (or compare) `objects.sha256`.
pub fn compile(root: &Path, check: bool, tmp: &Path) -> Result<usize, Error> {
    let tc = toolchains(root)?;
    c11::verify_toolchains(&tc)?;
    let mut manifest = String::new();
    let mut n = 0;
    for (dir, spec) in tests(root)? {
        for cc in &tc.compilers {
            let rel = format!("{dir}/obj/{}.o", cc.name);
            let dest = if check {
                tmp.join(format!("cspawn-{n}.o"))
            } else {
                let p = root.join(&rel);
                if let Some(d) = p.parent() {
                    io(d, std::fs::create_dir_all(d))?;
                }
                p
            };
            let dest = if dest.is_absolute() {
                dest
            } else {
                io(&dest, std::env::current_dir())?.join(&dest)
            };
            let st = io(
                &cc.driver,
                Command::new(&cc.driver)
                    .current_dir(root.join(&dir))
                    .args(&tc.flags)
                    .arg("-c")
                    .arg(&spec.source)
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
    let mp = root.join("objects.sha256");
    if check {
        if io(&mp, std::fs::read_to_string(&mp))? != manifest {
            return err("spawn/objects.sha256 is out of date");
        }
    } else {
        io(&mp, std::fs::write(&mp, manifest))?;
    }
    Ok(n)
}

/// One ingested thread.
pub struct CThread {
    /// The relocated bytes without the final `ret`.
    pub code: Vec<u8>,
    /// Code offsets of the marker calls, with (`spawn`?, thread).
    pub cuts: Vec<(usize, (bool, u32))>,
    /// Per segment: (asm text, length, CIR statements).
    pub segs: Vec<Vec<(String, usize, Vec<String>)>>,
    pub scratch: Option<u8>,
    pub spawned: bool,
}

/// Split one segment into instructions (the unique length at which `cir::decode` succeeds).
fn decode_seg(bytes: &[u8]) -> Result<Vec<(usize, cir::Insn)>, Error> {
    let mut out = Vec::new();
    let mut o = 0;
    while o < bytes.len() {
        let found = (1..=15)
            .filter(|n| o + n <= bytes.len())
            .find_map(|n| cir::decode(&bytes[o..o + n]).ok().map(|i| (n, i)));
        match found {
            Some((n, i)) => {
                out.push((n, i));
                o += n;
            }
            None => {
                let end = (o + 8).min(bytes.len());
                return err(format!(
                    "unsupported instruction at offset {o}: {}",
                    bytes[o..end]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect::<String>()
                ));
            }
        }
    }
    Ok(out)
}

fn asm_text(i: &cir::Insn) -> String {
    format!("{i:?}")
}

/// Ingest thread function `name` of `obj` as thread `k`.
pub fn ingest_thread(obj: &Object, name: &str, k: usize, spawned: bool) -> Result<CThread, Error> {
    let sym = obj
        .defined(name, elf::STT_FUNC)
        .ok_or_else(|| Error(format!("no function `{name}`")))?;
    let sec = usize::from(sym.shndx);
    let sbytes = obj
        .section_bytes(sec)?
        .ok_or_else(|| Error(format!("`{name}`: no section bytes")))?;
    let lo = usize::try_from(sym.value).map_err(|_| Error("symbol value".into()))?;
    let len = usize::try_from(sym.size).map_err(|_| Error("symbol size".into()))?;
    let mut code = sbytes
        .get(lo..lo + len)
        .ok_or_else(|| Error(format!("`{name}` past its section")))?
        .to_vec();
    if code.last() != Some(&0xc3) {
        return err(format!("`{name}` does not end with ret"));
    }
    code.pop();
    let base = 0x40_0000 + 0x1000 * k as u64;
    let mut cuts = Vec::new();
    for r in obj.relas.get(sec).map(Vec::as_slice).unwrap_or_default() {
        let off = usize::try_from(r.offset).map_err(|_| Error("reloc offset".into()))?;
        if off < lo || off >= lo + len {
            continue;
        }
        let o = off - lo;
        let s = &obj.symbols[r.sym].name;
        let Some(m) = marker(s) else {
            return err(format!("`{name}`: relocation against `{s}`"));
        };
        if r.kind != elf::R_X86_64_PLT32 || o == 0 || code.get(o - 1) != Some(&0xe8) {
            return err(format!("`{name}`: `{s}` is not a call rel32"));
        }
        let p = base as i64 + o as i64;
        let v = stub_addr(m.0, m.1) as i64 + r.addend - p;
        let v = i32::try_from(v).map_err(|_| Error("call out of range".into()))?;
        code[o..o + 4].copy_from_slice(&v.to_le_bytes());
        cuts.push((o - 1, m));
    }
    cuts.sort_by_key(|c| c.0);
    // segments
    let mut raw = Vec::new();
    let mut start = 0;
    for (c, _) in &cuts {
        raw.push(&code[start..*c]);
        start = c + 5;
    }
    raw.push(&code[start..]);
    let mut decoded = Vec::new();
    let mut used: Vec<u8> = Vec::new();
    for seg in &raw {
        let d = decode_seg(seg).map_err(|e| Error(format!("`{name}`: {}", e.0)))?;
        for (_, i) in &d {
            used.extend(i.regs());
        }
        decoded.push(d);
    }
    let needs = decoded.iter().flatten().any(|(_, i)| i.needs_scratch());
    let scratch = if needs {
        cir::SCRATCH.iter().copied().find(|r| !used.contains(r))
    } else {
        None
    };
    let mut segs = Vec::new();
    for d in &decoded {
        let mut items = Vec::new();
        for (n, i) in d {
            items.push((asm_text(i), *n, cir::lift(i, scratch)?));
        }
        segs.push(items);
    }
    Ok(CThread {
        code,
        cuts,
        segs,
        scratch,
        spawned,
    })
}

fn verdict(v: &str) -> String {
    format!(".{v}")
}

fn mark(m: (bool, u32)) -> String {
    if m.0 {
        format!(".spawn {}", m.1)
    } else {
        format!(".join {}", m.1)
    }
}

/// Render one test.
fn render_test(
    s: &mut String,
    id: &str,
    dir: &str,
    cc: &str,
    spec: &Spec,
    ths: &[CThread],
) -> Result<(), Error> {
    let n = ths.len();
    let _ = writeln!(
        s,
        "/-- `{}` compiled by {cc} (`examples/litmus-c/spawn/{dir}`), translation-validated. -/",
        spec.name
    );
    let _ = writeln!(s, "def {id} : CTest where");
    let _ = writeln!(s, "  test := {{");
    let _ = writeln!(s, "    name := \"{}@{cc}\"", spec.name);
    let _ = writeln!(
        s,
        "    source := \"examples/litmus-c/spawn/{dir}/{}\"",
        spec.source
    );
    let _ = writeln!(s, "    doc := \"\"");
    let locs: Vec<String> = spec
        .locs
        .iter()
        .map(|l| format!("⟨\"{}\", 0x{:x}, {}, {}⟩", l.name, l.addr, l.size, l.init))
        .collect();
    let _ = writeln!(s, "    locs := [{}]", locs.join(", "));
    let _ = writeln!(s, "    threads := []");
    let _ = writeln!(
        s,
        "    quant := {}",
        if spec.quant == "exists" {
            ".exists_"
        } else {
            ".forall_"
        }
    );
    let mut atoms = Vec::new();
    for (l, v) in &spec.cond {
        let loc = spec.loc(l)?;
        atoms.push(format!(".atom (.mem 0x{:x} {} {v})", loc.addr, loc.size));
    }
    let mut cond = atoms.pop().unwrap_or_default();
    while let Some(a) = atoms.pop() {
        cond = format!(".and ({a}) ({cond})");
    }
    let _ = writeln!(s, "    cond := {cond}");
    let _ = writeln!(s, "    coverage := .tso");
    let _ = writeln!(s, "    tso := some {}", verdict(&spec.verdicts[1]));
    let _ = writeln!(s, "    xl := {}", verdict(&spec.verdicts[2]));
    let _ = writeln!(s, "    sc := some {}", verdict(&spec.verdicts[0]));
    let _ = writeln!(s, "    basis := \"spawn/join C litmus\" }}");
    s.push_str("  threads := [");
    for (k, th) in ths.iter().enumerate() {
        if k > 0 {
            s.push(',');
        }
        let bytes: Vec<String> = th.code.iter().map(|b| format!("0x{b:02x}")).collect();
        let cuts: Vec<String> = th.cuts.iter().map(|c| c.0.to_string()).collect();
        let _ = write!(
            s,
            "\n    {{ base := Silmaril.X86.Litmus.codeBase {k}\n      \
             code := [{}]\n      \
             regions := Silmaril.X86.Litmus.testRegions {n}\n      \
             init := Silmaril.X86.Litmus.initCore (Silmaril.X86.Litmus.codeBase {k}) []\n      \
             cuts := [{}]\n      spawned := {} }}",
            bytes.join(", "),
            cuts.join(", "),
            th.spawned
        );
    }
    s.push_str("]\n");
    let mut marks: Vec<(bool, u32)> = ths
        .iter()
        .flat_map(|t| t.cuts.iter().map(|c| c.1))
        .collect();
    marks.sort();
    marks.dedup();
    let stubs: Vec<String> = marks
        .iter()
        .map(|m| format!("(0x{:x}, {})", stub_addr(m.0, m.1), mark(*m)))
        .collect();
    let _ = writeln!(s, "  stubs := [{}]", stubs.join(", "));
    s.push_str("  certs := [");
    for (k, th) in ths.iter().enumerate() {
        if k > 0 {
            s.push(',');
        }
        let _ = write!(s, "\n    -- thread {k}");
        if let Some(sc) = th.scratch {
            let _ = write!(s, " (scratch {})", cir::REGS[usize::from(sc)]);
        }
        s.push_str("\n    { pro := [],\n      segs := [");
        for (j, seg) in th.segs.iter().enumerate() {
            if j > 0 {
                let _ = write!(s, ",\n        -- call {}", mark(th.cuts[j - 1].1));
            }
            s.push_str("\n        [");
            for (q, (asm, len, ops)) in seg.iter().enumerate() {
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
        s.push_str("] }");
    }
    s.push_str("]\n");
    let dom: Vec<String> = spec.dom.iter().map(u64::to_string).collect();
    let _ = writeln!(s, "  dom := [{}]", dom.join(", "));
    let fuel = ths
        .iter()
        .flat_map(|t| t.segs.iter().map(Vec::len))
        .max()
        .unwrap_or(0)
        + 1;
    let _ = writeln!(s, "  fuel := {fuel}\n");
    Ok(())
}

/// Render both Lean modules; the test identifiers.
pub fn render(root: &Path) -> Result<(String, String, Vec<String>), Error> {
    let tc = toolchains(root)?;
    let mut body = String::new();
    let mut names = Vec::new();
    let mut refused = Vec::new();
    for (dir, spec) in tests(root)? {
        for cc in &tc.compilers {
            let rel = format!("{dir}/obj/{}.o", cc.name);
            let p = root.join(&rel);
            let obj = Object::parse(io(&p, std::fs::read(&p))?)?;
            let ths: Result<Vec<CThread>, Error> = spec
                .threads
                .iter()
                .enumerate()
                .map(|(k, (f, sp))| ingest_thread(&obj, f, k, *sp))
                .collect();
            match ths {
                Ok(ths) => {
                    let id = format!("«{}@{}»", spec.name, cc.name);
                    render_test(&mut body, &id, &dir, &cc.name, &spec, &ths)?;
                    names.push(id);
                }
                Err(e) => refused.push(format!("{}@{}: {}", spec.name, cc.name, e.0)),
            }
        }
    }
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.Marked.Defs\n\n");
    s.push_str("/-!\n# Spawn/join C litmus tests, translation-validated into CIR (generated)\n\n");
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir-c`) from the objects in\n\
         `examples/litmus-c/spawn`; do not edit. `cargo run --release -- cir-c --check` regenerates \
         it and\ncompares byte for byte.\n\n\
         Per (program, compiler): the locations, condition and expected \
         verdicts\nof `litmus.txt`, each thread function's relocated bytes (final `ret` dropped) \
         with the offsets of\nits marker calls, the marker stubs, and the **untrusted** proposer's \
         marked certificate (per\nsegment, per instruction: its decoded form in a comment, its \
         length and its CIR statements).\nLean's `mtvRun` checks the certificate against the \
         bytes.\n",
    );
    if refused.is_empty() {
        s.push_str("\nEvery (program, compiler) ingests.\n");
    } else {
        s.push_str("\nNot ingested (the proposer refuses them):\n\n");
        for r in &refused {
            let _ = writeln!(s, "* {}", r.replace('`', ""));
        }
    }
    s.push_str(
        "-/\n\n@[expose] public section\n\nnamespace Silmaril.X86.Concurrency.Cir.Tv.CSpawn\n\n",
    );
    s.push_str("open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv\n\n");
    s.push_str("set_option maxRecDepth 4096\n\n");
    s.push_str(&body);
    s.push_str("/-- Every translation-validated C test. -/\ndef all : List CTest := [\n");
    let _ = writeln!(s, "  {}]", names.join(",\n  "));
    s.push_str("\nend Silmaril.X86.Concurrency.Cir.Tv.CSpawn\n");
    let mut pr = String::new();
    pr.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.CSpawn.Defs\n\n");
    pr.push_str("/-!\n# Spawn/join C litmus tests: per-test kernel checks (generated)\n\n");
    pr.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir-c`); do not edit.\n\n\
         One `decide +kernel` per test of `CTest.allOk` (kernel-checked). What\nthey give is stated in \
         `Silmaril.X86.Concurrency.Cir.Tv.CSpawn.Thms`.\n-/\n\n",
    );
    pr.push_str(
        "@[expose] public section\n\nnamespace Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawn\n\n",
    );
    pr.push_str(
        "open Silmaril.X86.Concurrency.Cir.Tv Silmaril.X86.Concurrency.Cir.Tv.CSpawn\n\n",
    );
    for id in &names {
        let short = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(
            pr,
            "theorem «{short}_ok» : {id}.allOk = true := by decide +kernel\n"
        );
    }
    pr.push_str("/-- Every test passes. -/\ntheorem all_ok : ∀ c ∈ all, c.allOk = true := by\n");
    pr.push_str(
        "  intro c hc\n  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hc\n",
    );
    pr.push_str("  rcases hc with ");
    let pats: Vec<&str> = names.iter().map(|_| "rfl").collect();
    pr.push_str(&pats.join(" | "));
    pr.push('\n');
    for id in &names {
        let short = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(pr, "  · exact «{short}_ok»");
    }
    pr.push_str("\nend Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawn\n");
    Ok((s, pr, names))
}

/// `litmus-x86 cir-c [compile] [--check] [--root DIR] [--tmp DIR]`.
pub fn run(args: &[String]) -> Result<(), Error> {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut root = crate_dir.join("../../examples/litmus-c/spawn");
    let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/CSpawn/Defs.lean");
    let proofs = crate_dir.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCSpawn.lean");
    let mut tmp: PathBuf = std::env::temp_dir();
    let (mut check, mut comp) = (false, false);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "compile" => comp = true,
            "--check" => check = true,
            "--root" => {
                root = it
                    .next()
                    .ok_or_else(|| Error("--root needs a value".into()))?
                    .into();
            }
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
    let (text, ptext, names) = render(&root)?;
    for (path, body) in [(&out, &text), (&proofs, &ptext)] {
        if check {
            let old = io(path, std::fs::read_to_string(path))?;
            if &old != body {
                return err(format!(
                    "{} is out of date; run `cargo run --release -- cir-c`",
                    path.display()
                ));
            }
            println!(
                "ok: {} tests, {} is up to date",
                names.len(),
                path.display()
            );
        } else {
            if let Some(p) = path.parent() {
                io(p, std::fs::create_dir_all(p))?;
            }
            io(path, std::fs::write(path, body))?;
            println!("wrote {} tests to {}", names.len(), path.display());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn markers() {
        assert_eq!(marker("cir_spawn1"), Some((true, 1)));
        assert_eq!(marker("cir_join12"), Some((false, 12)));
        assert_eq!(marker("cir_joinx"), None);
        assert_eq!(marker("pthread_create"), None);
        assert_eq!(stub_addr(true, 1), 0x50_0010);
        assert_eq!(stub_addr(false, 2), 0x50_0820);
    }

    #[test]
    fn segments_decode() {
        // movl $1, 0x10000 ; movl 0x10000, %eax
        let b = [
            0xc7, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x8b, 0x04, 0x25,
            0x00, 0x00, 0x01, 0x00,
        ];
        let d = decode_seg(&b).unwrap();
        assert_eq!(d.len(), 2);
        assert_eq!(d[0].0, 11);
        assert_eq!(d[1].0, 7);
        // gcc's unlocked `addl $1, 0x10000` is refused
        assert!(decode_seg(&[0x83, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01]).is_err());
    }

    #[test]
    fn spec_parses() {
        let s = Spec::parse(
            "name T\nsource t.c\nloc x 0x10000 4 0\nthread P0\nthread P1 spawned\n\
             quant forall\ncond x=1 /\\ x=1\nverdict forbidden forbidden allowed\ndom 0 1\n",
        )
        .unwrap();
        assert_eq!(s.threads, vec![("P0".into(), false), ("P1".into(), true)]);
        assert_eq!(s.cond.len(), 2);
        assert!(Spec::parse("name T\n").is_err());
    }

    /// The generated modules are up to date with the committed objects.
    #[test]
    fn modules_up_to_date() {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = crate_dir.join("../../examples/litmus-c/spawn");
        let (text, ptext, _) = render(&root).unwrap();
        let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/CSpawn/Defs.lean");
        let proofs = crate_dir.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCSpawn.lean");
        assert_eq!(std::fs::read_to_string(out).unwrap(), text);
        assert_eq!(std::fs::read_to_string(proofs).unwrap(), ptext);
    }
}
