//! `cir-f`: the futex C litmus programs of
//! `examples/litmus-c/futex`, compiled with the pinned compilers and checked against their CIR
//! programs by bounded trace inclusion.
//!
//! ```text
//! litmus-x86 cir-f compile [--check]   # build (or check) <test>/obj/<cc>.o and objects.sha256
//! litmus-x86 cir-f [--check]           # write (or check) the generated Lean modules
//! ```
//!
//! `compile` builds every (program, compiler) object with the compilers and flags pinned in
//! `examples/litmus-c/toolchains.txt` (the `c11` pins) and records their sha256 in
//! `examples/litmus-c/futex/objects.sha256`.
//!
//! The generator (**untrusted**; Lean's `Cir.Tv.FTest.tvOk` checks what it emits) reads each
//! committed object and takes out the thread functions `P0`, `P1`, ... in specification order:
//! thread `k` is placed at `0x400000 + 0x1000 k` (Lean's `codeBase k`), and no relocation may
//! fall inside a thread function (the programs use fixed addresses and inline `syscall`s, so
//! there is nothing to relocate). The whole function is kept, every `ret` included: Lean's
//! `sexplore` ends a thread at a `ret`. The CIR program, the instruction and wait budgets and whether
//! threads may block come from `litmus.txt`; the generator does not lift instructions.
//!
//! Output: `Silmaril/X86/Concurrency/Cir/Tv/CFutex/Defs.lean` (one `Cir.Tv.FTest` per
//! (program, compiler)) and `Silmaril/Proofs/X86/Concurrency/Cir/TvCFutex.lean` (one
//! `decide +kernel` per check that the specification asks for: `tvOk` always, then `allOk`
//! (`check all`) or a witness combination (`check witness i j ...`)).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::c11;
use crate::elf::{self, Object};
use crate::litmus::Error;

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

fn io<T>(p: &Path, r: std::io::Result<T>) -> Result<T, Error> {
    r.map_err(|e| Error(format!("{}: {e}", p.display())))
}

fn num(s: &str) -> Result<u64, Error> {
    let r = match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16),
        None => s.parse(),
    };
    r.map_err(|_| Error(format!("bad number `{s}`")))
}

/// A location of a specification.
#[derive(Clone, Debug)]
pub struct FLoc {
    pub name: String,
    pub addr: u64,
    pub size: u64,
    pub init: u64,
}

/// What the generated proofs check for a test.
#[derive(Clone, Debug, PartialEq)]
pub enum Check {
    /// `allOk`: inclusion and the full verdict enumeration.
    All,
    /// `tvOk` and an SC witness from one trace per thread (indices into the CIR traces).
    Witness(Vec<u64>),
    /// `tvOk` and an SC witness from one trace per thread and a schedule (a thread id per
    /// access unit), checked without enumeration.
    Sched(Vec<u64>, Vec<u64>),
    /// `tvOk` only.
    Tv,
}

/// A specification (`<test>/litmus.txt`).
#[derive(Clone, Debug)]
pub struct FSpec {
    pub name: String,
    pub source: String,
    pub locs: Vec<FLoc>,
    pub threads: Vec<String>,
    pub quant: String,
    /// Disjunction of conjunctions of `loc=value` atoms.
    pub cond: Vec<Vec<(String, u64)>>,
    /// SC, TSO, XL.
    pub verdicts: [String; 3],
    pub dom: Vec<u64>,
    /// The CIR program (a Lean term).
    pub cir: String,
    /// Instruction budget per compiler (`fuel N` sets it for every compiler).
    pub fuel: Vec<(String, u64)>,
    /// Futex-wait budget per thread (the CIR wait loops' bound).
    pub waits: u64,
    pub blk: bool,
    pub check: Check,
}

impl FSpec {
    /// Parse a specification.
    pub fn parse(src: &str) -> Result<FSpec, Error> {
        let mut sp = FSpec {
            name: String::new(),
            source: String::new(),
            locs: Vec::new(),
            threads: Vec::new(),
            quant: String::new(),
            cond: Vec::new(),
            verdicts: Default::default(),
            dom: Vec::new(),
            cir: String::new(),
            fuel: Vec::new(),
            waits: 0,
            blk: false,
            check: Check::Tv,
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
                ["loc", n, a, z, i] => sp.locs.push(FLoc {
                    name: (*n).to_string(),
                    addr: num(a)?,
                    size: num(z)?,
                    init: num(i)?,
                }),
                ["thread", f] => sp.threads.push((*f).to_string()),
                ["quant", q @ ("exists" | "forall")] => sp.quant = (*q).to_string(),
                ["cond", rest @ ..] => {
                    for d in rest.join(" ").split("\\/") {
                        let mut conj = Vec::new();
                        for a in d.split("/\\") {
                            let (n, v) = a
                                .trim()
                                .split_once('=')
                                .ok_or_else(|| Error(format!("bad atom `{a}`")))?;
                            conj.push((n.trim().to_string(), num(v.trim())?));
                        }
                        sp.cond.push(conj);
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
                ["cir", t @ ..] => sp.cir = t.join(" "),
                ["fuel", f] => sp.fuel.push(("*".into(), num(f)?)),
                ["fuel", fs @ ..] => {
                    for f in fs {
                        let (c, v) = f
                            .split_once(':')
                            .ok_or_else(|| Error(format!("bad fuel `{f}`")))?;
                        sp.fuel.push((c.to_string(), num(v)?));
                    }
                }
                ["waits", w] => sp.waits = num(w)?,
                ["blk", b @ ("true" | "false")] => sp.blk = *b == "true",
                ["check", "all"] => sp.check = Check::All,
                ["check", "tv"] => sp.check = Check::Tv,
                ["check", "sched", rest @ ..] => {
                    let i = rest
                        .iter()
                        .position(|w| *w == ";")
                        .ok_or_else(|| Error("sched: `;` between indices and schedule".into()))?;
                    let ks = rest[..i].iter().map(|k| num(k)).collect::<Result<_, _>>()?;
                    let sch = rest[i + 1..]
                        .iter()
                        .map(|k| num(k))
                        .collect::<Result<_, _>>()?;
                    sp.check = Check::Sched(ks, sch);
                }
                ["check", "witness", ks @ ..] => {
                    let mut v = Vec::new();
                    for k in ks {
                        v.push(num(k)?);
                    }
                    sp.check = Check::Witness(v);
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
            || sp.cir.is_empty()
            || sp.fuel.is_empty()
        {
            return err("incomplete specification");
        }
        if let Check::Witness(ks) | Check::Sched(ks, _) = &sp.check
            && ks.len() != sp.threads.len()
        {
            return err("one witness index per thread");
        }
        Ok(sp)
    }

    /// The instruction budget for compiler `cc`.
    fn fuel_for(&self, cc: &str) -> Result<u64, Error> {
        self.fuel
            .iter()
            .find(|f| f.0 == cc || f.0 == "*")
            .map(|f| f.1)
            .ok_or_else(|| Error(format!("no fuel for `{cc}`")))
    }

    fn loc(&self, n: &str) -> Result<&FLoc, Error> {
        self.locs
            .iter()
            .find(|l| l.name == n)
            .ok_or_else(|| Error(format!("unknown location `{n}`")))
    }
}

/// The test directories of `index.txt`, with their specifications.
pub fn tests(root: &Path) -> Result<Vec<(String, FSpec)>, Error> {
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
        let spec = FSpec::parse(&src).map_err(|e| Error(format!("{}: {}", sp.display(), e.0)))?;
        out.push((l.to_string(), spec));
    }
    Ok(out)
}

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
                tmp.join(format!("cfutex-{n}.o"))
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
            return err("futex/objects.sha256 is out of date");
        }
    } else {
        io(&mp, std::fs::write(&mp, manifest))?;
    }
    Ok(n)
}

/// The bytes of thread function `name` (whole, every `ret` kept); no relocation may fall
/// inside it.
pub fn ingest_thread(obj: &Object, name: &str) -> Result<Vec<u8>, Error> {
    let sym = obj
        .defined(name, elf::STT_FUNC)
        .ok_or_else(|| Error(format!("no function `{name}`")))?;
    let sec = usize::from(sym.shndx);
    let sbytes = obj
        .section_bytes(sec)?
        .ok_or_else(|| Error(format!("`{name}`: no section bytes")))?;
    let lo = usize::try_from(sym.value).map_err(|_| Error("symbol value".into()))?;
    let len = usize::try_from(sym.size).map_err(|_| Error("symbol size".into()))?;
    let code = sbytes
        .get(lo..lo + len)
        .ok_or_else(|| Error(format!("`{name}` past its section")))?
        .to_vec();
    for r in obj.relas.get(sec).map(Vec::as_slice).unwrap_or_default() {
        let off = usize::try_from(r.offset).map_err(|_| Error("reloc offset".into()))?;
        if off >= lo && off < lo + len {
            let s = &obj.symbols[r.sym].name;
            return err(format!("`{name}`: relocation against `{s}`"));
        }
    }
    if !code.contains(&0xc3) {
        return err(format!("`{name}` has no ret"));
    }
    Ok(code)
}

fn verdict(v: &str) -> String {
    format!(".{v}")
}

fn atom(spec: &FSpec, l: &str, v: u64) -> Result<String, Error> {
    let loc = spec.loc(l)?;
    Ok(format!(".atom (.mem 0x{:x} {} {v})", loc.addr, loc.size))
}

fn fold(op: &str, mut xs: Vec<String>) -> String {
    let mut acc = xs.pop().unwrap_or_default();
    while let Some(a) = xs.pop() {
        acc = format!(".{op} ({a}) ({acc})");
    }
    acc
}

/// Render one test.
fn render_test(
    s: &mut String,
    id: &str,
    dir: &str,
    cc: &str,
    spec: &FSpec,
    ths: &[Vec<u8>],
) -> Result<(), Error> {
    let n = ths.len();
    let _ = writeln!(
        s,
        "/-- `{}` compiled by {cc} (`examples/litmus-c/futex/{dir}`). -/",
        spec.name
    );
    let _ = writeln!(s, "def {id} : FTest where");
    let _ = writeln!(s, "  test := {{");
    let _ = writeln!(s, "    name := \"{}@{cc}\"", spec.name);
    let _ = writeln!(
        s,
        "    source := \"examples/litmus-c/futex/{dir}/{}\"",
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
    let mut ds = Vec::new();
    for conj in &spec.cond {
        let mut cs = Vec::new();
        for (l, v) in conj {
            cs.push(atom(spec, l, *v)?);
        }
        ds.push(fold("and", cs));
    }
    let _ = writeln!(s, "    cond := {}", fold("or", ds));
    let _ = writeln!(s, "    coverage := .tso");
    let _ = writeln!(s, "    tso := some {}", verdict(&spec.verdicts[1]));
    let _ = writeln!(s, "    xl := {}", verdict(&spec.verdicts[2]));
    let _ = writeln!(s, "    sc := some {}", verdict(&spec.verdicts[0]));
    let _ = writeln!(s, "    basis := \"futex C litmus\" }}");
    s.push_str("  threads := [");
    for (k, code) in ths.iter().enumerate() {
        if k > 0 {
            s.push(',');
        }
        let bytes: Vec<String> = code.iter().map(|b| format!("0x{b:02x}")).collect();
        let _ = write!(
            s,
            "\n    {{ base := Silmaril.X86.Litmus.codeBase {k}\n      \
             code := [{}]\n      \
             regions := Silmaril.X86.Litmus.testRegions {n}\n      \
             init := Silmaril.X86.Litmus.initCore (Silmaril.X86.Litmus.codeBase {k}) [] }}",
            bytes.join(", ")
        );
    }
    s.push_str("]\n");
    let _ = writeln!(s, "  prog := {}", spec.cir);
    let dom: Vec<String> = spec.dom.iter().map(u64::to_string).collect();
    let _ = writeln!(s, "  dom := [{}]", dom.join(", "));
    let _ = writeln!(s, "  fuel := {}", spec.fuel_for(cc)?);
    let _ = writeln!(s, "  waits := {}", spec.waits);
    let _ = writeln!(s, "  blk := {}\n", spec.blk);
    Ok(())
}

/// Render both Lean modules; the test identifiers.
pub fn render(root: &Path) -> Result<(String, String, Vec<String>), Error> {
    let tc = toolchains(root)?;
    let mut body = String::new();
    let mut names = Vec::new();
    let mut checks = Vec::new();
    for (dir, spec) in tests(root)? {
        for cc in &tc.compilers {
            let rel = format!("{dir}/obj/{}.o", cc.name);
            let p = root.join(&rel);
            let obj = Object::parse(io(&p, std::fs::read(&p))?)?;
            let ths: Vec<Vec<u8>> = spec
                .threads
                .iter()
                .map(|f| ingest_thread(&obj, f))
                .collect::<Result<_, _>>()
                .map_err(|e| Error(format!("{}@{}: {}", spec.name, cc.name, e.0)))?;
            let id = format!("«{}@{}»", spec.name, cc.name);
            render_test(&mut body, &id, &dir, &cc.name, &spec, &ths)?;
            checks.push((id.clone(), spec.check.clone()));
            names.push(id);
        }
    }
    let mut s = String::new();
    s.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.Sys.Defs\n");
    s.push_str("public import Silmaril.X86.Concurrency.Cir.Futex.Progs.Defs\n\n");
    s.push_str("/-!\n# Futex C litmus tests against their CIR programs (generated)\n\n");
    s.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir-f`) from the objects in\n\
         `examples/litmus-c/futex`; do not edit. `cargo run --release -- cir-f --check` \
         regenerates it and\ncompares byte for byte.\n\n\
         Per (program, compiler): the locations, condition and expected \
         verdicts\nof `litmus.txt`, each thread function's bytes (whole, at `codeBase k`), the \
         CIR program written\nfrom the C source (`Cir.Futex.Progs`), the value domain, the \
         instruction and wait budgets and\nwhether threads may block. Lean's `FTest.tvOk` checks bounded \
         trace inclusion.\n-/\n\n",
    );
    s.push_str("@[expose] public section\n\nnamespace Silmaril.X86.Concurrency.Cir.Tv.CFutex\n\n");
    s.push_str(
        "open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv \
         Silmaril.X86.Concurrency.Cir.Futex.Progs\n\n",
    );
    s.push_str("set_option maxRecDepth 4096\n\n");
    s.push_str(&body);
    s.push_str("/-- Every futex C test. -/\ndef all : List FTest := [\n");
    let _ = writeln!(s, "  {}]", names.join(",\n  "));
    s.push_str("\nend Silmaril.X86.Concurrency.Cir.Tv.CFutex\n");
    let mut pr = String::new();
    pr.push_str("module\n\npublic import Silmaril.X86.Concurrency.Cir.Tv.CFutex.Defs\n");
    pr.push('\n');
    pr.push_str("/-!\n# Futex C litmus tests: per-test kernel checks (generated)\n\n");
    pr.push_str(
        "GENERATED by `tools/litmus-x86` (`cargo run --release -- cir-f`); do not edit.\n\n\
         One `decide +kernel` per check (kernel-checked): \
         `tvOk` for every\ntest, then `allOk` or one SC witness combination where the \
         specification asks for it. What\nthey give is stated in \
         `Silmaril.X86.Concurrency.Cir.Tv.CFutex.Thms`.\n-/\n\n",
    );
    pr.push_str(
        "@[expose] public section\n\nnamespace Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex\n\n",
    );
    pr.push_str(
        "open Silmaril.X86.Concurrency.Cir.Tv Silmaril.X86.Concurrency.Cir.Tv.CFutex\n\n",
    );
    pr.push_str("set_option maxRecDepth 100000\n\n");
    for (id, ck) in &checks {
        let short = id.trim_start_matches('«').trim_end_matches('»');
        let _ = writeln!(
            pr,
            "theorem «{short}_tv» : {id}.tvOk = true := by decide +kernel\n"
        );
        match ck {
            Check::All => {
                let _ = writeln!(
                    pr,
                    "theorem «{short}_ok» : {id}.allOk = true := by decide +kernel\n"
                );
            }
            Check::Witness(ks) => {
                let ks: Vec<String> = ks.iter().map(u64::to_string).collect();
                let _ = writeln!(
                    pr,
                    "theorem «{short}_witness» : {id}.witnessOk [{}] = true := by decide +kernel\n",
                    ks.join(", ")
                );
            }
            Check::Sched(ks, sch) => {
                let ks: Vec<String> = ks.iter().map(u64::to_string).collect();
                let sch: Vec<String> = sch.iter().map(u64::to_string).collect();
                let _ = writeln!(
                    pr,
                    "theorem «{short}_sched» : {id}.schedOk [{}] [{}] = true := by decide +kernel\n",
                    ks.join(", "),
                    sch.join(", ")
                );
            }
            Check::Tv => {}
        }
    }
    pr.push_str("\nend Silmaril.Proofs.X86.Concurrency.Cir.TvCFutex\n");
    Ok((s, pr, names))
}

/// `litmus-x86 cir-f [compile] [--check] [--root DIR] [--tmp DIR]`.
pub fn run(args: &[String]) -> Result<(), Error> {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut root = crate_dir.join("../../examples/litmus-c/futex");
    let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/CFutex/Defs.lean");
    let proofs = crate_dir.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCFutex.lean");
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
                    "{} is out of date; run `cargo run --release -- cir-f`",
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
    fn spec_parses() {
        let s = FSpec::parse(
            "name T\nsource t.c\nloc x 0x10000 4 0\nloc y 0x10040 4 0\nthread P0\nthread P1\n\
             quant forall\ncond x=1 /\\ y=1 \\/ x=0\nverdict forbidden forbidden forbidden\n\
             dom 0 1\ncir flag 1\nfuel gcc:17 clang:16\nblk true\ncheck witness 0 3\n",
        )
        .unwrap();
        assert_eq!(s.cond.len(), 2);
        assert_eq!(s.cond[0].len(), 2);
        assert!(s.blk);
        assert_eq!(s.check, Check::Witness(vec![0, 3]));
        let t = FSpec::parse(
            "name T\nsource t.c\nloc x 0x10000 4 0\nthread P0\nthread P1\nquant exists\n\
             cond x=1\nverdict allowed allowed allowed\ndom 0 1\ncir p\nfuel 3\n\
             check sched 0 0 ; 0 1 1 0\n",
        )
        .unwrap();
        assert_eq!(t.check, Check::Sched(vec![0, 0], vec![0, 1, 1, 0]));
        assert_eq!(s.cir, "flag 1");
        assert_eq!(s.fuel_for("clang").unwrap(), 16);
        assert!(s.fuel_for("icc").is_err());
        assert!(FSpec::parse("name T\n").is_err());
        // one witness index per thread
        assert!(
            FSpec::parse(
                "name T\nsource t.c\nloc x 0x10000 4 0\nthread P0\nquant forall\ncond x=1\n\
             verdict forbidden forbidden forbidden\ndom 0 1\ncir p\nfuel 3\ncheck witness 0 1\n"
            )
            .is_err()
        );
    }

    #[test]
    fn conditions_render() {
        let s = FSpec::parse(
            "name T\nsource t.c\nloc x 0x10000 4 0\nloc y 0x10040 4 0\nthread P0\n\
             quant forall\ncond x=1 /\\ y=1 \\/ x=0\nverdict forbidden forbidden forbidden\n\
             dom 0 1\ncir p\nfuel 3\n",
        )
        .unwrap();
        let mut out = String::new();
        render_test(&mut out, "t", "d", "gcc", &s, &[vec![0xc3]]).unwrap();
        assert!(out.contains(
            "cond := .or (.and (.atom (.mem 0x10000 4 1)) (.atom (.mem 0x10040 4 1))) \
             (.atom (.mem 0x10000 4 0))"
        ));
    }

    /// The generated modules are up to date with the committed objects.
    #[test]
    fn modules_up_to_date() {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = crate_dir.join("../../examples/litmus-c/futex");
        let (text, ptext, _) = render(&root).unwrap();
        let out = crate_dir.join("../../Silmaril/X86/Concurrency/Cir/Tv/CFutex/Defs.lean");
        let proofs = crate_dir.join("../../Silmaril/Proofs/X86/Concurrency/Cir/TvCFutex.lean");
        assert_eq!(std::fs::read_to_string(out).unwrap(), text);
        assert_eq!(std::fs::read_to_string(proofs).unwrap(), ptext);
    }
}
