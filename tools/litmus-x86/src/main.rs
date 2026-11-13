//! `litmus-x86`: import the x86 litmus corpus into a Lean data module.
//!
//! ```text
//! litmus-x86 [generate] [--corpus DIR] [--out FILE] [--as PATH] [--tmp DIR]
//! litmus-x86 --check    [--corpus DIR] [--out FILE] [--as PATH] [--tmp DIR]
//! litmus-x86 list       [--corpus DIR]
//! litmus-x86 export [--check] [--json FILE] [--corpus DIR] [--out FILE] [--as PATH] [--tmp DIR]
//! litmus-x86 c11 compile [--check] [--root DIR] [--tmp DIR]
//! litmus-x86 c11 ingest  [--check] [--root DIR] [--objdump PATH] [--tmp DIR] [--summary]
//! litmus-x86 ingest --obj FILE --spec FILE --variant na|rlx|ra|sc [--compiler NAME]
//!                   [--objdump PATH] [--tmp DIR]
//! litmus-x86 cir [--check] [--json FILE] [--out FILE] [--proofs FILE]
//! litmus-x86 cir-c [compile] [--check] [--root DIR] [--tmp DIR]
//! litmus-x86 c11 cir [--check]
//! litmus-x86 cir-f [compile] [--check] [--root DIR] [--tmp DIR]
//! ```
//!
//! `generate` (the default) reads `corpus/index.txt`, parses every test, assembles its threads
//! with GNU `as`, runs the SC/x86-TSO checker on the TSO-covered tests (the TSO verdict must
//! equal the recorded one), and writes the Lean module. `--check` does the same but compares
//! with the existing file instead of writing it, and fails on any difference. `list` prints
//! the checker's verdicts without assembling. `export` regenerates the Lean module in memory,
//! fails unless it equals the file on disk, and writes (or with `--check`, compares) the JSON
//! export for the hardware harness (`src/export.rs`).
//!
//! `c11` handles the C11 litmus programs of `examples/litmus-c` (`src/c11.rs`):
//! `compile` builds every (program, variant, compiler) object with the pinned compilers and
//! writes (or checks) `objects.sha256`; `ingest` takes the thread functions out of every
//! committed object, relocates them to the fixed layout, lifts and checks them
//! (`src/ingest.rs`) and writes (or checks) `export/c11.json` and `export/c11-meta.json`.
//! `ingest` does the same for one object and prints the test's export JSON.
//!
//! `cir` (`src/cir.rs`) is the untrusted proposer for translation validation into
//! CIR: it decodes every x86-TSO-covered thread of `export/corpus.json` from its bytes, lifts it
//! to CIR statements with a certificate, and writes (or with `--check`, compares)
//! `Silmaril/X86/Concurrency/Cir/Tv/Corpus/Defs.lean`.
//!
//! `cir-c` (`src/cspawn.rs`) compiles the spawn/join C litmus programs of
//! `examples/litmus-c/spawn` with the pinned compilers (`compile`), and proposes marked
//! certificates for their thread functions, written (or with `--check`, compared) to
//! `Silmaril/X86/Concurrency/Cir/Tv/CSpawn/Defs.lean` and its per-test kernel checks.
//!
//! `cir-f` (`src/cfutex.rs`) compiles the futex C litmus programs of
//! `examples/litmus-c/futex` (`compile`) and writes (or with `--check`, compares)
//! `Silmaril/X86/Concurrency/Cir/Tv/CFutex/Defs.lean`, which pairs each thread function's bytes
//! with the CIR program of its C source, and its per-test kernel checks.

mod asm;
mod c11;
mod c11cir;
mod cfutex;
mod chan;
mod checker;
mod cir;
mod cspawn;
mod cspec;
mod elf;
mod emit;
mod export;
mod ingest;
mod insn;
mod json;
mod litmus;
mod model;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use checker::{Mm, Outcome, Verdict};
use emit::{Coverage, Entry};
use litmus::Error;
use model::Model;

/// The pinned herdtools7 revision the `corpus/herdtools7` files were copied from.
pub const HERD_REV: &str = "9f90176bdd6fc2ec3b34a7989c2ba011f538d821";

/// One row of `corpus/index.txt`.
#[derive(Debug, PartialEq, Eq)]
pub struct Row {
    pub path: String,
    pub coverage: Coverage,
    pub expected: Verdict,
    pub basis: String,
}

/// Parse the corpus index.
pub fn parse_index(src: &str) -> Result<Vec<Row>, Error> {
    let mut rows = Vec::new();
    for (n, line) in src.lines().enumerate() {
        let l = line.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let cols: Vec<&str> = l.splitn(4, '|').map(str::trim).collect();
        if cols.len() != 4 {
            return Err(Error(format!("index line {}: expected 4 columns", n + 1)));
        }
        let coverage = match cols[1] {
            "tso" => Coverage::Tso,
            "xl" => Coverage::Xl,
            c => return Err(Error(format!("index line {}: bad coverage `{c}`", n + 1))),
        };
        let expected = match cols[2] {
            "allowed" => Verdict::Allowed,
            "forbidden" => Verdict::Forbidden,
            v => return Err(Error(format!("index line {}: bad verdict `{v}`", n + 1))),
        };
        rows.push(Row {
            path: cols[0].to_string(),
            coverage,
            expected,
            basis: cols[3].to_string(),
        });
    }
    Ok(rows)
}

struct Opts {
    mode: String,
    check: bool,
    json: PathBuf,
    corpus: PathBuf,
    out: PathBuf,
    asm: PathBuf,
    tmp: PathBuf,
}

fn opts() -> Result<Opts, Error> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut o = Opts {
        mode: "generate".into(),
        check: false,
        json: root.join("export/corpus.json"),
        corpus: root.join("corpus"),
        out: root.join("../../Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean"),
        asm: PathBuf::from("as"),
        tmp: std::env::temp_dir(),
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut val = |name: &str| {
            args.next()
                .ok_or_else(|| Error(format!("{name} needs a value")))
        };
        match a.as_str() {
            "generate" | "list" | "export" => o.mode = a,
            "--check" => o.check = true,
            "--json" => o.json = val("--json")?.into(),
            "--corpus" => o.corpus = val("--corpus")?.into(),
            "--out" => o.out = val("--out")?.into(),
            "--as" => o.asm = val("--as")?.into(),
            "--tmp" => o.tmp = val("--tmp")?.into(),
            _ => return Err(Error(format!("unknown argument `{a}`"))),
        }
    }
    Ok(o)
}

/// Load, resolve and check one row (without assembling).
fn load(corpus: &Path, row: &Row) -> Result<(Model, Option<Outcome>, Option<Outcome>), Error> {
    let path = corpus.join(&row.path);
    let src =
        std::fs::read_to_string(&path).map_err(|e| Error(format!("{}: {e}", path.display())))?;
    let t = litmus::parse(&src).map_err(|e| Error(format!("{}: {e}", row.path)))?;
    let m = Model::resolve(&t).map_err(|e| Error(format!("{}: {e}", row.path)))?;
    match row.coverage {
        Coverage::Tso => {
            let tso = checker::check(&m, Mm::Tso).map_err(|e| {
                Error(format!(
                    "{}: tso row outside checker scope: {}",
                    row.path, e.0
                ))
            })?;
            let sc =
                checker::check(&m, Mm::Sc).map_err(|e| Error(format!("{}: {}", row.path, e.0)))?;
            if tso.verdict != row.expected {
                return Err(Error(format!(
                    "{}: checker says TSO {}, index records {}",
                    row.path,
                    tso.verdict.name(),
                    row.expected.name()
                )));
            }
            if sc.verdict == Verdict::Allowed && tso.verdict == Verdict::Forbidden {
                return Err(Error(format!("{}: SC allows what TSO forbids", row.path)));
            }
            Ok((m, Some(tso), Some(sc)))
        }
        Coverage::Xl => {
            if checker::check(&m, Mm::Tso).is_ok() {
                return Err(Error(format!(
                    "{}: xl row is inside the x86-TSO checker's scope",
                    row.path
                )));
            }
            Ok((m, None, None))
        }
    }
}

fn objdump_version(objdump: &Path) -> Result<String, Error> {
    let out = std::process::Command::new(objdump)
        .arg("--version")
        .output()
        .map_err(|e| Error(format!("{}: {e}", objdump.display())))?;
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .next()
        .unwrap_or("")
        .to_string())
}

/// `c11 compile|ingest` and `ingest`.
fn run_c11(args: &[String]) -> Result<(), Error> {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut root = crate_dir.join("../../examples/litmus-c");
    let mut export_dir = crate_dir.join("export");
    let mut objdump = PathBuf::from("objdump");
    let mut tmp = std::env::temp_dir();
    let (mut check, mut summary) = (false, false);
    let (mut obj, mut spec, mut variant, mut compiler) = (None, None, None, "cc".to_string());
    let mut it = args.iter().skip(1);
    let sub = if args[0] == "c11" {
        it.next().cloned().unwrap_or_default()
    } else {
        "one".into()
    };
    while let Some(a) = it.next() {
        let mut val = |n: &str| {
            it.next()
                .cloned()
                .ok_or_else(|| Error(format!("{n} needs a value")))
        };
        match a.as_str() {
            "--check" => check = true,
            "--summary" => summary = true,
            "--root" => root = val("--root")?.into(),
            "--export-dir" => export_dir = val("--export-dir")?.into(),
            "--objdump" => objdump = val("--objdump")?.into(),
            "--tmp" => tmp = val("--tmp")?.into(),
            "--obj" => obj = Some(PathBuf::from(val("--obj")?)),
            "--spec" => spec = Some(PathBuf::from(val("--spec")?)),
            "--variant" => variant = Some(val("--variant")?),
            "--compiler" => compiler = val("--compiler")?,
            _ => return Err(Error(format!("unknown argument `{a}`"))),
        }
    }
    let dir = tmp.join(format!("litmus-x86-c11-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| Error(format!("{}: {e}", dir.display())))?;
    let r = (|| -> Result<(), Error> {
        match sub.as_str() {
            "cir" => c11cir::run(check),
            "compile" => {
                let n = c11::compile(&root, check, &dir)?;
                println!(
                    "ok: {n} objects {}",
                    if check {
                        "recompile byte-identically"
                    } else {
                        "written"
                    }
                );
                Ok(())
            }
            "ingest" => {
                let tests = c11::ingest_all(&root, &objdump, &dir)?;
                let tp = root.join("toolchains.txt");
                let tc = c11::parse_toolchains(
                    &std::fs::read_to_string(&tp)
                        .map_err(|e| Error(format!("{}: {e}", tp.display())))?,
                )?;
                let mut prov = vec![
                    "C sources: examples/litmus-c; objects pinned in examples/litmus-c/objects.sha256.".to_string(),
                    format!("Flags: {}", tc.flags.join(" ")),
                ];
                for cc in &tc.compilers {
                    prov.push(format!("{}: {}", cc.name, cc.version));
                }
                prov.push(format!(
                    "Disassembler (lifting only): {}",
                    objdump_version(&objdump)?
                ));
                prov.push(format!(
                    "Layout: data at 0x{:x} (one 64-byte slot per location, specification order); thread k's code relocated to 0x{:x} + 0x{:x}*k; the final ret is dropped.",
                    model::BASE,
                    ingest::CODE_BASE,
                    ingest::CODE_STRIDE
                ));
                prov.push("xl = tso: every data access is an aligned whole-location 4-byte write-back access (checked by the checker's scope), so Exec.xl_iff_tso_of_tame applies; not computed separately.".into());
                let ex = c11::render_export(&tests, &prov);
                let meta = c11::render_meta(&tests, &tc, &prov);
                let files = [
                    (export_dir.join("c11.json"), ex),
                    (export_dir.join("c11-meta.json"), meta),
                ];
                for (p, text) in &files {
                    if check {
                        let old = std::fs::read_to_string(p)
                            .map_err(|e| Error(format!("{}: {e}", p.display())))?;
                        if &old != text {
                            return Err(Error(format!(
                                "{} is out of date; run `cargo run --release -- c11 ingest`",
                                p.display()
                            )));
                        }
                    } else {
                        std::fs::create_dir_all(&export_dir)
                            .map_err(|e| Error(format!("{}: {e}", export_dir.display())))?;
                        std::fs::write(p, text)
                            .map_err(|e| Error(format!("{}: {e}", p.display())))?;
                    }
                }
                if summary {
                    print!("{}", c11::summary(&tests));
                    for ((cc, k), f) in c11::mapping_table(&tests) {
                        println!(
                            "{cc:6} {k:14} {}",
                            f.into_iter().collect::<Vec<_>>().join(" | ")
                        );
                    }
                }
                println!(
                    "ok: {} tests {}",
                    tests.len(),
                    if check { "up to date" } else { "written" }
                );
                Ok(())
            }
            "one" => {
                let (Some(obj), Some(sp), Some(v)) = (obj.clone(), spec.clone(), variant.clone())
                else {
                    return Err(Error("ingest needs --obj, --spec and --variant".into()));
                };
                let v =
                    cspec::Variant::parse(&v).ok_or_else(|| Error(format!("bad variant `{v}`")))?;
                let src = std::fs::read_to_string(&sp)
                    .map_err(|e| Error(format!("{}: {e}", sp.display())))?;
                let s = cspec::Spec::parse(&src)?;
                let src_path = sp.with_file_name(&s.source);
                let t = c11::ingest_one(
                    &obj,
                    &s,
                    v,
                    &compiler,
                    &s.name,
                    &obj.display().to_string(),
                    &src_path.display().to_string(),
                    &src_path,
                    &objdump,
                    &dir,
                )?;
                print!(
                    "{}",
                    c11::render_export(std::slice::from_ref(&t), &["single-object ingest".into()])
                );
                Ok(())
            }
            s => Err(Error(format!("unknown c11 subcommand `{s}`"))),
        }
    })();
    let _ = std::fs::remove_dir_all(&dir);
    r
}

fn run() -> Result<(), Error> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().is_some_and(|a| a == "c11" || a == "ingest") {
        return run_c11(&args);
    }
    if args.first().is_some_and(|a| a == "cir") {
        return cir::run(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "cir-c") {
        return cspawn::run(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "cir-f") {
        return cfutex::run(&args[1..]);
    }
    if args.first().is_some_and(|a| a == "chan") {
        return chan::run(&args[1..]);
    }
    let o = opts()?;
    let index_path = o.corpus.join("index.txt");
    let index = std::fs::read_to_string(&index_path)
        .map_err(|e| Error(format!("{}: {e}", index_path.display())))?;
    let rows = parse_index(&index)?;
    if o.mode == "list" {
        for r in &rows {
            let (m, tso, sc) = load(&o.corpus, r)?;
            let f = |v: &Option<Outcome>| {
                v.as_ref().map_or("-".to_string(), |o| {
                    format!(
                        "{} ({} execs, {} finals)",
                        o.verdict.name(),
                        o.executions,
                        o.finals
                    )
                })
            };
            println!(
                "{:24} expected={:9} tso={:36} sc={:36} {}",
                m.name,
                r.expected.name(),
                f(&tso),
                f(&sc),
                r.path
            );
        }
        return Ok(());
    }
    let asm_version = asm::version(&o.asm)?;
    let dir = o.tmp.join(format!("litmus-x86-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| Error(format!("{}: {e}", dir.display())))?;
    let mut entries = Vec::new();
    let mut sets: Vec<export::Sets> = Vec::new();
    let mut names = std::collections::BTreeSet::new();
    let result = (|| {
        for r in &rows {
            let (m, tso, sc) = load(&o.corpus, r)?;
            sets.push(match (&tso, &sc) {
                (Some(t), Some(s)) => Some((t.states.clone(), s.states.clone())),
                _ => None,
            });
            let (tso, sc) = (tso.map(|o| o.verdict), sc.map(|o| o.verdict));
            if !names.insert(m.name.clone()) {
                return Err(Error(format!("duplicate test name `{}`", m.name)));
            }
            let code = asm::assemble(&m, &o.asm, &dir)?;
            entries.push(Entry {
                path: r.path.clone(),
                model: m,
                code,
                coverage: r.coverage,
                tso,
                xl: r.expected,
                sc,
                basis: r.basis.clone(),
            });
        }
        Ok(())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    result?;
    let prov = vec![
        format!("herdtools7 files: <https://github.com/herd/herdtools7> at `{HERD_REV}` (CeCILL-B), copied under `tools/litmus-x86/corpus/herdtools7` with `SHA256SUMS`."),
        "Paper tests: Owens, Sarkar, Sewell, *A better x86 memory model: x86-TSO (extended version)*, Appendix A, transcribed under `tools/litmus-x86/corpus/paper`.".into(),
        "Own tests: hand-written under `tools/litmus-x86/corpus/silmaril`.".into(),
        format!("Assembler: `{asm_version}` (`as --64`)."),
        format!("{} tests; layout base 0x{:x}, one 64-byte-aligned slot per location.", entries.len(), model::BASE),
    ];
    let text = emit::render(&entries, &prov)?;
    if o.mode == "export" {
        let old = std::fs::read_to_string(&o.out)
            .map_err(|e| Error(format!("{}: {e}", o.out.display())))?;
        if old != text {
            return Err(Error(format!(
                "{} is out of date; run `cargo run --release -- generate` before exporting",
                o.out.display()
            )));
        }
        let json = export::render(&entries, &sets, &prov)?;
        if o.check {
            let old = std::fs::read_to_string(&o.json)
                .map_err(|e| Error(format!("{}: {e}", o.json.display())))?;
            if old != json {
                return Err(Error(format!(
                    "{} is out of date; run `cargo run --release -- export`",
                    o.json.display()
                )));
            }
            println!(
                "ok: {} tests, {} and {} are up to date",
                entries.len(),
                o.out.display(),
                o.json.display()
            );
        } else {
            if let Some(p) = o.json.parent() {
                std::fs::create_dir_all(p).map_err(|e| Error(format!("{}: {e}", p.display())))?;
            }
            std::fs::write(&o.json, json)
                .map_err(|e| Error(format!("{}: {e}", o.json.display())))?;
            println!("wrote {} tests to {}", entries.len(), o.json.display());
        }
        return Ok(());
    }
    if o.check {
        let old = std::fs::read_to_string(&o.out)
            .map_err(|e| Error(format!("{}: {e}", o.out.display())))?;
        if old != text {
            return Err(Error(format!(
                "{} is out of date; run `cargo run --release -- generate`",
                o.out.display()
            )));
        }
        println!(
            "ok: {} tests, {} is up to date",
            entries.len(),
            o.out.display()
        );
    } else {
        if let Some(p) = o.out.parent() {
            std::fs::create_dir_all(p).map_err(|e| Error(format!("{}: {e}", p.display())))?;
        }
        std::fs::write(&o.out, text).map_err(|e| Error(format!("{}: {e}", o.out.display())))?;
        println!("wrote {} tests to {}", entries.len(), o.out.display());
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("litmus-x86: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_rows() {
        let rows = parse_index("# c\n\na.litmus | tso | allowed | x | y\n").unwrap();
        assert_eq!(rows[0].basis, "x | y");
        assert!(parse_index("a | tso | maybe | b").is_err());
        assert!(parse_index("a | arm | allowed | b").is_err());
    }

    /// The whole corpus: every test parses and resolves, every TSO verdict agrees with the
    /// index, and every XL-only test is outside the TSO checker's scope.
    #[test]
    fn corpus_verdicts() {
        let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus");
        let rows =
            parse_index(&std::fs::read_to_string(corpus.join("index.txt")).unwrap()).unwrap();
        assert!(rows.len() >= 60);
        for r in &rows {
            load(&corpus, r).unwrap();
        }
    }

    /// Every file of the corpus directories is listed in the index.
    #[test]
    fn index_is_complete() {
        let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus");
        let rows =
            parse_index(&std::fs::read_to_string(corpus.join("index.txt")).unwrap()).unwrap();
        for d in ["paper", "silmaril", "herdtools7/catalogue/x86/tests"] {
            for f in std::fs::read_dir(corpus.join(d)).unwrap() {
                let p = f.unwrap().path();
                if p.extension().is_some_and(|e| e == "litmus") {
                    let rel = format!("{d}/{}", p.file_name().unwrap().to_string_lossy());
                    assert!(rows.iter().any(|r| r.path == rel), "{rel} not in index");
                }
            }
        }
    }

    /// Assembling a test with the system `as` yields the expected encodings.
    #[test]
    fn assembles_sb() {
        let t = litmus::parse("X86 SB\n{}\n P0 | P1 ;\n MOV [x],$1 | MOV [y],$1 ;\n MOV EAX,[y] | MOV EAX,[x] ;\n MFENCE | XCHG [x],EAX ;\nexists (0:EAX=0)\n").unwrap();
        let m = Model::resolve(&t).unwrap();
        let dir = std::env::temp_dir().join(format!("litmus-x86-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let code = asm::assemble(&m, Path::new("as"), &dir).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(
            code[0][0].1,
            vec![
                0xc7, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00
            ]
        );
        assert_eq!(code[0][1].1, vec![0x8b, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00]);
        assert_eq!(code[0][2].1, vec![0x0f, 0xae, 0xf0]);
        assert_eq!(code[1][2].1, vec![0x87, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00]);
    }
}
