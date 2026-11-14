//! `litmus-run`: run the x86 litmus corpus natively and check observed ⊆ allowed.
//!
//! ```text
//! litmus-run [--json FILE] [--test NAME]... [--time SECS] [--iters N] [--seed N]
//!            [--delay N] [--model tso|sc] [--ci] [--report FILE] [--list]
//! ```
//!
//! Each test of `tools/litmus-x86/export/corpus.json` runs with one pinned thread per litmus
//! thread (distinct physical cores), a spin barrier per iteration and a random delay, for
//! `--time` seconds (default 2) or `--iters` iterations. The thread code is the corpus bytes
//! (the same bytes as `Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean`) in an RX mapping, and
//! the locations live at their fixed corpus addresses. Checks:
//!
//! * TSO-covered tests: every observed final state is in the model-allowed set (`--model`,
//!   x86-TSO by default; `sc` is a negative control that must fail on SB-like tests);
//! * XL-only tests: if the recorded XL verdict is `forbidden`, the witness is never observed.
//!
//! The exit status is 1 if any check fails. `--ci` fixes the seed (so the delay sequence) and
//! the iteration count (`CI_ITERS`, with a `CI_TIME` cap per test; a capped run is reported as
//! `CAPPED`, not as a failure). The observed outcomes still depend on the hardware.
//! Never observing a forbidden outcome is evidence, not proof.

mod corpus;
mod json;
mod native;
mod wrap;

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use corpus::{Outcome, Test, Verdict};

/// The fixed seed of `--ci`.
pub const CI_SEED: u64 = 0x5369_6c4c_6974_3500;
/// The iteration count of `--ci`.
pub const CI_ITERS: u64 = 3_000_000;
/// The time cap of `--ci` per test.
pub const CI_TIME: f64 = 5.0;
/// The default maximum delay, in loop iterations.
pub const DEFAULT_DELAY: u64 = 256;

/// The model the observed outcomes of TSO-covered tests are checked against.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Model {
    Tso,
    Sc,
}

/// The assessment of one run.
#[derive(Clone, Debug)]
pub struct Assessment {
    /// Observed outcomes outside the allowed set (TSO-covered tests), with counts.
    pub outside: Vec<(Outcome, u64)>,
    /// Number of iterations whose final state satisfies the witness.
    pub witness: u64,
    /// The XL verdict is `forbidden` and the witness was observed (XL-only tests).
    pub xl_violation: bool,
    /// Observed outcomes that TSO allows and SC forbids, with counts.
    pub weak: Vec<(Outcome, u64)>,
    /// Number of outcomes TSO allows and SC forbids (TSO-covered tests).
    pub weak_allowed: usize,
    /// Number of TSO-allowed outcomes never observed.
    pub unseen_allowed: usize,
}

impl Assessment {
    /// Whether the run passed its checks.
    pub fn ok(&self) -> bool {
        self.outside.is_empty() && !self.xl_violation
    }
}

/// Check a histogram against a test's data.
pub fn assess(
    t: &Test,
    model: Model,
    hist: &std::collections::BTreeMap<Outcome, u64>,
) -> Result<Assessment, String> {
    let mut a = Assessment {
        outside: Vec::new(),
        witness: 0,
        xl_violation: false,
        weak: Vec::new(),
        weak_allowed: 0,
        unseen_allowed: 0,
    };
    for (o, n) in hist {
        let w = t
            .witness_holds(o)
            .ok_or_else(|| format!("{}: witness cannot be evaluated on {}", t.name, t.show(o)))?;
        if w {
            a.witness += n;
        }
    }
    match &t.allowed {
        Some(al) => {
            let set = match model {
                Model::Tso => &al.tso,
                Model::Sc => &al.sc,
            };
            a.outside = hist
                .iter()
                .filter(|(o, _)| !set.contains(*o))
                .map(|(o, n)| (o.clone(), *n))
                .collect();
            let weak: BTreeSet<&Outcome> = al.tso.difference(&al.sc).collect();
            a.weak_allowed = weak.len();
            a.weak = hist
                .iter()
                .filter(|(o, _)| weak.contains(o))
                .map(|(o, n)| (o.clone(), *n))
                .collect();
            a.unseen_allowed = al.tso.iter().filter(|o| !hist.contains_key(*o)).count();
        }
        None => {
            if t.tso_covered {
                return Err(format!("{}: TSO-covered test without allowed sets", t.name));
            }
            a.xl_violation = t.xl == Verdict::Forbidden && a.witness > 0;
        }
    }
    Ok(a)
}

struct Opts {
    json: PathBuf,
    tests: Vec<String>,
    time: f64,
    iters: Option<u64>,
    seed: u64,
    delay: u64,
    model: Model,
    ci: bool,
    report: Option<PathBuf>,
    list: bool,
}

fn opts() -> Result<Opts, String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut o = Opts {
        json: root.join("../litmus-x86/export/corpus.json"),
        tests: Vec::new(),
        time: 2.0,
        iters: None,
        seed: 0,
        delay: DEFAULT_DELAY,
        model: Model::Tso,
        ci: false,
        report: None,
        list: false,
    };
    let (mut time, mut iters, mut seed) = (None, None, None);
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut val = || args.next().ok_or_else(|| format!("{a} needs a value"));
        let num = |s: String| -> Result<u64, String> {
            match s.strip_prefix("0x") {
                Some(h) => u64::from_str_radix(h, 16),
                None => s.parse(),
            }
            .map_err(|_| format!("bad number `{s}`"))
        };
        match a.as_str() {
            "--json" => o.json = val()?.into(),
            "--test" => o.tests.push(val()?),
            "--time" => {
                let v = val()?;
                time = Some(v.parse::<f64>().map_err(|_| format!("bad time `{v}`"))?)
            }
            "--iters" => iters = Some(num(val()?)?),
            "--seed" => seed = Some(num(val()?)?),
            "--delay" => o.delay = num(val()?)?,
            "--model" => {
                o.model = match val()?.as_str() {
                    "tso" => Model::Tso,
                    "sc" => Model::Sc,
                    m => return Err(format!("unknown model `{m}`")),
                }
            }
            "--ci" => o.ci = true,
            "--report" => o.report = Some(val()?.into()),
            "--list" => o.list = true,
            _ => return Err(format!("unknown argument `{a}`")),
        }
    }
    if o.ci {
        o.seed = CI_SEED;
        o.iters = Some(CI_ITERS);
        o.time = CI_TIME;
    } else {
        o.seed = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(1, |d| d.as_nanos() as u64);
    }
    o.time = time.unwrap_or(o.time);
    o.iters = iters.or(o.iters);
    o.seed = seed.unwrap_or(o.seed);
    if !(o.time > 0.0 && o.time <= 600.0) {
        return Err("--time must be in (0, 600] seconds".into());
    }
    Ok(o)
}

fn cpuinfo(field: &str) -> String {
    std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.split(':').next().is_some_and(|k| k.trim() == field))
                .and_then(|l| l.split_once(':'))
                .map(|(_, v)| v.trim().to_string())
        })
        .unwrap_or_else(|| "?".into())
}

fn verdict_name(v: Option<Verdict>) -> &'static str {
    match v {
        Some(Verdict::Allowed) => "allowed",
        Some(Verdict::Forbidden) => "forbidden",
        None => "-",
    }
}

fn run() -> Result<bool, String> {
    let o = opts()?;
    let src = std::fs::read_to_string(&o.json).map_err(|e| format!("{}: {e}", o.json.display()))?;
    let corpus = corpus::parse(&src).map_err(|e| format!("{}: {e}", o.json.display()))?;
    let tests: Vec<(usize, &Test)> = corpus
        .tests
        .iter()
        .enumerate()
        .filter(|(_, t)| o.tests.is_empty() || o.tests.contains(&t.name))
        .collect();
    if let Some(n) = o
        .tests
        .iter()
        .find(|n| !corpus.tests.iter().any(|t| &t.name == *n))
    {
        return Err(format!("no test named `{n}`"));
    }
    if o.list {
        for (_, t) in &tests {
            println!(
                "{:24} threads={} tso={:9} sc={:9} xl={:9} allowed={}",
                t.name,
                t.threads.len(),
                verdict_name(t.tso),
                verdict_name(t.sc),
                verdict_name(Some(t.xl)),
                t.allowed.as_ref().map_or(0, |a| a.tso.len())
            );
        }
        return Ok(true);
    }
    let cores = native::physical_cores();
    let need = tests
        .iter()
        .map(|(_, t)| t.threads.len())
        .max()
        .unwrap_or(0);
    if cores.len() < need {
        return Err(format!(
            "need {need} physical cores, only {} available to this process",
            cores.len()
        ));
    }
    let data = native::Mapping::data()?;
    let p = native::Params {
        iters: o.iters,
        time: Duration::from_secs_f64(o.time),
        seed: o.seed,
        delay: o.delay,
        cpus: cores.iter().map(|(c, _, _)| *c).collect(),
    };
    let model = match o.model {
        Model::Tso => "x86-TSO",
        Model::Sc => "SC (negative control)",
    };
    let mut md = String::new();
    let _ = writeln!(md, "## Run parameters\n");
    let _ = writeln!(md, "- CPU: {}", cpuinfo("model name"));
    let _ = writeln!(
        md,
        "- family/model/stepping: {}/{}/{}; microcode: {}",
        cpuinfo("cpu family"),
        cpuinfo("model"),
        cpuinfo("stepping"),
        cpuinfo("microcode")
    );
    let kernel = std::fs::read_to_string("/proc/sys/kernel/osrelease").unwrap_or_default();
    let _ = writeln!(md, "- kernel: {}", kernel.trim());
    let cs: Vec<String> = cores
        .iter()
        .take(need)
        .map(|(c, pk, co)| format!("cpu{c} (package {pk}, core {co})"))
        .collect();
    let _ = writeln!(md, "- litmus thread i runs on: {}", cs.join(", "));
    let _ = writeln!(
        md,
        "- mode: {}; seed {:#x}; iterations {}; time cap {} s per test; delay 0..={} loop iterations",
        if o.ci { "--ci" } else { "default" },
        o.seed,
        o.iters
            .map_or("unbounded (time-limited)".into(), |n| n.to_string()),
        o.time,
        o.delay
    );
    let _ = writeln!(md, "- TSO-covered tests checked against: {model}");
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let shown = std::fs::canonicalize(&o.json)
        .ok()
        .zip(std::fs::canonicalize(&repo).ok())
        .and_then(|(j, r)| j.strip_prefix(r).ok().map(Path::to_path_buf))
        .unwrap_or_else(|| o.json.clone());
    let _ = writeln!(md, "- export: `{}`", shown.display());
    for pv in &corpus.provenance {
        let _ = writeln!(md, "  - {pv}");
    }
    let _ = writeln!(
        md,
        "\n## Summary\n\n`weak` = observed outcomes that TSO allows and SC forbids / all such outcomes.\n`unseen` = TSO-allowed outcomes never observed.\n\n| test | cov | TSO | SC | XL | iterations | distinct | witness seen | weak | unseen | check |\n|---|---|---|---|---|---|---|---|---|---|---|"
    );
    let mut hists = String::new();
    let mut all_ok = true;
    let mut weak_seen = Vec::new();
    for (i, t) in &tests {
        let r = native::run(t, *i, &p, &data)?;
        let a = assess(t, o.model, &r.hist)?;
        // A time-capped fixed-iteration run is reported (`CAPPED`) but is not a failure.
        all_ok &= a.ok();
        let status = if !a.ok() {
            "FAIL"
        } else if r.capped {
            "CAPPED"
        } else {
            "ok"
        };
        println!(
            "{:24} {:3} iters={:8} distinct={:3} witness={:8} weak={}/{} {status}",
            t.name,
            if t.tso_covered { "tso" } else { "xl" },
            r.iterations,
            r.hist.len(),
            a.witness,
            a.weak.len(),
            a.weak_allowed
        );
        for (out, n) in &a.outside {
            println!("    OUTSIDE ALLOWED SET: {} x{n}", t.show(out));
        }
        if a.xl_violation {
            println!("    XL-FORBIDDEN WITNESS OBSERVED ({} times)", a.witness);
        }
        if !a.weak.is_empty() {
            weak_seen.push(t.name.clone());
        }
        let (weak, unseen) = if t.allowed.is_some() {
            (
                format!("{}/{}", a.weak.len(), a.weak_allowed),
                a.unseen_allowed.to_string(),
            )
        } else {
            ("-".into(), "-".into())
        };
        let _ = writeln!(
            md,
            "| {} | {} | {} | {} | {} | {} | {} | {} | {weak} | {unseen} | {status} |",
            t.name,
            if t.tso_covered { "tso" } else { "xl" },
            verdict_name(t.tso),
            verdict_name(t.sc),
            verdict_name(Some(t.xl)),
            r.iterations,
            r.hist.len(),
            a.witness
        );
        let _ = writeln!(
            hists,
            "\n### {}\n\n`{}`, {} iterations in {:.2} s\n",
            t.name,
            t.path,
            r.iterations,
            r.elapsed.as_secs_f64()
        );
        let mut rows: Vec<(&Outcome, &u64)> = r.hist.iter().collect();
        rows.sort_by(|x, y| y.1.cmp(x.1).then(x.0.cmp(y.0)));
        for (out, n) in rows {
            let mut tags = Vec::new();
            if t.witness_holds(out) == Some(true) {
                tags.push("witness");
            }
            if let Some(al) = &t.allowed {
                if !al.tso.contains(out) {
                    tags.push("NOT TSO-ALLOWED");
                } else if !al.sc.contains(out) {
                    tags.push("TSO-only");
                }
            }
            let tag = if tags.is_empty() {
                String::new()
            } else {
                format!(" [{}]", tags.join(", "))
            };
            let _ = writeln!(hists, "    {n:>9}  {}{tag}", t.show(out));
        }
    }
    let _ = writeln!(
        md,
        "\nTests with an observed TSO-only (SC-forbidden) outcome: {}.\n",
        if weak_seen.is_empty() {
            "none".into()
        } else {
            weak_seen.join(", ")
        }
    );
    let _ = writeln!(md, "## Histograms\n{hists}");
    println!(
        "{} tests; TSO-only outcomes observed in: {}",
        tests.len(),
        weak_seen.join(", ")
    );
    if let Some(path) = &o.report {
        std::fs::write(path, md).map_err(|e| format!("{}: {e}", path.display()))?;
        println!("wrote {}", path.display());
    }
    Ok(all_ok)
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => {
            eprintln!("litmus-run: some checks FAILED (see above)");
            ExitCode::FAILURE
        }
        Err(e) => {
            eprintln!("litmus-run: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn load() -> corpus::Corpus {
        let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../litmus-x86/export/corpus.json");
        corpus::parse(&std::fs::read_to_string(p).unwrap()).unwrap()
    }

    fn get<'a>(c: &'a corpus::Corpus, n: &str) -> &'a Test {
        c.tests.iter().find(|t| t.name == n).unwrap()
    }

    /// The allowed sets reproduce the recorded verdicts: a TSO (SC) witness verdict is
    /// `allowed` iff some outcome of the TSO (SC) set satisfies the witness; SC ⊆ TSO.
    #[test]
    fn allowed_sets_match_verdicts() {
        let c = load();
        assert_eq!(c.tests.len(), 68);
        for t in &c.tests {
            match &t.allowed {
                Some(a) => {
                    assert!(t.tso_covered, "{}", t.name);
                    assert_eq!(t.verdict_of(&a.tso), t.tso, "{}", t.name);
                    assert_eq!(t.verdict_of(&a.sc), t.sc, "{}", t.name);
                    assert_eq!(t.tso, Some(t.xl), "{}", t.name);
                    assert!(a.sc.is_subset(&a.tso), "{}", t.name);
                    assert!(!a.sc.is_empty(), "{}", t.name);
                }
                None => assert!(!t.tso_covered && t.tso.is_none(), "{}", t.name),
            }
        }
    }

    /// Cross-check against the Lean table: every test's verdicts and every instruction's
    /// bytes, in order, appear in its `def` block of `Corpus/Defs.lean`.
    #[test]
    fn export_matches_lean_table() {
        let c = load();
        let lean = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean"),
        )
        .unwrap();
        for t in &c.tests {
            let head = format!("def «{}» : Test where", t.name);
            let start = lean.find(&head).unwrap_or_else(|| panic!("{}", t.name));
            let block = &lean[start..];
            let block = &block[..block[1..].find("\ndef ").map_or(block.len(), |e| e + 1)];
            let lv = |v: Option<Verdict>| match v {
                Some(Verdict::Allowed) => "some .allowed",
                Some(Verdict::Forbidden) => "some .forbidden",
                None => "none",
            };
            assert!(
                block.contains(&format!("tso := {}\n", lv(t.tso))),
                "{}",
                t.name
            );
            assert!(
                block.contains(&format!("sc := {}\n", lv(t.sc))),
                "{}",
                t.name
            );
            let xl = lv(Some(t.xl)).trim_start_matches("some ");
            assert!(block.contains(&format!("xl := {xl}\n")), "{}", t.name);
            let mut pos = 0;
            for th in &t.threads {
                for (asm, bytes) in &th.code {
                    let bs: Vec<String> = bytes.iter().map(|b| format!("0x{b:02x}")).collect();
                    let needle = format!("⟨\"{asm}\", [{}]", bs.join(", "));
                    let at = block[pos..]
                        .find(&needle)
                        .unwrap_or_else(|| panic!("{}: {needle}", t.name));
                    pos += at + needle.len();
                }
            }
            for l in &t.locs {
                assert!(
                    block.contains(&format!(
                        "⟨\"{}\", 0x{:x}, {},",
                        l.name,
                        l.addr,
                        l.init.len()
                    )),
                    "{}: {}",
                    t.name,
                    l.name
                );
            }
        }
    }

    #[test]
    fn assess_flags_outside_and_xl_witness() {
        let c = load();
        let sb = get(&c, "SB");
        let al = sb.allowed.as_ref().unwrap();
        let weak = al.tso.difference(&al.sc).next().unwrap().clone();
        let mut h = BTreeMap::new();
        h.insert(weak.clone(), 3u64);
        let a = assess(sb, Model::Tso, &h).unwrap();
        assert!(a.ok());
        assert_eq!(a.witness, 3);
        assert_eq!(a.weak.len(), 1);
        let a = assess(sb, Model::Sc, &h).unwrap();
        assert!(!a.ok());
        // An outcome outside every set (x = 7).
        let mut bad = weak.clone();
        bad.mem[0] = vec![7, 0, 0, 0];
        h.insert(bad, 1);
        assert_eq!(assess(sb, Model::Tso, &h).unwrap().outside.len(), 1);
        // XL-only, XL-forbidden: observing the witness fails.
        let t = get(&c, "MP+movnti+sfence");
        assert_eq!(t.xl, Verdict::Forbidden);
        let w = Outcome {
            regs: vec![vec![], vec![1, 0]],
            mem: vec![vec![1, 0, 0, 0], vec![1, 0, 0, 0]],
        };
        assert_eq!(t.threads[1].observe, vec![0, 3]);
        assert_eq!(t.witness_holds(&w), Some(true));
        let mut h = BTreeMap::new();
        h.insert(w, 1u64);
        assert!(assess(t, Model::Tso, &h).unwrap().xl_violation);
    }

    /// A short hardware run on this machine (x86-64 Linux, at least 2 physical cores): SB and
    /// a locked RMW test produce only TSO-allowed outcomes, and every iteration is recorded.
    #[test]
    fn hardware_smoke() {
        let c = load();
        let cores = native::physical_cores();
        if cores.len() < 2 {
            eprintln!("skipping: fewer than 2 physical cores");
            return;
        }
        let data = native::Mapping::data().unwrap();
        let p = native::Params {
            iters: Some(5_000),
            time: Duration::from_secs(10),
            seed: CI_SEED,
            delay: DEFAULT_DELAY,
            cpus: cores.iter().map(|(c, _, _)| *c).collect(),
        };
        for (i, n) in ["SB", "RMW+lock-xadds", "SB+mfences"].iter().enumerate() {
            let t = get(&c, n);
            let r = native::run(t, i, &p, &data).unwrap();
            assert_eq!(r.iterations, 5_000);
            assert_eq!(r.hist.values().sum::<u64>(), 5_000);
            assert!(assess(t, Model::Tso, &r.hist).unwrap().ok(), "{n}");
        }
        // The compiled C11 tests (rip-relative code at its fixed `code_base`), in the same
        // test so that only one data mapping at 0x10000 exists at a time.
        let p11 = Path::new(env!("CARGO_MANIFEST_DIR")).join("../litmus-x86/export/c11.json");
        let c11 = corpus::parse(&std::fs::read_to_string(p11).unwrap()).unwrap();
        for (i, n) in ["SB+rlx@gcc", "SB+sc@clang", "Counter+rlx@clang"]
            .iter()
            .enumerate()
        {
            let t = get(&c11, n);
            assert!(t.threads.iter().all(|th| th.code_base.is_some()));
            let r = native::run(t, i, &p, &data).unwrap();
            assert_eq!(r.hist.values().sum::<u64>(), 5_000);
            assert!(assess(t, Model::Tso, &r.hist).unwrap().ok(), "{n}");
            // Every outcome has the stores of the code: the relocated accesses hit the page.
            for o in r.hist.keys() {
                assert!(o.mem.iter().any(|m| m.iter().any(|b| *b != 0)), "{n}");
            }
        }
    }
}
