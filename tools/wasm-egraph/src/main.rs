//! `wasm-egraph`: untrusted proof-producing equality saturation for straight-line integer
//! Wasm. It searches for a chain of verified rewrite rules (Lean's
//! `Silmaril.Wasm.Auto.Rules.library`) and prints a certificate that Lean's checker
//! (`Silmaril.Wasm.Auto.EGraph.checkEqL`, `checkRefL`) validates in the kernel. Nothing here
//! is trusted: a wrong certificate fails the Lean check.
//!
//! ```text
//! wasm-egraph rules
//! wasm-egraph prove [--locals i32,i64,..] [--refine] [--flat] LHS RHS
//! wasm-egraph optimize [--locals ..] [--flat] TERM
//! wasm-egraph bench CORPUS [--lean OUT.lean --module NAME] [--table OUT.md]
//! wasm-egraph emit-wasm CORPUS OUT.wasm        (the corpus inputs as one module)
//! wasm-egraph tv IN.wasm OUT.wasm [--names CORPUS] [--lean OUT.lean --module NAME] [--table OUT.md]
//! wasm-egraph tv-seg IN.wasm OUT.wasm [--func] [--lean OUT.lean --module NAME] [--table OUT.md]
//! wasm-egraph bench-seg CORPUS [--lean OUT.lean --module NAME] [--table OUT.md]
//! wasm-egraph gen-random-locals N SEED OUT.wasm
//! wasm-egraph emit-seg CORPUS A.wasm B.wasm   (the `(mode func)` cases of a seg corpus)
//! ```
//!
//! `tv-seg` and `bench-seg` handle code with `local.set`, `local.tee` and `drop` through effect
//! summaries (Lean's `Silmaril.Wasm.Auto.ESeg`): function bodies are proved equal up to their
//! locals (`BodyEquiv`), traps included, and, when both are typed and trap-free, also in the
//! every-run logic (`Silmaril.Wasm.Auto.Equiv.OutEquiv`). With locals (Lean's `Silmaril.Wasm.Auto.ESeg`):
//! `select` on `i32` operands, bodies whose declared locals differ (compared from function entry,
//! `FuncEquiv`; `--func` does so for every pair), and every-run theorems for typed bodies that
//! trap. Search limits count work, not time (`egraph::WORK`).
//!
//! `tv` (translation validation) pairs the functions of an optimizer's input and output
//! modules and proves each pair of straight-line bodies equivalent.
//!
//! Terms are WAT folded expressions, several for several results; with `--flat` a side
//! is a flat instruction list (`local.get 0; i32.const 1; i32.add`).

mod egraph;
mod rules;
mod seg;
mod sexp;
mod term;
mod wasm;

use egraph::{EGraph, Limits, Step, WORK, minimise, replay};
use sexp::Sexp;
use std::fmt::Write as _;
use std::process::ExitCode;
use std::time::Instant;
use term::{Term, Ty};

fn parse_locals(s: &str) -> Result<Vec<Ty>, String> {
    if s.is_empty() {
        return Ok(vec![]);
    }
    s.split(',')
        .map(|t| Ty::parse(t.trim()).ok_or_else(|| format!("bad type {t}")))
        .collect()
}

fn parse_side(src: &str, flat: bool) -> Result<Vec<Term>, String> {
    if flat {
        term::lift_flat(src)
    } else {
        sexp::parse_all(src)?.iter().map(Term::parse).collect()
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Eq,
    Ref,
}

struct Outcome {
    proved: bool,
    certs: Vec<Vec<Step>>,
    rhs: Vec<Term>,
    nodes: usize,
    iters: usize,
    millis: f64,
    note: String,
    /// Results proved only by the second (backoff) attempt.
    backoff: usize,
    /// Certificate steps before minimisation.
    raw_steps: usize,
}

fn limits() -> Limits {
    Limits {
        iters: 12,
        nodes: 30_000,
        work: WORK,
        backoff: None,
    }
}

/// The second attempt: backoff scheduling (so associativity and commutativity cannot fill
/// the graph in a few iterations) with more iterations.
fn limits_backoff() -> Limits {
    Limits {
        iters: 60,
        nodes: 30_000,
        work: WORK,
        backoff: Some(egraph::Backoff {
            match_limit: 100,
            ban_length: 2,
        }),
    }
}

/// Prove `lhs[i] = rhs[i]` (or refinement) for every position.
fn prove(locals: &[Ty], mode: Mode, lhs: &[Term], rhs: &[Term]) -> Outcome {
    let start = Instant::now();
    let lib = rules::library();
    let mut out = Outcome {
        proved: false,
        certs: vec![],
        rhs: rhs.to_vec(),
        nodes: 0,
        iters: 0,
        millis: 0.0,
        note: String::new(),
        backoff: 0,
        raw_steps: 0,
    };
    if lhs.len() != rhs.len() {
        out.note = format!("{} results against {}", lhs.len(), rhs.len());
        return out;
    }
    for (l, r) in lhs.iter().zip(rhs) {
        let mut found = None;
        for (k, lim) in [limits(), limits_backoff()].iter().enumerate() {
            let mut g = EGraph::new(locals.to_vec(), lib.clone(), mode == Mode::Ref);
            let a = g.add_term(l);
            let b = g.add_term(r);
            out.iters += g.run(lim, |g| g.find(a) == g.find(b));
            out.nodes += g.len();
            let mut budget = 200_000;
            if let Some(steps) = g.explain(a, b, &mut budget) {
                if k > 0 {
                    out.backoff += 1;
                }
                found = Some(steps);
                break;
            }
        }
        let Some(steps) = found else {
            out.note = format!(
                "no proof of {} = {} ({} nodes)",
                l.wat(),
                r.wat(),
                out.nodes
            );
            out.millis = start.elapsed().as_secs_f64() * 1e3;
            return out;
        };
        let raw = steps.len();
        let steps = minimise(locals, &lib, l, &steps);
        out.raw_steps += raw;
        match replay(locals, &lib, l, &steps) {
            Ok((t, all_eq)) if &t == r && (all_eq || mode == Mode::Ref) => out.certs.push(steps),
            Ok((t, _)) => {
                out.note = format!("explanation ends at {} or uses a refinement", t.wat());
                return out;
            }
            Err(e) => {
                out.note = format!("explanation does not replay: {e}");
                return out;
            }
        }
    }
    out.proved = true;
    out.millis = start.elapsed().as_secs_f64() * 1e3;
    out
}

/// Find the smallest equivalent term of each input and prove it.
fn optimize(locals: &[Ty], lhs: &[Term]) -> Outcome {
    let start = Instant::now();
    let lib = rules::library();
    let mut out = Outcome {
        proved: true,
        certs: vec![],
        rhs: vec![],
        nodes: 0,
        iters: 0,
        millis: 0.0,
        note: String::new(),
        backoff: 0,
        raw_steps: 0,
    };
    for l in lhs {
        let mut g = EGraph::new(locals.to_vec(), lib.clone(), false);
        let a = g.add_term(l);
        out.iters += g.run(&limits(), |_| false);
        let b = g.extract(a);
        out.nodes += g.len();
        let best = g.term(b);
        let mut budget = 200_000;
        match g
            .explain(a, b, &mut budget)
            .map(|s| minimise(locals, &lib, l, &s))
            .map(|s| (replay(locals, &lib, l, &s), s))
        {
            Some((Ok((t, true)), steps)) if t == best => {
                out.certs.push(steps);
                out.rhs.push(best);
            }
            _ => {
                out.proved = false;
                out.note = format!("no replayable explanation for {}", best.wat());
                out.rhs.push(l.clone());
                out.certs.push(vec![]);
            }
        }
    }
    out.millis = start.elapsed().as_secs_f64() * 1e3;
    out
}

fn lean_list<T>(xs: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", xs.iter().map(f).collect::<Vec<_>>().join(", "))
}

fn lean_locals(locals: &[Ty]) -> String {
    lean_list(locals, |t| t.lean().to_string())
}

/// A Lean theorem for a proved case.
fn lean_theorem(name: &str, locals: &[Ty], mode: Mode, lhs: &[Term], o: &Outcome) -> String {
    let certs = lean_list(&o.certs, |c| lean_list(c, Step::lean));
    let (rel, lemma) = match mode {
        Mode::Eq => ("SegEquiv", "segEquiv_of_checkEqL"),
        Mode::Ref => ("SegRefines", "segRefines_of_checkRefL"),
    };
    let mut s = String::new();
    let flat = |ts: &[Term]| {
        let mut v = vec![];
        ts.iter().for_each(|t| t.flat(&mut v));
        v.join("; ")
    };
    let _ = writeln!(s, "/-- `{}` ⟶ `{}` -/", flat(lhs), flat(&o.rhs));
    let _ = writeln!(
        s,
        "theorem {name} :\n    {rel} {}\n      (compileL {})\n      (compileL {}) :=",
        lean_locals(locals),
        lean_list(lhs, Term::lean),
        lean_list(&o.rhs, Term::lean)
    );
    let _ = writeln!(s, "  {lemma} {certs} library_sound (by decide +kernel)\n");
    s
}

fn cert_sexp(o: &Outcome) -> String {
    let mut s = String::from("(cert");
    for c in &o.certs {
        s.push_str("\n  (");
        s.push_str(
            &c.iter()
                .map(|st| format!("({})", st.lean()))
                .collect::<Vec<_>>()
                .join(" "),
        );
        s.push(')');
    }
    s.push(')');
    s
}

struct Args {
    pos: Vec<String>,
    locals: Vec<Ty>,
    refine: bool,
    flat: bool,
    lean: Option<String>,
    module: Option<String>,
    table: Option<String>,
    name: String,
    names: Option<String>,
    /// `tv-seg --func`: compare every pair from function entry (`checkFunc`, `FuncEquiv`), the
    /// form `wasm-check pass --egraph-tv-seg` lifts to module equivalence.
    func: bool,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut a = Args {
        pos: vec![],
        locals: vec![],
        refine: false,
        flat: false,
        lean: None,
        module: None,
        table: None,
        name: "egraph_case".into(),
        names: None,
        func: false,
    };
    let mut it = raw.iter();
    while let Some(x) = it.next() {
        let mut val = |what: &str| {
            it.next()
                .cloned()
                .ok_or_else(|| format!("{what} needs a value"))
        };
        match x.as_str() {
            "--locals" => a.locals = parse_locals(&val("--locals")?)?,
            "--refine" => a.refine = true,
            "--flat" => a.flat = true,
            "--lean" => a.lean = Some(val("--lean")?),
            "--module" => a.module = Some(val("--module")?),
            "--table" => a.table = Some(val("--table")?),
            "--name" => a.name = val("--name")?,
            "--names" => a.names = Some(val("--names")?),
            "--func" => a.func = true,
            _ => a.pos.push(x.clone()),
        }
    }
    Ok(a)
}

fn run() -> Result<bool, String> {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = raw.first() else {
        return Err("usage: wasm-egraph (rules | prove | optimize | bench) ...".into());
    };
    let a = parse_args(&raw[1..])?;
    match cmd.as_str() {
        "rules" => {
            for (i, r) in rules::library().iter().enumerate() {
                println!("{i} {}", r.text());
            }
            Ok(true)
        }
        "prove" => {
            let [l, r] = a.pos.as_slice() else {
                return Err("prove needs LHS RHS".into());
            };
            let (lhs, rhs) = (parse_side(l, a.flat)?, parse_side(r, a.flat)?);
            let mode = if a.refine { Mode::Ref } else { Mode::Eq };
            let o = prove(&a.locals, mode, &lhs, &rhs);
            report(&a, mode, &lhs, &o);
            Ok(o.proved)
        }
        "optimize" => {
            let [l] = a.pos.as_slice() else {
                return Err("optimize needs TERM".into());
            };
            let lhs = parse_side(l, a.flat)?;
            let o = optimize(&a.locals, &lhs);
            println!(
                "; optimized: {}",
                o.rhs.iter().map(Term::wat).collect::<Vec<_>>().join(" ")
            );
            report(&a, Mode::Eq, &lhs, &o);
            Ok(o.proved)
        }
        "bench" => {
            let [f] = a.pos.as_slice() else {
                return Err("bench needs CORPUS".into());
            };
            bench(f, &a)
        }
        "emit-wasm" => {
            let [f, out] = a.pos.as_slice() else {
                return Err("emit-wasm needs CORPUS OUT.wasm".into());
            };
            let cases = corpus_inputs(f)?;
            let funcs: Vec<_> = cases
                .iter()
                .map(|(_, l, ts)| {
                    let mut body = vec![];
                    ts.iter().for_each(|t| t.flat(&mut body));
                    (
                        l.clone(),
                        ts.iter().map(|t| t.type_of(l).unwrap_or(Ty::I32)).collect(),
                        body,
                    )
                })
                .collect();
            std::fs::write(out, wasm::write(&funcs)?).map_err(|e| format!("{out}: {e}"))?;
            eprintln!("{} functions", funcs.len());
            Ok(true)
        }
        "gen-random" => {
            let [n, seed, out] = a.pos.as_slice() else {
                return Err("gen-random needs N SEED OUT.wasm".into());
            };
            let n: usize = n.parse().map_err(|_| "bad N")?;
            let mut rng: u64 = seed.parse().map_err(|_| "bad SEED")?;
            let funcs: Vec<_> = (0..n).map(|_| random_func(&mut rng)).collect();
            std::fs::write(out, wasm::write(&funcs)?).map_err(|e| format!("{out}: {e}"))?;
            Ok(true)
        }
        "tv" => {
            let [i, o] = a.pos.as_slice() else {
                return Err("tv needs IN.wasm OUT.wasm".into());
            };
            tv(i, o, &a)
        }
        "tv-seg" => {
            let [i, o] = a.pos.as_slice() else {
                return Err("tv-seg needs IN.wasm OUT.wasm".into());
            };
            tv_seg(i, o, &a)
        }
        "bench-seg" => {
            let [f] = a.pos.as_slice() else {
                return Err("bench-seg needs CORPUS".into());
            };
            bench_seg(f, &a)
        }
        "emit-seg" => {
            // the `(mode func)` cases of a seg corpus as two modules (lhs, rhs), function `f<k>`
            // for the `k`-th such case
            let [f, out_a, out_b] = a.pos.as_slice() else {
                return Err("emit-seg needs CORPUS A.wasm B.wasm".into());
            };
            let src = std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?;
            let (mut fa, mut fb) = (vec![], vec![]);
            for c in sexp::parse_all(&src)? {
                let items = c.list().ok_or("a case is a list")?;
                if Sexp::field(items, "mode")
                    .and_then(|m| m.first().and_then(Sexp::atom).map(str::to_string))
                    .as_deref()
                    != Some("func")
                {
                    continue;
                }
                let tys = |k: &str| -> Result<Vec<Ty>, String> {
                    Sexp::field(items, k)
                        .unwrap_or_default()
                        .iter()
                        .map(|t| {
                            t.atom()
                                .and_then(Ty::parse)
                                .ok_or_else(|| "bad local type".to_string())
                        })
                        .collect()
                };
                let side = |k: &str| -> Result<Vec<String>, String> {
                    let f = Sexp::field(items, k).ok_or_else(|| format!("missing {k}"))?;
                    let text = f
                        .first()
                        .and_then(Sexp::string)
                        .ok_or("a side is a string")?;
                    Ok(text
                        .split(['\n', ';'])
                        .map(str::trim)
                        .filter(|l| !l.is_empty())
                        .map(str::to_string)
                        .collect())
                };
                let (ps, da, db) = (tys("locals")?, tys("alocals")?, tys("blocals")?);
                let (la, lb) = (side("lhs")?, side("rhs")?);
                let body_a: Vec<seg::Ins> = la
                    .iter()
                    .map(|l| seg::Ins::parse(l))
                    .collect::<Result<_, _>>()?;
                let sa = seg::lift_entry(&ps, &da, &body_a)?;
                let res: Vec<Ty> = sa
                    .stack
                    .iter()
                    .rev()
                    .map(|t| t.type_of(&ps).unwrap_or(Ty::I32))
                    .collect();
                fa.push((ps.clone(), res.clone(), da, la));
                fb.push((ps, res, db, lb));
            }
            std::fs::write(out_a, wasm::write_locals(&fa)?).map_err(|e| format!("{out_a}: {e}"))?;
            std::fs::write(out_b, wasm::write_locals(&fb)?).map_err(|e| format!("{out_b}: {e}"))?;
            Ok(true)
        }
        "gen-random-locals" => {
            let [n, seed, out] = a.pos.as_slice() else {
                return Err("gen-random-locals needs N SEED OUT.wasm".into());
            };
            let n: usize = n.parse().map_err(|_| "bad N")?;
            let mut rng: u64 = seed.parse().map_err(|_| "bad SEED")?;
            let funcs: Vec<_> = (0..n).map(|_| random_func_locals(&mut rng)).collect();
            std::fs::write(out, wasm::write_locals(&funcs)?).map_err(|e| format!("{out}: {e}"))?;
            Ok(true)
        }
        _ => Err(format!("unknown command {cmd}")),
    }
}

fn report(a: &Args, mode: Mode, lhs: &[Term], o: &Outcome) {
    if o.proved {
        println!(
            "; proved: {} e-nodes, {} iterations, {:.1} ms",
            o.nodes, o.iters, o.millis
        );
        println!("{}", cert_sexp(o));
        if a.lean.is_some() {
            print!("{}", lean_theorem(&a.name, &a.locals, mode, lhs, o));
        }
    } else {
        println!("; unknown: {}", o.note);
    }
}

/// Run a corpus: `(case NAME (locals ..) [(mode ref)] [(flat)] (lhs ..) (rhs ..) [(expect unknown)])`
/// or `(case NAME (locals ..) (optimize ..))`.
fn bench(path: &str, a: &Args) -> Result<bool, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let cases = sexp::parse_all(&src)?;
    let mut lean = String::new();
    let mut table = String::from(
        "| case | mode | result | expected | e-nodes | iterations | steps (before minimising) | search ms |\n|---|---|---|---|---|---|---|---|\n",
    );
    let mut all_ok = true;
    for c in &cases {
        let items = c.list().ok_or("a case is a list")?;
        let name = items.get(1).and_then(Sexp::atom).ok_or("case name")?;
        let locals: Vec<Ty> = Sexp::field(items, "locals")
            .unwrap_or_default()
            .iter()
            .map(|t| {
                t.atom()
                    .and_then(Ty::parse)
                    .ok_or_else(|| format!("{name}: bad local type"))
            })
            .collect::<Result<_, _>>()?;
        let flat = Sexp::field(items, "flat").is_some();
        let side = |key: &str| -> Result<Vec<Term>, String> {
            let f = Sexp::field(items, key).ok_or_else(|| format!("{name}: missing {key}"))?;
            if flat {
                term::lift_flat(
                    f.first()
                        .and_then(Sexp::string)
                        .ok_or("flat side is a string")?,
                )
            } else {
                f.iter().map(Term::parse).collect()
            }
        };
        let expect_unknown = Sexp::field(items, "expect")
            .is_some_and(|e| e.first().and_then(Sexp::atom) == Some("unknown"));
        let mode = if Sexp::field(items, "mode")
            .is_some_and(|m| m.first().and_then(Sexp::atom) == Some("ref"))
        {
            Mode::Ref
        } else {
            Mode::Eq
        };
        let (mode_s, lhs, o) = if Sexp::field(items, "optimize").is_some() {
            let lhs = side("optimize")?;
            let o = optimize(&locals, &lhs);
            ("optimize", lhs, o)
        } else {
            let (lhs, rhs) = (side("lhs")?, side("rhs")?);
            let o = prove(&locals, mode, &lhs, &rhs);
            (if mode == Mode::Ref { "refine" } else { "equiv" }, lhs, o)
        };
        let result = if o.proved { "proved" } else { "unknown" };
        let expected = if expect_unknown { "unknown" } else { "proved" };
        all_ok &= result == expected;
        let steps: usize = o.certs.iter().map(Vec::len).sum();
        let _ = writeln!(
            table,
            "| `{name}` | {mode_s} | {result} | {expected} | {} | {} | {steps} ({}) | {:.1} |",
            o.nodes, o.iters, o.raw_steps, o.millis
        );
        eprintln!(
            "{name}: {result} ({} nodes, {} steps, {:.1} ms){}",
            o.nodes,
            steps,
            o.millis,
            if o.note.is_empty() {
                String::new()
            } else {
                format!(" -- {}", o.note)
            }
        );
        if o.proved {
            lean.push_str(&lean_theorem(
                &name.replace('-', "_"),
                &locals,
                mode,
                &lhs,
                &o,
            ));
        }
    }
    if let Some(out) = &a.lean {
        let module = a.module.clone().unwrap_or_else(|| "Corpus".into());
        let header = format!(
            "module\n\npublic import Silmaril.Wasm.Auto.EGraph.Thms\npublic import Silmaril.Wasm.Auto.Rules.Thms\n\n/-! # {module}: e-graph certificates checked by the kernel\n\nGenerated by `tools/wasm-egraph` (`wasm-egraph bench {path}`); do not edit. Every\ntheorem is checked by `decide +kernel` on the certificate checker; the search that found\nthe certificates is not trusted.\n-/\n\n@[expose] public section\n\nnamespace Silmaril.Wasm.Auto.Corpus\n\nopen Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.Rules\n\n"
        );
        let text = format!("{header}{lean}end Silmaril.Wasm.Auto.Corpus\n");
        std::fs::write(out, text).map_err(|e| format!("{out}: {e}"))?;
    }
    if let Some(out) = &a.table {
        std::fs::write(out, &table).map_err(|e| format!("{out}: {e}"))?;
    } else {
        print!("{table}");
    }
    Ok(all_ok)
}

/// One equivalence case of a corpus: its name, the local types and the left-hand terms.
type CorpusCase = (String, Vec<Ty>, Vec<Term>);

/// The equivalence cases of a corpus whose left side is in the fragment and expected to
/// be proved: `(name, locals, lhs terms)`.
fn corpus_inputs(path: &str) -> Result<Vec<CorpusCase>, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let mut out = vec![];
    for c in sexp::parse_all(&src)? {
        let items = c.list().ok_or("a case is a list")?;
        let name = items
            .get(1)
            .and_then(Sexp::atom)
            .ok_or("case name")?
            .to_string();
        if Sexp::field(items, "mode").is_some()
            || Sexp::field(items, "optimize").is_some()
            || Sexp::field(items, "expect").is_some()
        {
            continue;
        }
        let locals: Vec<Ty> = Sexp::field(items, "locals")
            .unwrap_or_default()
            .iter()
            .filter_map(|t| t.atom().and_then(Ty::parse))
            .collect();
        let f = Sexp::field(items, "lhs").ok_or("lhs")?;
        let lhs = if Sexp::field(items, "flat").is_some() {
            term::lift_flat(f.first().and_then(Sexp::string).ok_or("flat side")?)?
        } else {
            f.iter().map(Term::parse).collect::<Result<_, _>>()?
        };
        out.push((name, locals, lhs));
    }
    Ok(out)
}

fn next(rng: &mut u64) -> u64 {
    *rng = rng
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *rng >> 33
}

fn random_term(rng: &mut u64, t: Ty, locals: &[Ty], depth: u32) -> Term {
    use term::{BinOp::*, Op, RelOp};
    let r = next(rng) % 100;
    if depth == 0 || r < 25 {
        let cands: Vec<u32> = (0..locals.len() as u32)
            .filter(|&i| locals[i as usize] == t)
            .collect();
        if !cands.is_empty() && !r.is_multiple_of(3) {
            return Term::leaf(Op::Lget(cands[(next(rng) as usize) % cands.len()]));
        }
        let ks = [0u64, 1, 2, 3, 7, 8, 31, 32, 255, t.mask(), t.mask() - 1];
        return Term::leaf(Op::Const(t, ks[(next(rng) as usize) % ks.len()]));
    }
    if t == Ty::I32 && r < 40 {
        // a test or comparison, possibly on i64 operands
        let ot = if next(rng).is_multiple_of(2) {
            Ty::I32
        } else {
            Ty::I64
        };
        if r < 30 {
            return Term {
                op: Op::Test(ot),
                ch: vec![random_term(rng, ot, locals, depth - 1)],
            };
        }
        let rels = [
            RelOp::Eq,
            RelOp::Ne,
            RelOp::LtS,
            RelOp::LtU,
            RelOp::GtU,
            RelOp::GeS,
        ];
        let op = rels[(next(rng) as usize) % rels.len()];
        return Term {
            op: Op::Rel(ot, op),
            ch: vec![
                random_term(rng, ot, locals, depth - 1),
                random_term(rng, ot, locals, depth - 1),
            ],
        };
    }
    let bins = [
        Add, Add, Sub, Mul, And, Or, Xor, Shl, ShrU, ShrS, DivU, RemU,
    ];
    let op = bins[(next(rng) as usize) % bins.len()];
    Term {
        op: Op::Bin(t, op),
        ch: vec![
            random_term(rng, t, locals, depth - 1),
            random_term(rng, t, locals, depth - 1),
        ],
    }
}

/// A random straight-line function: 1-3 parameters, one result.
fn random_func(rng: &mut u64) -> (Vec<Ty>, Vec<Ty>, Vec<String>) {
    let np = 1 + (next(rng) % 3) as usize;
    let params: Vec<Ty> = (0..np)
        .map(|_| {
            if next(rng).is_multiple_of(3) {
                Ty::I64
            } else {
                Ty::I32
            }
        })
        .collect();
    let rt = if next(rng).is_multiple_of(3) {
        Ty::I64
    } else {
        Ty::I32
    };
    let t = random_term(rng, rt, &params, 4);
    let mut body = vec![];
    t.flat(&mut body);
    (params, vec![rt], body)
}

/// Translation validation of an optimizer run.
fn tv(input: &str, output: &str, a: &Args) -> Result<bool, String> {
    let read = |p: &str| {
        std::fs::read(p)
            .map_err(|e| format!("{p}: {e}"))
            .and_then(|b| wasm::read(&b))
    };
    let (mi, mo) = (read(input)?, read(output)?);
    // Pair functions by export name (optimizers may merge or reorder functions).
    let mut pairs = vec![];
    for (name, i) in &mi.exports {
        let j = mo
            .exports
            .iter()
            .find(|(n, _)| n == name)
            .map(|e| e.1)
            .ok_or_else(|| format!("export {name} missing in output"))?;
        pairs.push((
            mi.funcs.get(*i).ok_or("bad export index")?,
            mo.funcs.get(j).ok_or("bad export index")?,
        ));
    }
    let names: Vec<String> = match &a.names {
        Some(c) => corpus_inputs(c)?.into_iter().map(|c| c.0).collect(),
        None => mi.exports.iter().map(|e| e.0.clone()).collect(),
    };
    let mut lean = String::new();
    let mut table = String::from(
        "| function | result | changed | e-nodes | steps | search ms | note |\n|---|---|---|---|---|---|---|\n",
    );
    let mut all = true;
    for (k, (x, y)) in pairs.into_iter().enumerate() {
        let name = names.get(k).cloned().unwrap_or_else(|| format!("f{k}"));
        let gx = x.frame();
        let gy = y.frame();
        let (res, changed, o, note) = match (x.terms(), y.terms()) {
            _ if x.results != y.results => {
                ("unknown", true, None, "result types differ".to_string())
            }
            (Ok(l), Ok(r)) if gy.len() <= gx.len() && gx[..gy.len()] == gy[..] => {
                let changed = l != r;
                let o = prove(&gx, Mode::Eq, &l, &r);
                if o.proved {
                    lean.push_str(&lean_theorem(&format!("tv_{name}"), &gx, Mode::Eq, &l, &o));
                }
                (
                    if o.proved { "proved" } else { "unknown" },
                    changed,
                    Some(o),
                    String::new(),
                )
            }
            (Ok(_), Ok(_)) => ("unknown", true, None, "output locals differ".to_string()),
            (Err(e), _) | (_, Err(e)) => ("unsupported", false, None, e),
        };
        all &= res == "proved";
        let (nodes, steps, ms) = o.as_ref().map_or((0, 0, 0.0), |o| {
            (o.nodes, o.certs.iter().map(Vec::len).sum(), o.millis)
        });
        let note = if note.is_empty() {
            o.map(|o| o.note).unwrap_or_default()
        } else {
            note
        };
        table.push_str(&format!(
            "| `{name}` | {res} | {} | {nodes} | {steps} | {ms:.1} | {note} |\n",
            if changed { "yes" } else { "no" }
        ));
    }
    if let Some(out) = &a.lean {
        let module = a.module.clone().unwrap_or_else(|| "OptTV".into());
        let header = format!(
            "module\n\npublic import Silmaril.Wasm.Auto.EGraph.Thms\npublic import Silmaril.Wasm.Auto.Rules.Thms\n\n/-! # {module}: translation validation of an optimizer run\n\nGenerated by `tools/wasm-egraph` (`wasm-egraph tv`); do not edit. For each function of the\ninput module, the body before and after the optimizer, lifted to terms, with an e-graph\ncertificate checked by `decide +kernel`. The frame types are the input function's\nparameters and declared locals.\n-/\n\n@[expose] public section\n\nnamespace Silmaril.Wasm.Auto.{module}\n\nopen Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.Rules\n\n"
        );
        let text = format!("{header}{lean}end Silmaril.Wasm.Auto.{module}\n");
        std::fs::write(out, text).map_err(|e| format!("{out}: {e}"))?;
    }
    match &a.table {
        Some(out) => std::fs::write(out, &table).map_err(|e| format!("{out}: {e}"))?,
        None => print!("{table}"),
    }
    Ok(all)
}

/// A random straight-line function with locals: 1-3 parameters, 1-3 declared locals, a few
/// `local.set`/`local.tee`/`drop` statements over parameters and already-set locals, then one
/// result. Declared locals are read only after they are set (the Lean statement quantifies
/// over every typed frame, not only zero-initialised ones).
fn random_func_locals(rng: &mut u64) -> (Vec<Ty>, Vec<Ty>, Vec<Ty>, Vec<String>) {
    let ty = |rng: &mut u64| {
        if next(rng).is_multiple_of(3) {
            Ty::I64
        } else {
            Ty::I32
        }
    };
    let np = 1 + (next(rng) % 3) as usize;
    let params: Vec<Ty> = (0..np).map(|_| ty(rng)).collect();
    let nl = 1 + (next(rng) % 3) as usize;
    let mut locals: Vec<Ty> = (0..nl).map(|_| ty(rng)).collect();
    // grouped by type, as Binaryen's binary writer groups them (so the output's local
    // indices are the input's unless a pass renumbers them)
    locals.sort();
    let mut frame = params.clone();
    frame.extend(&locals);
    let mut visible: Vec<u32> = (0..np as u32).collect();
    let mut body = vec![];
    let stmts = 2 + (next(rng) % 4) as usize;
    for _ in 0..stmts {
        let k = np + (next(rng) % nl as u64) as usize;
        let e = random_term_vis(rng, frame[k], &frame, &visible, 3);
        e.flat(&mut body);
        let sets = match next(rng) % 5 {
            0 => {
                body.push(format!("local.tee {k}"));
                body.push("drop".into());
                true
            }
            1 => {
                body.push("drop".into());
                false
            }
            _ => {
                body.push(format!("local.set {k}"));
                true
            }
        };
        if sets && !visible.contains(&(k as u32)) {
            visible.push(k as u32);
        }
    }
    let rt = ty(rng);
    random_term_vis(rng, rt, &frame, &visible, 3).flat(&mut body);
    (params, vec![rt], locals, body)
}

/// `random_term` reading only the locals in `visible`.
fn random_term_vis(rng: &mut u64, t: Ty, locals: &[Ty], visible: &[u32], depth: u32) -> Term {
    loop {
        let e = random_term(rng, t, locals, depth);
        let mut flat = vec![];
        e.flat(&mut flat);
        if flat.iter().all(|l| {
            l.strip_prefix("local.get ")
                .is_none_or(|i| visible.contains(&i.parse().unwrap_or(u32::MAX)))
        }) {
            return e;
        }
    }
}

fn seg_limits() -> Vec<Limits> {
    vec![limits(), limits_backoff()]
}

/// The Lean module header of a segment module.
fn seg_header(module: &str, what: &str) -> String {
    format!(
        "module\n\npublic import Silmaril.Wasm.Auto.ESeg.Thms\npublic import Silmaril.Wasm.Auto.Rules.Thms\n\n/-! # {module}: e-graph certificates for code with locals, checked by the kernel\n\nGenerated by `tools/wasm-egraph` ({what});\ndo not edit. Each `BodyEquiv` theorem relates the two instruction lists themselves (equal\nresults, stores, modules and traps; locals may differ), checked by `decide +kernel` on\n`checkBody` (`SegEquiv` and `checkSeg` for segment cases: the locals are equal too;\n`BodyEquivSel`/`checkBodySel` for bodies with `select`; `FuncEquiv`/`checkFunc` for bodies whose\ndeclared locals differ, compared from function entry); each `_everyRun` theorem restates it in\nthe every-run logic (`Silmaril.Wasm.Auto.Equiv.OutEquiv` or `SegEquiv`, or\n`Silmaril.Wasm.Auto.ESeg.FuncOutEquiv`) for typed bodies, traps included (segments: typed\nand trap-free). The search that found the certificates is not trusted.\n-/\n\n@[expose] public section\n\nnamespace Silmaril.Wasm.Auto.{module}\n\nopen Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.Rules Silmaril.Wasm.Auto.ESeg\n\n"
    )
}

/// How a pair of bodies is compared.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PairMode {
    /// `checkSeg`: segments, equal locals too.
    Seg,
    /// `checkBody` (`checkBodySel` with `select`): one frame types both bodies.
    Body,
    /// `checkFunc`: same parameters, different declared locals, from function entry.
    Func,
}

/// The Lean text of one proved pair. `frame`: the frame types (`Body`, `Seg`) or the
/// parameters (`Func`, with the declared locals `da`, `db`). `every`: restate it in the
/// every-run logic (`pure`: typed and trap-free, the pass-2 bridges; else typed, traps
/// included, the pass-3 bridges).
#[allow(clippy::too_many_arguments)]
fn seg_lean(
    name: &str,
    frame: &[Ty],
    da: &[Ty],
    db: &[Ty],
    a: &[seg::Ins],
    b: &[seg::Ins],
    cert: &seg::SegCert,
    mode: PairMode,
    every: Option<bool>,
) -> String {
    let mut s = String::new();
    let fr = lean_locals(frame);
    let _ = writeln!(
        s,
        "/-- The first body of `{name}`. -/\ndef {name}_a : List Instr := {}\n",
        seg::lean_instrs(a)
    );
    let _ = writeln!(
        s,
        "/-- The second body of `{name}`. -/\ndef {name}_b : List Instr := {}\n",
        seg::lean_instrs(b)
    );
    let has_sel = a.iter().chain(b).any(|i| *i == seg::Ins::Select);
    let (rel, lemma) = match (mode, has_sel) {
        (PairMode::Seg, false) => (format!("SegEquiv {fr}"), "segEquiv_of_checkSeg"),
        (PairMode::Seg, true) => (
            format!("Silmaril.Wasm.Auto.ESeg.SegEquivSel {fr}"),
            "Silmaril.Wasm.Auto.ESeg.segEquivSel_of_checkSegSel",
        ),
        (PairMode::Body, false) => (format!("BodyEquiv {fr}"), "bodyEquiv_of_checkBody"),
        (PairMode::Body, true) => (
            format!("Silmaril.Wasm.Auto.ESeg.BodyEquivSel {fr}"),
            "Silmaril.Wasm.Auto.ESeg.bodyEquivSel_of_checkBodySel",
        ),
        (PairMode::Func, _) => (
            format!(
                "Silmaril.Wasm.Auto.ESeg.FuncEquiv {fr} {} {}",
                lean_locals(da),
                lean_locals(db)
            ),
            "Silmaril.Wasm.Auto.ESeg.funcEquiv_of_checkFunc",
        ),
    };
    let _ = writeln!(
        s,
        "theorem {name} : {rel} {name}_a {name}_b :=\n  {lemma}\n    {}\n    library_sound (by decide +kernel)\n",
        cert.lean(mode == PairMode::Seg)
    );
    match (every, mode, has_sel) {
        (Some(true), PairMode::Seg, false) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun : Silmaril.Wasm.Auto.Equiv.SegEquiv {fr} [] {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.equivSeg_of_segEquiv {name} (by decide +kernel)\n"
            );
        }
        (Some(true), PairMode::Seg, true) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun : Silmaril.Wasm.Auto.Equiv.SegEquiv {fr} [] {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.equivSeg_of_segEquivSel {name} (by decide +kernel)\n"
            );
        }
        (Some(true), PairMode::Body, false) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun : Silmaril.Wasm.Auto.Equiv.OutEquiv {fr} [] {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.outEquiv_of_bodyEquiv {name} (by decide +kernel) (by decide +kernel)\n"
            );
        }
        (Some(false), PairMode::Body, false) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun : Silmaril.Wasm.Auto.Equiv.OutEquiv {fr} [] {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.outEquiv_of_bodyEquiv_typed {name} (by decide +kernel)\n    (by decide +kernel)\n"
            );
        }
        (Some(_), PairMode::Body, true) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun : Silmaril.Wasm.Auto.Equiv.OutEquiv {fr} [] {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.outEquivSel_of_bodyEquivSel {name} (by decide +kernel)\n    (by decide +kernel)\n"
            );
        }
        (Some(_), PairMode::Func, _) => {
            let _ = writeln!(
                s,
                "theorem {name}_everyRun :\n    Silmaril.Wasm.Auto.ESeg.FuncOutEquiv {fr} {} {} {name}_a {name}_b :=\n  Silmaril.Wasm.Auto.ESeg.funcOutEquiv_of_funcEquiv {name} (by decide +kernel)\n    (by decide +kernel)\n",
                lean_locals(da),
                lean_locals(db)
            );
        }
        _ => {}
    }
    s
}

/// Typed and trap-free (Lean's `pureOk`).
fn pure(frame: &[Ty], s: &seg::Sym) -> bool {
    s.terms()
        .iter()
        .all(|e| seg::no_trap(e) && e.type_of(frame).is_some())
}

struct SegRow {
    name: String,
    result: &'static str,
    changed: bool,
    nodes: usize,
    steps: usize,
    millis: f64,
    every_run: bool,
    note: String,
}

fn seg_table(rows: &[SegRow]) -> String {
    let mut t = String::from(
        "| function | result | changed | every-run | e-nodes | steps | search ms | note |\n|---|---|---|---|---|---|---|---|\n",
    );
    for r in rows {
        t.push_str(&format!(
            "| `{}` | {} | {} | {} | {} | {} | {:.1} | {} |\n",
            r.name,
            r.result,
            if r.changed { "yes" } else { "no" },
            if r.every_run { "yes" } else { "" },
            r.nodes,
            r.steps,
            r.millis,
            r.note
        ));
    }
    t
}

/// Prove one pair of bodies; returns the row and the Lean text. `frame`: the frame types, or
/// the parameters in `Func` mode (with the declared locals `da`, `db`).
#[allow(clippy::too_many_arguments)]
fn seg_pair(
    name: &str,
    frame: &[Ty],
    da: &[Ty],
    db: &[Ty],
    a: &[seg::Ins],
    b: &[seg::Ins],
    mode: PairMode,
) -> (SegRow, String) {
    let start = Instant::now();
    let lib = rules::library();
    let mut row = SegRow {
        name: name.to_string(),
        result: "unknown",
        changed: a != b,
        nodes: 0,
        steps: 0,
        millis: 0.0,
        every_run: false,
        note: String::new(),
    };
    let full = |d: &[Ty]| -> Vec<Ty> { frame.iter().chain(d).copied().collect() };
    let lifted = if mode == PairMode::Func {
        (seg::lift_entry(frame, da, a), seg::lift_entry(frame, db, b))
    } else {
        (seg::lift(frame, a), seg::lift(frame, b))
    };
    let (sa, sb) = match lifted {
        (Ok(x), Ok(y)) => (x, y),
        (Err(e), _) | (_, Err(e)) => {
            row.result = "unsupported";
            row.note = e;
            return (row, String::new());
        }
    };
    if mode == PairMode::Func
        && !sa
            .terms()
            .iter()
            .chain(sb.terms().iter())
            .all(|e| seg::reads_below(frame.len(), e))
    {
        row.note = "a body reads a declared local before setting it".into();
        return (row, String::new());
    }
    let mut p = seg::Prover {
        locals: frame,
        rules: &lib,
        lim: seg_limits(),
        nodes: 0,
    };
    let res = seg::prove(&mut p, &sa, &sb, mode == PairMode::Seg);
    row.nodes = p.nodes;
    row.millis = start.elapsed().as_secs_f64() * 1e3;
    match res {
        Ok(cert) => {
            row.result = "proved";
            row.steps = cert.steps();
            // every-run: typed and trap-free, or typed with traps (bodies)
            let is_pure = pure(frame, &sa) && (mode == PairMode::Seg || pure(frame, &sb));
            let every = match mode {
                PairMode::Seg => {
                    let has_sel = a.contains(&seg::Ins::Select);
                    if is_pure && (!has_sel || seg::typed(frame, a)) {
                        Some(true)
                    } else {
                        None
                    }
                }
                PairMode::Body => {
                    let has_sel = a.iter().chain(b).any(|i| *i == seg::Ins::Select);
                    if is_pure && !has_sel {
                        Some(true)
                    } else if seg::typed(frame, a) && seg::typed(frame, b) {
                        Some(false)
                    } else {
                        None
                    }
                }
                PairMode::Func => {
                    (seg::typed(&full(da), a) && seg::typed(&full(db), b)).then_some(false)
                }
            };
            row.every_run = every.is_some();
            let text = seg_lean(name, frame, da, db, a, b, &cert, mode, every);
            (row, text)
        }
        Err(e) => {
            row.note = e;
            (row, String::new())
        }
    }
}

/// Translation validation of an optimizer run, for bodies with locals.
fn tv_seg(input: &str, output: &str, a: &Args) -> Result<bool, String> {
    let read = |p: &str| {
        std::fs::read(p)
            .map_err(|e| format!("{p}: {e}"))
            .and_then(|b| wasm::read(&b))
    };
    let (mi, mo) = (read(input)?, read(output)?);
    let mut lean = String::new();
    let mut rows = vec![];
    for (name, i) in &mi.exports {
        let j = mo
            .exports
            .iter()
            .find(|(n, _)| n == name)
            .map(|e| e.1)
            .ok_or_else(|| format!("export {name} missing in output"))?;
        let (x, y) = (
            mi.funcs.get(*i).ok_or("bad export index")?,
            mo.funcs.get(j).ok_or("bad export index")?,
        );
        let (gx, gy) = (x.frame(), y.frame());
        // one frame typing both bodies: the longer one, when the other is a prefix of it;
        // else (renumbered declared locals) compare from function entry
        let (frame, mode) = if a.func && x.params == y.params {
            (x.params.clone(), PairMode::Func)
        } else if gy.len() <= gx.len() && gx[..gy.len()] == gy[..] {
            (gx, PairMode::Body)
        } else if gx.len() <= gy.len() && gy[..gx.len()] == gx[..] {
            (gy, PairMode::Body)
        } else if x.params == y.params {
            (x.params.clone(), PairMode::Func)
        } else {
            rows.push(SegRow {
                name: name.clone(),
                result: "unknown",
                changed: true,
                nodes: 0,
                steps: 0,
                millis: 0.0,
                every_run: false,
                note: "parameters differ".into(),
            });
            continue;
        };
        let body = |f: &wasm::Func| f.body.clone().and_then(|b| seg::parse_body(&b));
        match (body(x), body(y)) {
            _ if x.results != y.results => rows.push(SegRow {
                name: name.clone(),
                result: "unknown",
                changed: true,
                nodes: 0,
                steps: 0,
                millis: 0.0,
                every_run: false,
                note: "result types differ".into(),
            }),
            (Ok(ba), Ok(bb)) => {
                let (mut row, text) = seg_pair(
                    &format!("tv_{name}"),
                    &frame,
                    &x.locals,
                    &y.locals,
                    &ba,
                    &bb,
                    mode,
                );
                row.name = name.clone();
                eprintln!(
                    "{name}: {} ({} nodes, {} steps, {:.1} ms){}",
                    row.result,
                    row.nodes,
                    row.steps,
                    row.millis,
                    if row.note.is_empty() {
                        String::new()
                    } else {
                        format!(" -- {}", row.note)
                    }
                );
                lean.push_str(&text);
                rows.push(row);
            }
            (Err(e), _) | (_, Err(e)) => rows.push(SegRow {
                name: name.clone(),
                result: "unsupported",
                changed: true,
                nodes: 0,
                steps: 0,
                millis: 0.0,
                every_run: false,
                note: e,
            }),
        }
    }
    if let Some(out) = &a.lean {
        let module = a.module.clone().unwrap_or_else(|| "SegTV".into());
        let text = format!(
            "{}{lean}end Silmaril.Wasm.Auto.{module}\n",
            seg_header(&module, "`wasm-egraph tv-seg`")
        );
        std::fs::write(out, text).map_err(|e| format!("{out}: {e}"))?;
    }
    let table = seg_table(&rows);
    match &a.table {
        Some(out) => std::fs::write(out, &table).map_err(|e| format!("{out}: {e}"))?,
        None => print!("{table}"),
    }
    Ok(rows.iter().all(|r| r.result == "proved"))
}

/// A corpus of flat segments with locals:
/// `(case NAME (locals ..) [(mode seg)] (lhs "flat") (rhs "flat") [(expect unknown)])`.
fn bench_seg(path: &str, a: &Args) -> Result<bool, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let mut lean = String::new();
    let mut rows = vec![];
    let mut all_ok = true;
    for c in sexp::parse_all(&src)? {
        let items = c.list().ok_or("a case is a list")?;
        let name = items
            .get(1)
            .and_then(Sexp::atom)
            .ok_or("case name")?
            .replace('-', "_");
        let frame: Vec<Ty> = Sexp::field(items, "locals")
            .unwrap_or_default()
            .iter()
            .map(|t| t.atom().and_then(Ty::parse).ok_or("bad local type"))
            .collect::<Result<_, _>>()?;
        let side = |k: &str| -> Result<Vec<seg::Ins>, String> {
            let f = Sexp::field(items, k).ok_or_else(|| format!("{name}: missing {k}"))?;
            let text = f
                .first()
                .and_then(Sexp::string)
                .ok_or("a side is a string")?;
            text.split(['\n', ';'])
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .map(seg::Ins::parse)
                .collect()
        };
        let mode_field = Sexp::field(items, "mode");
        let mode = match mode_field
            .as_ref()
            .and_then(|m| m.first().and_then(Sexp::atom))
        {
            Some("seg") => PairMode::Seg,
            Some("func") => PairMode::Func,
            _ => PairMode::Body,
        };
        // `func` mode: `(locals ..)` are the parameters, `(alocals ..)` and `(blocals ..)` the
        // declared locals of each side
        let tys = |k: &str| -> Result<Vec<Ty>, String> {
            Sexp::field(items, k)
                .unwrap_or_default()
                .iter()
                .map(|t| {
                    t.atom()
                        .and_then(Ty::parse)
                        .ok_or_else(|| "bad local type".to_string())
                })
                .collect()
        };
        let (da, db) = (tys("alocals")?, tys("blocals")?);
        let expect_unknown = Sexp::field(items, "expect")
            .is_some_and(|e| e.first().and_then(Sexp::atom) == Some("unknown"));
        let (row, text) = seg_pair(&name, &frame, &da, &db, &side("lhs")?, &side("rhs")?, mode);
        eprintln!(
            "{name}: {} ({} nodes, {} steps, {:.1} ms){}",
            row.result,
            row.nodes,
            row.steps,
            row.millis,
            if row.note.is_empty() {
                String::new()
            } else {
                format!(" -- {}", row.note)
            }
        );
        all_ok &= (row.result == "proved") != expect_unknown;
        lean.push_str(&text);
        rows.push(row);
    }
    if let Some(out) = &a.lean {
        let module = a.module.clone().unwrap_or_else(|| "SegCorpus".into());
        let text = format!(
            "{}{lean}end Silmaril.Wasm.Auto.{module}\n",
            seg_header(&module, &format!("`wasm-egraph bench-seg {path}`"))
        );
        std::fs::write(out, text).map_err(|e| format!("{out}: {e}"))?;
    }
    let table = seg_table(&rows);
    match &a.table {
        Some(out) => std::fs::write(out, &table).map_err(|e| format!("{out}: {e}"))?,
        None => print!("{table}"),
    }
    Ok(all_ok)
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("wasm-egraph: {e}");
            ExitCode::from(2)
        }
    }
}
