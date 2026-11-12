//! Effect summaries of straight-line code with locals, mirroring Lean's
//! `Silmaril.Wasm.Auto.ESeg` (`Sym`, `lstep`, `lift`), and certificates for its checkers
//! `checkBody` (function bodies, equal up to the locals) and `checkSeg` (segments).
//!
//! A summary is the operand stack, the current term of every local and the guards (terms
//! computed and discarded, whose traps are kept), all over the initial frame. The certificate
//! has an e-graph chain per stack slot (and per local, for segments) and a cover per term of
//! each side: `total` for a typed term without division, else a chain to a subterm of a term
//! of the other side. Untrusted: Lean recomputes the summaries and checks everything.
//!
//! With locals (Lean's `Silmaril.Wasm.Auto.ESeg`): `select` on `i32` operands is the term
//! `selTerm a b c = b ^ ((a ^ b) & (0 - (c != 0)))` (`lstep` takes the frame types for the type
//! check), and `lift_entry` lifts a body from function entry (parameters, then zero declared
//! locals) for `checkFunc`.

use crate::egraph::{EGraph, Limits, SHORT_WORK, Step, invert, minimise, replay};
use crate::rules::Rule;
use crate::term::{BinOp, Op, OpName, Term, Ty};

/// Lean's `Sym`: `stack` top first, `guards` newest first, as Lean's lists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sym {
    pub stack: Vec<Term>,
    pub locs: Vec<Term>,
    pub guards: Vec<Term>,
}

impl Sym {
    pub fn init(n: usize) -> Sym {
        Sym {
            stack: vec![],
            locs: (0..n as u32).map(|i| Term::leaf(Op::Lget(i))).collect(),
            guards: vec![],
        }
    }

    /// Lean's `Sym.terms`: guards, locals, stack.
    pub fn terms(&self) -> Vec<Term> {
        let mut v = self.guards.clone();
        v.extend(self.locs.iter().cloned());
        v.extend(self.stack.iter().cloned());
        v
    }
}

/// A flat instruction of the fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ins {
    Nop,
    Drop,
    Const(Ty, u64),
    Get(u32),
    Set(u32),
    Tee(u32),
    Select,
    Op(Op),
}

impl Ins {
    pub fn parse(line: &str) -> Result<Ins, String> {
        let mut w = line.split_whitespace();
        let name = w.next().unwrap_or("");
        let arg = w.next();
        let idx = || -> Result<u32, String> {
            arg.ok_or("index")?
                .parse()
                .map_err(|_| format!("bad index in `{line}`"))
        };
        Ok(match name {
            "nop" => Ins::Nop,
            "drop" => Ins::Drop,
            "local.set" => Ins::Set(idx()?),
            "local.tee" => Ins::Tee(idx()?),
            "select" => Ins::Select,
            _ => match Op::parse_name(name)
                .ok_or_else(|| format!("unsupported instruction `{line}`"))?
            {
                OpName::Lget => Ins::Get(idx()?),
                OpName::Const(t) => Ins::Const(
                    t,
                    crate::term::parse_const(t, arg.ok_or("const needs a value")?)?,
                ),
                OpName::Op(op) => Ins::Op(op),
            },
        })
    }

    /// The Lean `Instr`.
    pub fn lean(&self) -> String {
        match self {
            Ins::Nop => ".nop".into(),
            Ins::Drop => ".drop".into(),
            Ins::Const(t, n) => format!(".intConst {} {n}", t.lean()),
            Ins::Get(i) => format!(".localGet (lidx {i})"),
            Ins::Set(i) => format!(".localSet (lidx {i})"),
            Ins::Tee(i) => format!(".localTee (lidx {i})"),
            Ins::Select => ".select none".into(),
            Ins::Op(op) => {
                let h = op.lean_head();
                match op {
                    Op::Un(..) => h.replacen(".un ", ".intUnOp ", 1),
                    Op::Test(t) => format!(".intTestOp {} .eqz", t.lean()),
                    Op::Bin(..) => h.replacen(".bin ", ".intBinOp ", 1),
                    Op::Rel(..) => h.replacen(".rel ", ".intRelOp ", 1),
                    _ => unreachable!("leaves are not operators"),
                }
            }
        }
    }
}

pub fn parse_body(body: &[String]) -> Result<Vec<Ins>, String> {
    body.iter().map(|l| Ins::parse(l)).collect()
}

/// Lean's `ESeg.selTerm a b c`.
pub fn sel_term(a: Term, b: Term, c: Term) -> Term {
    let bin = |op: BinOp, x: Term, y: Term| Term {
        op: Op::Bin(Ty::I32, op),
        ch: vec![x, y],
    };
    let zero = || Term::leaf(Op::Const(Ty::I32, 0));
    let ne = Term {
        op: Op::Rel(Ty::I32, crate::term::RelOp::Ne),
        ch: vec![c, zero()],
    };
    bin(
        BinOp::Xor,
        b.clone(),
        bin(
            BinOp::And,
            bin(BinOp::Xor, a, b),
            bin(BinOp::Sub, zero(), ne),
        ),
    )
}

/// Lean's `ESeg.lstepSel` (`lstep` with `select`, its operands typed `i32` by `frame`).
fn lstep(frame: &[Ty], s: &mut Sym, i: &Ins) -> Result<(), String> {
    let pop = |s: &mut Sym| -> Result<Term, String> {
        if s.stack.is_empty() {
            return Err("stack underflow".into());
        }
        Ok(s.stack.remove(0))
    };
    match i {
        Ins::Nop => {}
        Ins::Drop => {
            let e = pop(s)?;
            s.guards.insert(0, e);
        }
        Ins::Const(t, n) => s.stack.insert(0, Term::leaf(Op::Const(*t, *n))),
        Ins::Get(x) => {
            let e = s
                .locs
                .get(*x as usize)
                .ok_or("local index out of range")?
                .clone();
            s.stack.insert(0, e);
        }
        Ins::Set(x) | Ins::Tee(x) => {
            let x = *x as usize;
            if x >= s.locs.len() || s.stack.is_empty() {
                return Err("bad local.set".into());
            }
            let e = s.stack[0].clone();
            if matches!(i, Ins::Set(_)) {
                s.stack.remove(0);
            }
            let old = std::mem::replace(&mut s.locs[x], e);
            s.guards.insert(0, old);
        }
        Ins::Select => {
            if s.stack.len() < 3 {
                return Err("stack underflow".into());
            }
            let (c, b, a) = (s.stack[0].clone(), s.stack[1].clone(), s.stack[2].clone());
            if [&a, &b, &c]
                .iter()
                .any(|e| e.type_of(frame) != Some(Ty::I32))
            {
                return Err("select of non-i32 operands".into());
            }
            s.stack.drain(0..3);
            s.stack.insert(0, sel_term(a, b, c));
        }
        Ins::Op(op) => {
            let k = op.arity();
            if s.stack.len() < k {
                return Err("stack underflow".into());
            }
            // the stack is top first: `b` (top) then `a`
            let mut ch: Vec<Term> = s.stack.drain(0..k).collect();
            ch.reverse();
            s.stack.insert(0, Term { op: op.clone(), ch });
        }
    }
    Ok(())
}

/// Lean's `lift n is` (`liftSel frame is` when `is` has a `select`).
pub fn lift(frame: &[Ty], is: &[Ins]) -> Result<Sym, String> {
    let mut s = Sym::init(frame.len());
    for i in is {
        lstep(frame, &mut s, i)?;
    }
    Ok(s)
}

/// Lean's `liftEntrySel params decl is`: from function entry, parameters then zero locals.
pub fn lift_entry(params: &[Ty], decl: &[Ty], is: &[Ins]) -> Result<Sym, String> {
    let mut frame = params.to_vec();
    frame.extend_from_slice(decl);
    let mut s = Sym::init(params.len());
    s.locs
        .extend(decl.iter().map(|t| Term::leaf(Op::Const(*t, 0))));
    for i in is {
        lstep(&frame, &mut s, i)?;
    }
    Ok(s)
}

/// Lean's `ESeg.readsBelow n`.
pub fn reads_below(n: usize, e: &Term) -> bool {
    match e.op {
        Op::Lget(i) => (i as usize) < n,
        _ => e.ch.iter().all(|c| reads_below(n, c)),
    }
}

/// Lean's `XExec.tsteps frame [] is` succeeds (the validator of typed straight-line code).
pub fn typed(frame: &[Ty], is: &[Ins]) -> bool {
    let mut st: Vec<Ty> = vec![]; // top last
    for i in is {
        let ok = match i {
            Ins::Nop => true,
            Ins::Drop => st.pop().is_some(),
            Ins::Const(t, _) => {
                st.push(*t);
                true
            }
            Ins::Get(x) => match frame.get(*x as usize) {
                Some(t) => {
                    st.push(*t);
                    true
                }
                None => false,
            },
            Ins::Set(x) | Ins::Tee(x) => match (st.last().copied(), frame.get(*x as usize)) {
                (Some(t), Some(u)) if t == *u => {
                    if matches!(i, Ins::Set(_)) {
                        st.pop();
                    }
                    true
                }
                _ => false,
            },
            Ins::Select => {
                let n = st.len();
                if n >= 3 && st[n - 1] == Ty::I32 && st[n - 2] == st[n - 3] {
                    st.truncate(n - 2);
                    true
                } else {
                    false
                }
            }
            Ins::Op(op) => {
                let (t, k, res) = match *op {
                    Op::Un(t, _) => (t, 1, t),
                    Op::Test(t) => (t, 1, Ty::I32),
                    Op::Bin(t, _) => (t, 2, t),
                    Op::Rel(t, _) => (t, 2, Ty::I32),
                    _ => return false,
                };
                let n = st.len();
                if n >= k && st[n - k..].iter().all(|u| *u == t) {
                    st.truncate(n - k);
                    st.push(res);
                    true
                } else {
                    false
                }
            }
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Lean's `Cover`.
#[derive(Clone, Debug)]
pub enum Cover {
    Total,
    Sub(usize, Vec<usize>, Vec<Step>),
    Split1(Box<Cover>),
    Split2(Box<Cover>, Box<Cover>),
    Chain(Vec<Step>, Box<Cover>),
}

impl Cover {
    pub fn lean(&self) -> String {
        match self {
            Cover::Total => ".total".into(),
            Cover::Sub(j, p, ss) => format!(
                ".sub {j} [{}] [{}]",
                p.iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                ss.iter().map(Step::lean).collect::<Vec<_>>().join(", ")
            ),
            Cover::Split1(c) => format!(".split1 ({})", c.lean()),
            Cover::Split2(a, b) => format!(".split2 ({}) ({})", a.lean(), b.lean()),
            Cover::Chain(ss, c) => format!(
                ".chain [{}] ({})",
                ss.iter().map(Step::lean).collect::<Vec<_>>().join(", "),
                c.lean()
            ),
        }
    }

    fn steps(&self) -> usize {
        match self {
            Cover::Total => 0,
            Cover::Sub(_, _, s) => s.len(),
            Cover::Split1(c) => c.steps(),
            Cover::Split2(a, b) => a.steps() + b.steps(),
            Cover::Chain(ss, c) => ss.len() + c.steps(),
        }
    }
}

/// Lean's `safeBinOp`: the operator cannot trap on integers of type `t` with right operand `b`.
fn safe_head(t: &Term) -> bool {
    match t.op {
        Op::Bin(ty, op) => match op {
            BinOp::DivU | BinOp::RemU | BinOp::RemS => {
                matches!(t.ch[1].op, Op::Const(ct, n) if ct == ty && n != 0)
            }
            BinOp::DivS => {
                matches!(t.ch[1].op, Op::Const(ct, n) if ct == ty && n != 0 && n != ty.mask())
            }
            _ => true,
        },
        Op::Un(..) | Op::Test(_) | Op::Rel(..) => true,
        _ => false,
    }
}

pub fn no_trap(t: &Term) -> bool {
    !matches!(
        t.op,
        Op::Bin(_, BinOp::DivS | BinOp::DivU | BinOp::RemS | BinOp::RemU)
    ) && t.ch.iter().all(no_trap)
}

/// All subterms with their paths.
fn subterms<'a>(t: &'a Term, path: &mut Vec<usize>, out: &mut Vec<(Vec<usize>, &'a Term)>) {
    out.push((path.clone(), t));
    for (i, c) in t.ch.iter().enumerate() {
        path.push(i);
        subterms(c, path, out);
        path.pop();
    }
}

pub struct Prover<'a> {
    pub locals: &'a [Ty],
    pub rules: &'a [Rule],
    pub lim: Vec<Limits>,
    pub nodes: usize,
}

impl Prover<'_> {
    /// An equational chain from `l` to `r` (with the second family of computed rewrites).
    pub fn chain(&mut self, l: &Term, r: &Term) -> Option<Vec<Step>> {
        if l == r {
            return Some(vec![]);
        }
        let debug = std::env::var_os("WASM_EGRAPH_DEBUG").is_some();
        let t0 = std::time::Instant::now();
        if debug {
            eprintln!("  chain {} = {}", l.wat(), r.wat());
        }
        for lim in &self.lim {
            let mut g = EGraph::new(self.locals.to_vec(), self.rules.to_vec(), false);
            g.use_comp2 = true;
            let a = g.add_term(l);
            let b = g.add_term(r);
            g.run(lim, |g| g.find(a) == g.find(b));
            self.nodes += g.len();
            if debug {
                eprintln!("    saturated: {} nodes, {:?}", g.len(), t0.elapsed());
            }
            let mut budget = 200_000;
            if let Some(steps) = g.explain(a, b, &mut budget) {
                if debug {
                    eprintln!("    explained: {} steps, {:?}", steps.len(), t0.elapsed());
                }
                let steps = minimise(self.locals, self.rules, l, &steps);
                if debug {
                    eprintln!("    minimised: {} steps, {:?}", steps.len(), t0.elapsed());
                }
                if let Ok((t, true)) = replay(self.locals, self.rules, l, &steps)
                    && &t == r
                {
                    return Some(steps);
                }
            }
        }
        None
    }

    /// A cover of `e` by the terms `other` (`pair`: a term of `other` already proved equal,
    /// with its index and chain).
    fn cover(
        &mut self,
        e: &Term,
        other: &[Term],
        pair: Option<(usize, &Vec<Step>)>,
    ) -> Option<Cover> {
        if no_trap(e) && e.type_of(self.locals).is_some() {
            return Some(Cover::Total);
        }
        for (j, r) in other.iter().enumerate() {
            let mut subs = vec![];
            subterms(r, &mut vec![], &mut subs);
            if let Some((p, _)) = subs.iter().find(|(_, s)| *s == e) {
                return Some(Cover::Sub(j, p.clone(), vec![]));
            }
        }
        if safe_head(e) && e.type_of(self.locals).is_some() {
            let covered: Option<Vec<Cover>> =
                e.ch.iter().map(|c| self.cover(c, other, None)).collect();
            if let Some(mut cs) = covered {
                return Some(if cs.len() == 1 {
                    Cover::Split1(Box::new(cs.remove(0)))
                } else {
                    let b = cs.pop().unwrap();
                    Cover::Split2(Box::new(cs.pop().unwrap()), Box::new(b))
                });
            }
        }
        if let Some((j, c)) = pair {
            return Some(Cover::Sub(j, vec![], c.clone()));
        }
        // a trapping subterm of the other side equal to `e` (a short search per candidate)
        let saved = std::mem::replace(
            &mut self.lim,
            vec![Limits {
                iters: 8,
                nodes: 5_000,
                work: SHORT_WORK,
                backoff: None,
            }],
        );
        let mut found = None;
        'search: for (j, r) in other.iter().enumerate() {
            let mut subs = vec![];
            subterms(r, &mut vec![], &mut subs);
            for (p, s) in subs {
                if !no_trap(s)
                    && s.type_of(self.locals) == e.type_of(self.locals)
                    && let Some(c) = self.chain(e, s)
                {
                    found = Some(Cover::Sub(j, p, c));
                    break 'search;
                }
            }
        }
        self.lim = saved;
        if found.is_some() {
            return found;
        }
        // the smallest equal term (constant folding, simplification), then cover that
        let (s, steps) = self.simplest(e)?;
        if &s == e {
            return None;
        }
        let c = self.cover(&s, other, None)?;
        Some(Cover::Chain(steps, Box::new(c)))
    }

    /// The smallest term equal to `e` found by a short search, with its chain.
    fn simplest(&mut self, e: &Term) -> Option<(Term, Vec<Step>)> {
        let mut g = EGraph::new(self.locals.to_vec(), self.rules.to_vec(), false);
        g.use_comp2 = true;
        let a = g.add_term(e);
        g.run(
            &Limits {
                iters: 8,
                nodes: 5_000,
                work: SHORT_WORK,
                backoff: None,
            },
            |_| false,
        );
        self.nodes += g.len();
        let b = g.extract(a);
        let mut budget = 200_000;
        let steps = g.explain(a, b, &mut budget)?;
        let steps = minimise(self.locals, self.rules, e, &steps);
        match replay(self.locals, self.rules, e, &steps) {
            Ok((t, true)) if t == g.term(b) => Some((t, steps)),
            _ => None,
        }
    }
}

/// A certificate for `checkBody` (`locs` empty) or `checkSeg`.
pub struct SegCert {
    pub stack: Vec<Vec<Step>>,
    pub locs: Vec<Vec<Step>>,
    pub cov_a: Vec<Cover>,
    pub cov_b: Vec<Cover>,
}

impl SegCert {
    pub fn lean(&self, seg: bool) -> String {
        let chains = |cs: &[Vec<Step>]| {
            format!(
                "[{}]",
                cs.iter()
                    .map(|c| format!(
                        "[{}]",
                        c.iter().map(Step::lean).collect::<Vec<_>>().join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let covs = |cs: &[Cover]| {
            format!(
                "[{}]",
                cs.iter().map(Cover::lean).collect::<Vec<_>>().join(", ")
            )
        };
        if seg {
            format!(
                "{{ stack := {}, locs := {}, covA := {}, covB := {} }}",
                chains(&self.stack),
                chains(&self.locs),
                covs(&self.cov_a),
                covs(&self.cov_b)
            )
        } else {
            format!(
                "{{ stack := {}, covA := {}, covB := {} }}",
                chains(&self.stack),
                covs(&self.cov_a),
                covs(&self.cov_b)
            )
        }
    }

    pub fn steps(&self) -> usize {
        let cov = |c: &Cover| c.steps();
        self.stack
            .iter()
            .chain(&self.locs)
            .map(Vec::len)
            .sum::<usize>()
            + self.cov_a.iter().map(cov).sum::<usize>()
            + self.cov_b.iter().map(cov).sum::<usize>()
    }
}

/// Prove two lifted summaries equivalent (`seg`: also the locals).
pub fn prove(p: &mut Prover, a: &Sym, b: &Sym, seg: bool) -> Result<SegCert, String> {
    if a.stack.len() != b.stack.len() {
        return Err(format!(
            "{} results against {}",
            a.stack.len(),
            b.stack.len()
        ));
    }
    let mut stack = vec![];
    for (x, y) in a.stack.iter().zip(&b.stack) {
        stack.push(
            p.chain(x, y)
                .ok_or_else(|| format!("no proof of {} = {}", x.wat(), y.wat()))?,
        );
    }
    let mut locs = vec![];
    if seg {
        for (x, y) in a.locs.iter().zip(&b.locs) {
            locs.push(
                p.chain(x, y)
                    .ok_or_else(|| format!("no proof of local {} = {}", x.wat(), y.wat()))?,
            );
        }
    }
    let (ta, tb) = (a.terms(), b.terms());
    let (ga, gb) = (a.guards.len(), b.guards.len());
    // the numbers of locals differ for function-entry pairs (`checkFunc`)
    let (na, nb) = (a.locs.len(), b.locs.len());
    let mut cov_a = vec![];
    for (k, e) in ta.iter().enumerate() {
        // the paired slot of the other side (stack slots; locals for segments)
        let pair = if k >= ga + na {
            Some((gb + nb + (k - ga - na), &stack[k - ga - na]))
        } else if seg && k >= ga {
            Some((gb + (k - ga), &locs[k - ga]))
        } else {
            None
        };
        cov_a.push(
            p.cover(e, &tb, pair)
                .ok_or_else(|| format!("the trap of {} is not covered", e.wat()))?,
        );
    }
    let mut cov_b = vec![];
    for (k, e) in tb.iter().enumerate() {
        // the paired slot of the other side, with the inverted chain
        let back = if k >= gb + nb {
            let i = k - gb - nb;
            invert(p.locals, p.rules, &a.stack[i], &stack[i]).map(|c| (ga + na + i, c))
        } else if seg && k >= gb {
            let i = k - gb;
            invert(p.locals, p.rules, &a.locs[i], &locs[i]).map(|c| (ga + i, c))
        } else {
            None
        };
        let pair = back.as_ref().map(|(j, c)| (*j, c));
        cov_b.push(
            p.cover(e, &ta, pair)
                .ok_or_else(|| format!("the trap of {} is not covered", e.wat()))?,
        );
    }
    Ok(SegCert {
        stack,
        locs,
        cov_a,
        cov_b,
    })
}

pub fn lean_instrs(is: &[Ins]) -> String {
    format!(
        "[{}]",
        is.iter().map(Ins::lean).collect::<Vec<_>>().join(", ")
    )
}
