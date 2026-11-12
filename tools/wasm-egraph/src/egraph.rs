//! An e-graph with explanations, in the style of egg (Willsey et al., POPL 2021) and of
//! "Proof-producing congruence closure" (Nieuwenhuis and Oliveras, 2005).
//!
//! Every node id is a *concrete* term: its children are node ids, not classes, so
//! `term(id)` is a finite tree. Classes are a union-find over node ids. Each union adds
//! an edge to a proof forest, labelled by why the two concrete terms are equal: a rule
//! application at the root, constant folding at the root, or congruence (same operator,
//! children already equal). An explanation of `a = b` follows the unique forest path;
//! congruence edges recurse into the children with a path prefix. Paths in the forest
//! never change once two nodes are connected, so the recursion only uses older edges
//! and terminates.

use crate::rules::{Pat, Rule};
use crate::term::{BinOp, Op, Term, Ty, fold};
use std::collections::HashMap;

pub type Id = usize;

#[derive(Clone, Debug)]
enum Just {
    /// `from` rewrites to the other end by `rule`, forward (`fwd`) or backward.
    Rule {
        rule: usize,
        fwd: bool,
        from: Id,
    },
    /// `from` (an operator on constants) folds to the other end.
    Fold {
        from: Id,
    },
    /// `from` rewrites to the other end by a computed rewrite (`Term.comp?`).
    Comp {
        from: Id,
    },
    /// `from` rewrites to the other end by a computed rewrite of the second family
    /// (Lean's `Silmaril.Wasm.Auto.ESeg.comp2?`).
    Comp2 {
        from: Id,
    },
    Congr,
}

/// One step of a certificate (Lean's `Step`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    Rw {
        rule: usize,
        fwd: bool,
        path: Vec<usize>,
        extra: Vec<(u32, Term)>,
    },
    Fold {
        path: Vec<usize>,
    },
    Unfold {
        path: Vec<usize>,
        b: Term,
    },
    Comp {
        path: Vec<usize>,
    },
    Uncomp {
        path: Vec<usize>,
        b: Term,
    },
    Comp2 {
        path: Vec<usize>,
    },
    Uncomp2 {
        path: Vec<usize>,
        b: Term,
    },
}

impl Step {
    pub fn lean(&self) -> String {
        let p = |p: &[usize]| {
            format!(
                "[{}]",
                p.iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        match self {
            Step::Rw {
                rule,
                fwd,
                path,
                extra,
            } => {
                let ex: Vec<String> = extra
                    .iter()
                    .map(|(n, t)| format!("({n}, {})", t.lean()))
                    .collect();
                format!(".rw {rule} {fwd} {} [{}]", p(path), ex.join(", "))
            }
            Step::Fold { path } => format!(".fold {}", p(path)),
            Step::Unfold { path, b } => format!(".unfold {} {}", p(path), b.lean()),
            Step::Comp { path } => format!(".comp {}", p(path)),
            Step::Uncomp { path, b } => format!(".uncomp {} {}", p(path), b.lean()),
            Step::Comp2 { path } => format!(".comp2 {}", p(path)),
            Step::Uncomp2 { path, b } => format!(".uncomp2 {} {}", p(path), b.lean()),
        }
    }

    fn prefixed(&self, i: usize) -> Step {
        let pre = |p: &Vec<usize>| {
            let mut q = vec![i];
            q.extend(p);
            q
        };
        match self {
            Step::Rw {
                rule,
                fwd,
                path,
                extra,
            } => Step::Rw {
                rule: *rule,
                fwd: *fwd,
                path: pre(path),
                extra: extra.clone(),
            },
            Step::Fold { path } => Step::Fold { path: pre(path) },
            Step::Unfold { path, b } => Step::Unfold {
                path: pre(path),
                b: b.clone(),
            },
            Step::Comp { path } => Step::Comp { path: pre(path) },
            Step::Uncomp { path, b } => Step::Uncomp {
                path: pre(path),
                b: b.clone(),
            },
            Step::Comp2 { path } => Step::Comp2 { path: pre(path) },
            Step::Uncomp2 { path, b } => Step::Uncomp2 {
                path: pre(path),
                b: b.clone(),
            },
        }
    }
}

/// The work limit of a search (`Limits::work`), calibrated to about what 5 s of
/// search did on an idle build host (see `tests/run.sh` and `docs/projects/wasm-binaryen-tooling.md`).
pub const WORK: u64 = 5_000_000;

/// The work limit of the short searches for covers (formerly a 3 s timeout).
pub const SHORT_WORK: u64 = 3_000_000;

/// Matches collected per iteration, at most.
const MAX_MATCHES: usize = 200_000;

/// Search limits. All of them count work, not time, so a search gives the same answer on
/// an idle and on a loaded host (an earlier version also stopped after 5 s of wall-clock time).
pub struct Limits {
    pub iters: usize,
    pub nodes: usize,
    /// Work, at most: one unit per pattern tried at a class, per match found, per match
    /// applied, and per e-node at each rebuild (`EGraph::work`).
    pub work: u64,
    /// Backoff scheduling (egg's `BackoffScheduler`): a rule direction whose matches in one
    /// iteration exceed `match_limit << times_banned` is banned for `ban_length << times_banned`
    /// iterations. `None` applies every rule in every iteration (the pass-1 behaviour).
    pub backoff: Option<Backoff>,
}

#[derive(Clone, Copy, Debug)]
pub struct Backoff {
    pub match_limit: usize,
    pub ban_length: usize,
}

/// Per rule direction: how often it was banned and until which iteration.
#[derive(Clone, Copy, Debug, Default)]
struct BanState {
    times_banned: u32,
    banned_until: usize,
}

pub struct EGraph {
    pub locals: Vec<Ty>,
    pub rules: Vec<Rule>,
    /// Use refinement rules too (as if they were equations; explanations that use one
    /// backwards are rejected later).
    pub use_ref: bool,
    ops: Vec<Op>,
    ch: Vec<Vec<Id>>,
    ty: Vec<Option<Ty>>,
    /// The node's term has no division or remainder.
    total: Vec<bool>,
    uf: Vec<Id>,
    members: HashMap<Id, Vec<Id>>,
    memo: HashMap<(Op, Vec<Id>), Id>,
    fparent: Vec<Id>,
    fjust: Vec<Option<Just>>,
    pub unions: usize,
    /// Scheduler state per (rule, direction).
    bans: HashMap<(usize, bool), BanState>,
    /// The current iteration (for the scheduler).
    iter: usize,
    /// Rule directions banned at least once (for reports).
    pub banned: usize,
    /// Use the second family of computed rewrites (only the segment checker knows them).
    pub use_comp2: bool,
    /// Work done by the current `run` (see `Limits::work`).
    pub work: u64,
}

impl EGraph {
    pub fn new(locals: Vec<Ty>, rules: Vec<Rule>, use_ref: bool) -> EGraph {
        EGraph {
            locals,
            rules,
            use_ref,
            ops: vec![],
            ch: vec![],
            ty: vec![],
            total: vec![],
            uf: vec![],
            members: HashMap::new(),
            memo: HashMap::new(),
            fparent: vec![],
            fjust: vec![],
            unions: 0,
            bans: HashMap::new(),
            iter: 0,
            banned: 0,
            use_comp2: false,
            work: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }

    pub fn find(&self, mut a: Id) -> Id {
        while self.uf[a] != a {
            a = self.uf[a];
        }
        a
    }

    fn find_mut(&mut self, a: Id) -> Id {
        let r = self.find(a);
        let mut x = a;
        while self.uf[x] != r {
            let n = self.uf[x];
            self.uf[x] = r;
            x = n;
        }
        r
    }

    fn key(&self, op: &Op, ch: &[Id]) -> (Op, Vec<Id>) {
        (op.clone(), ch.iter().map(|&c| self.find(c)).collect())
    }

    /// Add a concrete node; returns an id whose term is exactly `op(term(ch))`.
    pub fn add(&mut self, op: Op, ch: Vec<Id>) -> Id {
        let key = self.key(&op, &ch);
        if let Some(&m) = self.memo.get(&key)
            && self.ch[m] == ch
        {
            return m;
        }
        let tys: Vec<Option<Ty>> = ch.iter().map(|&c| self.ty[c]).collect();
        let ty = op.type_of(&self.locals, &tys);
        let total = !matches!(
            op,
            Op::Bin(_, BinOp::DivS | BinOp::DivU | BinOp::RemS | BinOp::RemU)
        ) && ch.iter().all(|&c| self.total[c]);
        let id = self.ops.len();
        self.ops.push(op);
        self.ch.push(ch);
        self.ty.push(ty);
        self.total.push(total);
        self.uf.push(id);
        self.fparent.push(id);
        self.fjust.push(None);
        self.members.insert(id, vec![id]);
        match self.memo.get(&key) {
            Some(&m) => {
                self.union(id, m, Just::Congr);
            }
            None => {
                self.memo.insert(key, id);
            }
        }
        id
    }

    pub fn add_term(&mut self, t: &Term) -> Id {
        let ch = t.ch.iter().map(|c| self.add_term(c)).collect();
        self.add(t.op.clone(), ch)
    }

    pub fn term(&self, id: Id) -> Term {
        Term {
            op: self.ops[id].clone(),
            ch: self.ch[id].iter().map(|&c| self.term(c)).collect(),
        }
    }

    /// Re-root the proof tree of `a` at `a`.
    fn reroot(&mut self, a: Id) {
        let mut prev = a;
        let mut prev_just: Option<Just> = None;
        let mut x = a;
        loop {
            let p = self.fparent[x];
            let j = self.fjust[x].take();
            self.fparent[x] = prev;
            self.fjust[x] = prev_just;
            if p == x {
                break;
            }
            prev = x;
            prev_just = j;
            x = p;
        }
        self.fparent[a] = a;
        self.fjust[a] = None;
    }

    fn union(&mut self, a: Id, b: Id, j: Just) -> bool {
        let (ra, rb) = (self.find_mut(a), self.find_mut(b));
        if ra == rb {
            return false;
        }
        self.reroot(a);
        self.fparent[a] = b;
        self.fjust[a] = Some(j);
        let (big, small) = {
            let la = self.members[&ra].len();
            let lb = self.members[&rb].len();
            if la >= lb { (ra, rb) } else { (rb, ra) }
        };
        self.uf[small] = big;
        let moved = self.members.remove(&small).unwrap();
        self.members.get_mut(&big).unwrap().extend(moved);
        self.unions += 1;
        true
    }

    /// Restore the congruence invariant.
    pub fn rebuild(&mut self) {
        loop {
            let mut memo: HashMap<(Op, Vec<Id>), Id> = HashMap::new();
            let mut todo = vec![];
            for id in 0..self.ops.len() {
                let key = self.key(&self.ops[id], &self.ch[id]);
                match memo.get(&key) {
                    Some(&m) if self.find(m) != self.find(id) => todo.push((id, m)),
                    Some(_) => {}
                    None => {
                        memo.insert(key, id);
                    }
                }
            }
            if todo.is_empty() {
                self.memo = memo;
                return;
            }
            for (a, b) in todo {
                self.union(a, b, Just::Congr);
            }
        }
    }

    /// A member of class `c` of type `t` (and without division, if `total`).
    fn typed_member(&self, c: Id, t: Ty, total: bool) -> Option<Id> {
        self.members[&self.find(c)]
            .iter()
            .copied()
            .find(|&m| self.ty[m] == Some(t) && (!total || self.total[m]))
    }

    /// E-matching: all substitutions (variable -> class) under which `p` matches class `c`.
    fn ematch(&self, p: &Pat, c: Id, s: &[(u32, Id)], out: &mut Vec<Vec<(u32, Id)>>) {
        let c = self.find(c);
        match p {
            Pat::Var(t, n) | Pat::TVar(t, n) => {
                if self
                    .typed_member(c, *t, matches!(p, Pat::TVar(..)))
                    .is_none()
                {
                    return;
                }
                match s.iter().find(|(m, _)| m == n) {
                    Some((_, d)) => {
                        if self.find(*d) == c {
                            out.push(s.to_vec());
                        }
                    }
                    None => {
                        let mut s2 = s.to_vec();
                        s2.push((*n, c));
                        out.push(s2);
                    }
                }
            }
            Pat::Node(op, pch) => {
                for &m in &self.members[&c] {
                    if out.len() > MAX_MATCHES {
                        // a pathological class (associativity and commutativity): give up on it
                        return;
                    }
                    if &self.ops[m] != op {
                        continue;
                    }
                    let mut partial = vec![s.to_vec()];
                    for (i, pc) in pch.iter().enumerate() {
                        let mut next = vec![];
                        for s1 in &partial {
                            if next.len() > MAX_MATCHES {
                                break;
                            }
                            self.ematch(pc, self.ch[m][i], s1, &mut next);
                        }
                        partial = next;
                        if partial.is_empty() {
                            break;
                        }
                    }
                    out.extend(partial);
                }
            }
        }
    }

    /// Instantiate a pattern with typed class representatives.
    fn inst(&mut self, p: &Pat, s: &[(u32, Id)]) -> Option<Id> {
        match p {
            Pat::Var(t, n) | Pat::TVar(t, n) => {
                let c = s.iter().find(|(m, _)| m == n)?.1;
                self.typed_member(c, *t, matches!(p, Pat::TVar(..)))
            }
            Pat::Node(op, pch) => {
                let mut ch = vec![];
                for pc in pch {
                    ch.push(self.inst(pc, s)?);
                }
                Some(self.add(op.clone(), ch))
            }
        }
    }

    /// One round of rule applications and constant folding; returns whether anything
    /// changed.
    fn step(&mut self, lim: &Limits, start: std::time::Instant) -> bool {
        let _ = start;
        let mut matches = vec![];
        let mut roots: Vec<Id> = self.members.keys().copied().collect();
        roots.sort_unstable();
        for (ri, r) in self.rules.iter().enumerate() {
            if r.is_ref && !self.use_ref {
                continue;
            }
            for (fwd, src) in [(true, &r.lhs), (false, &r.rhs)] {
                if !fwd && r.is_ref {
                    continue;
                }
                if let Pat::Var(..) | Pat::TVar(..) = src {
                    // a bare variable matches everything; such directions only grow the graph
                    continue;
                }
                let ban = self.bans.get(&(ri, fwd)).copied().unwrap_or_default();
                if lim.backoff.is_some() && ban.banned_until > self.iter {
                    continue;
                }
                let mut mine = vec![];
                for &c in &roots {
                    if matches.len() + mine.len() > MAX_MATCHES || self.work > lim.work {
                        break;
                    }
                    let mut out = vec![];
                    self.ematch(src, c, &[], &mut out);
                    self.work += 1 + out.len() as u64;
                    for s in out {
                        mine.push((ri, fwd, s));
                    }
                }
                if let Some(b) = lim.backoff {
                    let threshold = b.match_limit << ban.times_banned;
                    if mine.len() > threshold {
                        let len = b.ban_length << ban.times_banned;
                        if ban.times_banned == 0 {
                            self.banned += 1;
                        }
                        self.bans.insert(
                            (ri, fwd),
                            BanState {
                                times_banned: ban.times_banned + 1,
                                banned_until: self.iter + len,
                            },
                        );
                        continue;
                    }
                }
                matches.extend(mine);
            }
        }
        let mut changed = false;
        let debug = std::env::var_os("WASM_EGRAPH_DEBUG").is_some();
        if debug {
            eprintln!("        {} matches, {:?}", matches.len(), start.elapsed());
        }
        for (ri, fwd, s) in matches {
            if self.len() > lim.nodes || self.work > lim.work {
                break;
            }
            self.work += 1;
            let r = self.rules[ri].clone();
            let (src, dst) = if fwd {
                (&r.lhs, &r.rhs)
            } else {
                (&r.rhs, &r.lhs)
            };
            let Some(x) = self.inst(src, &s) else {
                continue;
            };
            let Some(y) = self.inst(dst, &s) else {
                continue;
            };
            if self.find(x) != self.find(y) {
                self.union(
                    x,
                    y,
                    Just::Rule {
                        rule: ri,
                        fwd,
                        from: x,
                    },
                );
                changed = true;
            }
        }
        if debug {
            eprintln!(
                "        applied: {} nodes, {:?}",
                self.len(),
                start.elapsed()
            );
        }
        self.rebuild();
        self.work += self.len() as u64;
        if debug {
            eprintln!("        rebuilt, {:?}", start.elapsed());
        }
        changed |= self.fold_constants();
        self.rebuild();
        self.work += self.len() as u64;
        if debug {
            eprintln!("        folded, {:?}", start.elapsed());
        }
        changed |= self.computed();
        self.rebuild();
        self.work += self.len() as u64;
        if debug {
            eprintln!("        computed, {:?}", start.elapsed());
        }
        if self.use_comp2 {
            changed |= self.computed2();
            self.rebuild();
            self.work += self.len() as u64;
        }
        changed
    }

    fn konst(&self, id: Id) -> Option<(Ty, u64)> {
        match self.ops[id] {
            Op::Const(t, n) => Some((t, n)),
            _ => None,
        }
    }

    /// `comp2_term` on the concrete node `x`, building the result from node ids.
    fn comp2_node(&mut self, x: Id) -> Option<Id> {
        use crate::term::RelOp;
        if self.ops[x] == Op::Bin(Ty::I32, BinOp::And) {
            for (k, b) in [(0, 1), (1, 0)] {
                let (ck, cb) = (self.ch[x][k], self.ch[x][b]);
                if matches!(self.ops[ck], Op::Const(Ty::I32, c) if c % 2 == 1)
                    && matches!(self.ops[cb], Op::Test(_) | Op::Rel(..))
                {
                    return Some(cb);
                }
            }
        }
        match self.ops[x].clone() {
            Op::Bin(ty, op) => {
                let (ct, n) = self.konst(self.ch[x][1])?;
                if ct != ty {
                    return None;
                }
                let w = ty.width() as u64;
                match op {
                    BinOp::Shl | BinOp::ShrU | BinOp::ShrS => {
                        let inner = self.ch[x][0];
                        if self.ops[inner] != Op::Bin(ty, op) {
                            return None;
                        }
                        let (c1, m) = self.konst(self.ch[inner][1])?;
                        if !(c1 == ty && m < w && n < w && m + n < w) {
                            return None;
                        }
                        let a = self.ch[inner][0];
                        let c = self.add(Op::Const(ty, m + n), vec![]);
                        Some(self.add(Op::Bin(ty, op), vec![a, c]))
                    }
                    BinOp::DivS => {
                        let k = pow2_below(ty.width() - 1, n)? as u64;
                        if k == 0 {
                            return None;
                        }
                        let a = self.ch[x][0];
                        let c1 = self.add(Op::Const(ty, w - 1), vec![]);
                        let sign = self.add(Op::Bin(ty, BinOp::ShrS), vec![a, c1]);
                        let c2 = self.add(Op::Const(ty, w - k), vec![]);
                        let bias = self.add(Op::Bin(ty, BinOp::ShrU), vec![sign, c2]);
                        let sum = self.add(Op::Bin(ty, BinOp::Add), vec![a, bias]);
                        let c3 = self.add(Op::Const(ty, k), vec![]);
                        Some(self.add(Op::Bin(ty, BinOp::ShrS), vec![sum, c3]))
                    }
                    _ => None,
                }
            }
            Op::Rel(ty, op) => {
                let (ct, n) = self.konst(self.ch[x][1])?;
                if ct != ty {
                    return None;
                }
                let a = self.ch[x][0];
                match (op, n) {
                    (RelOp::LtU, 1) | (RelOp::LeU, 0) => Some(self.add(Op::Test(ty), vec![a])),
                    (RelOp::GtU, 0) | (RelOp::GeU, 1) => {
                        let z = self.add(Op::Const(ty, 0), vec![]);
                        Some(self.add(Op::Rel(ty, RelOp::Ne), vec![a, z]))
                    }
                    (RelOp::LtS, 0) if ty == Ty::I32 => {
                        let c = self.add(Op::Const(Ty::I32, 31), vec![]);
                        Some(self.add(Op::Bin(Ty::I32, BinOp::ShrU), vec![a, c]))
                    }
                    _ => None,
                }
            }
            Op::Test(ty) => {
                let inner = self.ch[x][0];
                if self.ops[inner] != Op::Bin(ty, BinOp::RemS) {
                    return None;
                }
                let (ct, n) = self.konst(self.ch[inner][1])?;
                if ct != ty {
                    return None;
                }
                pow2_below(ty.width() - 1, n)?;
                let a = self.ch[inner][0];
                let c = self.add(Op::Const(ty, n - 1), vec![]);
                let and = self.add(Op::Bin(ty, BinOp::And), vec![a, c]);
                Some(self.add(Op::Test(ty), vec![and]))
            }
            _ => None,
        }
    }

    /// The second family of computed rewrites (`comp2_term`), on concrete nodes built from
    /// class members: a node whose term `comp2_term` rewrites is united with the result.
    fn computed2(&mut self) -> bool {
        let n = self.len();
        // one pass: the first constant and the first node of each operator, per class
        let mut konst: HashMap<Id, Id> = HashMap::new();
        let mut by_op: HashMap<(Id, Op), Id> = HashMap::new();
        for id in 0..n {
            let r = self.find(id);
            if matches!(self.ops[id], Op::Const(..)) {
                konst.entry(r).or_insert(id);
            } else if self.ops[id].arity() > 0 {
                by_op.entry((r, self.ops[id].clone())).or_insert(id);
            }
        }
        let kof = |g: &EGraph, c: Id, t: Ty| {
            konst
                .get(&g.find(c))
                .copied()
                .filter(|&k| matches!(g.ops[k], Op::Const(ct, _) if ct == t))
        };
        let mut cands: Vec<Id> = vec![];
        for id in 0..n {
            if self.ops[id] == Op::Bin(Ty::I32, BinOp::And) {
                let (l, r) = (self.ch[id][0], self.ch[id][1]);
                let bool_of = |g: &EGraph, c: Id| {
                    g.members[&g.find(c)]
                        .iter()
                        .copied()
                        .find(|&m| matches!(g.ops[m], Op::Test(_) | Op::Rel(..)))
                };
                if let (Some(k), Some(b)) = (kof(self, l, Ty::I32), bool_of(self, r)) {
                    cands.push(self.add(Op::Bin(Ty::I32, BinOp::And), vec![k, b]));
                }
                if let (Some(b), Some(k)) = (bool_of(self, l), kof(self, r, Ty::I32)) {
                    cands.push(self.add(Op::Bin(Ty::I32, BinOp::And), vec![b, k]));
                }
            }
            match self.ops[id].clone() {
                Op::Bin(t, op) => {
                    let (l, r) = (self.ch[id][0], self.ch[id][1]);
                    let Some(k) = kof(self, r, t) else { continue };
                    if matches!(op, BinOp::Shl | BinOp::ShrU | BinOp::ShrS) {
                        if let Some(&m) = by_op.get(&(self.find(l), Op::Bin(t, op)))
                            && let Some(k0) = kof(self, self.ch[m][1], t)
                        {
                            let inner = self.add(Op::Bin(t, op), vec![self.ch[m][0], k0]);
                            cands.push(self.add(Op::Bin(t, op), vec![inner, k]));
                        }
                    } else if op == BinOp::DivS {
                        cands.push(self.add(Op::Bin(t, op), vec![l, k]));
                    }
                }
                Op::Rel(t, _) => {
                    let (l, r) = (self.ch[id][0], self.ch[id][1]);
                    if let Some(k) = kof(self, r, t) {
                        cands.push(self.add(self.ops[id].clone(), vec![l, k]));
                    }
                }
                Op::Test(t) => {
                    if let Some(&m) =
                        by_op.get(&(self.find(self.ch[id][0]), Op::Bin(t, BinOp::RemS)))
                        && let Some(k) = kof(self, self.ch[m][1], t)
                    {
                        let inner = self.add(Op::Bin(t, BinOp::RemS), vec![self.ch[m][0], k]);
                        cands.push(self.add(Op::Test(t), vec![inner]));
                    }
                }
                _ => {}
            }
        }
        let mut changed = false;
        cands.sort_unstable();
        cands.dedup();
        for x in cands {
            // built on node ids (a concrete term can be exponentially large as a tree)
            let Some(y) = self.comp2_node(x) else {
                continue;
            };
            if self.find(x) != self.find(y) {
                self.union(x, y, Just::Comp2 { from: x });
                changed = true;
            }
        }
        changed
    }

    /// Computed rewrites: a binary operator whose right operand class has a constant.
    fn computed(&mut self) -> bool {
        let mut changed = false;
        let n = self.len();
        for id in 0..n {
            let Op::Bin(t, op) = self.ops[id].clone() else {
                continue;
            };
            let (l, r) = (self.ch[id][0], self.ch[id][1]);
            let consts: Vec<(Id, u64)> = self.members[&self.find(r)]
                .iter()
                .filter_map(|&m| match self.ops[m] {
                    Op::Const(ct, v) if ct == t => Some((m, v)),
                    _ => None,
                })
                .collect();
            for (k, v) in consts {
                let Some((op2, v2)) = comp(t, op, v) else {
                    continue;
                };
                let x = self.add(Op::Bin(t, op), vec![l, k]);
                let c = self.add(Op::Const(t, v2), vec![]);
                let y = self.add(Op::Bin(t, op2), vec![l, c]);
                if self.find(x) != self.find(y) {
                    self.union(x, y, Just::Comp { from: x });
                    changed = true;
                }
            }
        }
        changed
    }

    /// Constant folding: an operator whose operand classes contain constants.
    fn fold_constants(&mut self) -> bool {
        let mut changed = false;
        let n = self.len();
        for id in 0..n {
            let op = self.ops[id].clone();
            if op.arity() == 0 {
                continue;
            }
            let mut consts = vec![];
            for &c in &self.ch[id].clone() {
                let k = self.members[&self.find(c)]
                    .iter()
                    .copied()
                    .find(|&m| matches!(self.ops[m], Op::Const(..)));
                match k {
                    Some(k) => consts.push(k),
                    None => break,
                }
            }
            if consts.len() != op.arity() {
                continue;
            }
            let operand_ty = match &op {
                Op::Un(t, _) | Op::Test(t) | Op::Bin(t, _) | Op::Rel(t, _) => *t,
                _ => continue,
            };
            let vals: Vec<u64> = consts
                .iter()
                .filter_map(|&k| match self.ops[k] {
                    Op::Const(t, v) if t == operand_ty => Some(v),
                    _ => None,
                })
                .collect();
            if vals.len() != consts.len() {
                continue;
            }
            let Some((rt, v)) = fold(&op, &vals) else {
                continue;
            };
            let x = self.add(op, consts);
            let y = self.add(Op::Const(rt, v), vec![]);
            if self.find(x) != self.find(y) {
                self.union(x, y, Just::Fold { from: x });
                changed = true;
            }
        }
        changed
    }

    /// Saturate until `stop` holds, nothing changes, or a limit is hit; returns the
    /// number of iterations.
    pub fn run(&mut self, lim: &Limits, mut stop: impl FnMut(&EGraph) -> bool) -> usize {
        let start = std::time::Instant::now();
        self.work = 0;
        self.rebuild();
        let mut it = 0;
        let debug = std::env::var_os("WASM_EGRAPH_DEBUG").is_some();
        while it < lim.iters && !stop(self) {
            it += 1;
            self.iter = it;
            if debug {
                eprintln!(
                    "      iter {it}: {} nodes, {:?}",
                    self.len(),
                    start.elapsed()
                );
            }
            if !self.step(lim, start) && !self.any_banned() {
                break;
            }
            if self.len() > lim.nodes || self.work > lim.work {
                break;
            }
        }
        if std::env::var_os("WASM_EGRAPH_WORK").is_some() {
            eprintln!(
                "      work {} in {:?} ({} nodes, {it} iterations)",
                self.work,
                start.elapsed(),
                self.len()
            );
        }
        it
    }

    /// Some rule direction is banned now (so an iteration without change is not saturation).
    fn any_banned(&self) -> bool {
        self.bans.values().any(|b| b.banned_until > self.iter)
    }

    /// The smallest term of a class.
    pub fn extract(&mut self, root: Id) -> Id {
        let n = self.len();
        let mut best: HashMap<Id, (usize, Id)> = HashMap::new();
        let mut changed = true;
        while changed {
            changed = false;
            for id in 0..n {
                let mut cost = 1usize;
                let mut ok = true;
                for &c in &self.ch[id] {
                    match best.get(&self.find(c)) {
                        Some((k, _)) => cost = cost.saturating_add(*k),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                let r = self.find(id);
                if best.get(&r).is_none_or(|(k, _)| cost < *k) {
                    best.insert(r, (cost, id));
                    changed = true;
                }
            }
        }
        self.build_best(root, &best)
    }

    fn build_best(&mut self, c: Id, best: &HashMap<Id, (usize, Id)>) -> Id {
        let (_, id) = best[&self.find(c)];
        let ch: Vec<Id> = self.ch[id].clone();
        let ch: Vec<Id> = ch.into_iter().map(|k| self.build_best(k, best)).collect();
        self.add(self.ops[id].clone(), ch)
    }

    fn ancestors(&self, a: Id) -> Vec<Id> {
        let mut v = vec![a];
        let mut x = a;
        while self.fparent[x] != x {
            x = self.fparent[x];
            v.push(x);
        }
        v
    }

    /// Steps taking `term(a)` to `term(b)`; `None` if they are not in one class or the
    /// explanation exceeds `budget` steps.
    pub fn explain(&self, a: Id, b: Id, budget: &mut usize) -> Option<Vec<Step>> {
        if self.find(a) != self.find(b) {
            return None;
        }
        if a == b {
            return Some(vec![]);
        }
        let pa = self.ancestors(a);
        let pb = self.ancestors(b);
        let lca = *pa.iter().find(|x| pb.contains(x))?;
        let mut steps = vec![];
        // a up to the lca: each edge x -> parent(x)
        for &x in pa.iter().take_while(|&&x| x != lca) {
            let y = self.fparent[x];
            steps.extend(self.explain_edge(x, y, self.fjust[x].as_ref()?, budget)?);
        }
        // the lca down to b: edges parent(x) -> x, in reverse order
        let down: Vec<Id> = pb.iter().copied().take_while(|&x| x != lca).collect();
        for &x in down.iter().rev() {
            let y = self.fparent[x];
            steps.extend(self.explain_edge(y, x, self.fjust[x].as_ref()?, budget)?);
        }
        if steps.len() > *budget {
            return None;
        }
        *budget -= steps.len();
        Some(steps)
    }

    fn explain_edge(&self, u: Id, v: Id, j: &Just, budget: &mut usize) -> Option<Vec<Step>> {
        match j {
            Just::Rule { rule, fwd, from } => {
                let fwd = if *from == u { *fwd } else { !*fwd };
                let r = &self.rules[*rule];
                let (src, dst) = if fwd {
                    (&r.lhs, &r.rhs)
                } else {
                    (&r.rhs, &r.lhs)
                };
                // bindings for the variables only the replacing side has, read off `term(v)`
                let mut sv = vec![];
                src.all_vars(&mut sv);
                let mut sd = vec![];
                if !pmatch(&self.locals, dst, &self.term(v), &mut sd) {
                    return None;
                }
                let extra = sd.into_iter().filter(|(n, _)| !sv.contains(n)).collect();
                Some(vec![Step::Rw {
                    rule: *rule,
                    fwd,
                    path: vec![],
                    extra,
                }])
            }
            Just::Fold { from } => {
                if *from == u {
                    Some(vec![Step::Fold { path: vec![] }])
                } else {
                    Some(vec![Step::Unfold {
                        path: vec![],
                        b: self.term(v),
                    }])
                }
            }
            Just::Comp { from } => {
                if *from == u {
                    Some(vec![Step::Comp { path: vec![] }])
                } else {
                    Some(vec![Step::Uncomp {
                        path: vec![],
                        b: self.term(v),
                    }])
                }
            }
            Just::Comp2 { from } => {
                if *from == u {
                    Some(vec![Step::Comp2 { path: vec![] }])
                } else {
                    Some(vec![Step::Uncomp2 {
                        path: vec![],
                        b: self.term(v),
                    }])
                }
            }
            Just::Congr => {
                let mut out = vec![];
                for (i, (&cu, &cv)) in self.ch[u].iter().zip(&self.ch[v]).enumerate() {
                    let sub = self.explain(cu, cv, budget)?;
                    out.extend(sub.iter().map(|s| s.prefixed(i)));
                }
                Some(out)
            }
        }
    }
}

/// Replay steps on a term with the same matching rules as Lean's checker; returns the
/// final term and whether every step was an equation.
pub fn replay(
    locals: &[Ty],
    rules: &[Rule],
    t: &Term,
    steps: &[Step],
) -> Result<(Term, bool), String> {
    let mut cur = t.clone();
    let mut all_eq = true;
    for (k, s) in steps.iter().enumerate() {
        cur = match s {
            Step::Rw {
                rule,
                fwd,
                path,
                extra,
            } => {
                let r = rules.get(*rule).ok_or("no such rule")?;
                if r.is_ref {
                    if !fwd {
                        return Err(format!(
                            "step {k}: refinement rule {} used backwards",
                            r.name
                        ));
                    }
                    all_eq = false;
                }
                let (src, dst) = if *fwd {
                    (&r.lhs, &r.rhs)
                } else {
                    (&r.rhs, &r.lhs)
                };
                let sub = cur.get(path).ok_or_else(|| format!("step {k}: bad path"))?;
                let mut s = extra.clone();
                if !pmatch(locals, src, sub, &mut s) {
                    return Err(format!(
                        "step {k}: rule {} does not match {}",
                        r.name,
                        sub.wat()
                    ));
                }
                let b = pinst(dst, &s).ok_or_else(|| format!("step {k}: unbound variable"))?;
                let mut chk = vec![];
                if !pmatch(locals, dst, &b, &mut chk) {
                    return Err(format!(
                        "step {k}: replacement binds a variable at the wrong type"
                    ));
                }
                cur.set(path, b).ok_or("bad path")?
            }
            Step::Fold { path } => {
                let sub = cur.get(path).ok_or("bad path")?;
                let b =
                    fold_term(sub).ok_or_else(|| format!("step {k}: cannot fold {}", sub.wat()))?;
                cur.set(path, b).ok_or("bad path")?
            }
            Step::Unfold { path, b } => {
                let sub = cur.get(path).ok_or("bad path")?;
                if fold_term(b).as_ref() != Some(sub) {
                    return Err(format!("step {k}: bad unfold"));
                }
                cur.set(path, b.clone()).ok_or("bad path")?
            }
            Step::Comp { path } => {
                let sub = cur.get(path).ok_or("bad path")?;
                let b = comp_term(sub)
                    .ok_or_else(|| format!("step {k}: no computed rewrite of {}", sub.wat()))?;
                cur.set(path, b).ok_or("bad path")?
            }
            Step::Uncomp { path, b } => {
                let sub = cur.get(path).ok_or("bad path")?;
                if comp_term(b).as_ref() != Some(sub) {
                    return Err(format!("step {k}: bad uncomp"));
                }
                cur.set(path, b.clone()).ok_or("bad path")?
            }
            Step::Comp2 { path } => {
                let sub = cur.get(path).ok_or("bad path")?;
                let b = comp2_term(sub)
                    .ok_or_else(|| format!("step {k}: no comp2 rewrite of {}", sub.wat()))?;
                cur.set(path, b).ok_or("bad path")?
            }
            Step::Uncomp2 { path, b } => {
                let sub = cur.get(path).ok_or("bad path")?;
                if comp2_term(b).as_ref() != Some(sub) {
                    return Err(format!("step {k}: bad uncomp2"));
                }
                cur.set(path, b.clone()).ok_or("bad path")?
            }
        };
    }
    Ok((cur, all_eq))
}

/// Invert an equational chain from `t`: the steps taking its end back to `t`. `None` if a
/// step does not replay or is a refinement.
pub fn invert(locals: &[Ty], rules: &[Rule], t: &Term, steps: &[Step]) -> Option<Vec<Step>> {
    let mut terms = vec![t.clone()];
    for k in 0..steps.len() {
        let (u, eq) = replay(locals, rules, terms.last().unwrap(), &steps[k..k + 1]).ok()?;
        if !eq {
            return None;
        }
        terms.push(u);
    }
    let mut out = vec![];
    for k in (0..steps.len()).rev() {
        let before = &terms[k];
        out.push(match &steps[k] {
            Step::Rw {
                rule, fwd, path, ..
            } => {
                let r = &rules[*rule];
                // the new replacing side is the old matched side
                let (old_src, old_dst) = if *fwd {
                    (&r.lhs, &r.rhs)
                } else {
                    (&r.rhs, &r.lhs)
                };
                let mut s = vec![];
                if !pmatch(locals, old_src, before.get(path)?, &mut s) {
                    return None;
                }
                let mut dv = vec![];
                old_dst.all_vars(&mut dv);
                Step::Rw {
                    rule: *rule,
                    fwd: !*fwd,
                    path: path.clone(),
                    extra: s.into_iter().filter(|(n, _)| !dv.contains(n)).collect(),
                }
            }
            Step::Fold { path } => Step::Unfold {
                path: path.clone(),
                b: before.get(path)?.clone(),
            },
            Step::Unfold { path, .. } => Step::Fold { path: path.clone() },
            Step::Comp { path } => Step::Uncomp {
                path: path.clone(),
                b: before.get(path)?.clone(),
            },
            Step::Uncomp { path, .. } => Step::Comp { path: path.clone() },
            Step::Comp2 { path } => Step::Uncomp2 {
                path: path.clone(),
                b: before.get(path)?.clone(),
            },
            Step::Uncomp2 { path, .. } => Step::Comp2 { path: path.clone() },
        });
    }
    match replay(locals, rules, terms.last().unwrap(), &out) {
        Ok((u, true)) if &u == t => Some(out),
        _ => None,
    }
}

/// Minimise a certificate: replay it and cut out every detour (a stretch of steps that
/// returns to a term already visited), keeping the result and the equation flag. Returns
/// the shorter chain; on a replay failure, the input unchanged.
pub fn minimise(locals: &[Ty], rules: &[Rule], t: &Term, steps: &[Step]) -> Vec<Step> {
    let mut cur: Vec<Step> = steps.to_vec();
    loop {
        // the terms before each step, and after the last
        let mut terms = vec![t.clone()];
        for k in 0..cur.len() {
            match replay(locals, rules, terms.last().unwrap(), &cur[k..k + 1]) {
                Ok((u, _)) => terms.push(u),
                Err(_) => return steps.to_vec(),
            }
        }
        // the first term that occurs again later: cut from its first to its last occurrence
        let mut cut = None;
        'outer: for i in 0..terms.len() {
            for j in (i + 1..terms.len()).rev() {
                if terms[i] == terms[j] {
                    cut = Some((i, j));
                    break 'outer;
                }
            }
        }
        match cut {
            Some((i, j)) => {
                cur.drain(i..j);
            }
            None => return cur,
        }
    }
}

/// Lean's `Term.comp?` on an operator and its constant right operand.
fn comp(t: Ty, op: BinOp, n: u64) -> Option<(BinOp, u64)> {
    let w = t.width() as u64;
    let pow2 = (n != 0 && n.is_power_of_two() && (n.trailing_zeros() as u64) < w)
        .then(|| n.trailing_zeros() as u64);
    match op {
        BinOp::Mul => pow2.map(|k| (BinOp::Shl, k)),
        BinOp::DivU => pow2.map(|k| (BinOp::ShrU, k)),
        BinOp::RemU => pow2.map(|_| (BinOp::And, n - 1)),
        BinOp::Shl | BinOp::ShrS | BinOp::ShrU | BinOp::Rotl | BinOp::Rotr => {
            (n >= w).then(|| (op, n % w))
        }
        _ => None,
    }
}

/// `k` with `2^k = n` and `k < bound` (Lean's `pow2Exp? bound n`).
fn pow2_below(bound: u32, n: u64) -> Option<u32> {
    (n != 0 && n.is_power_of_two() && n.trailing_zeros() < bound).then(|| n.trailing_zeros())
}

fn cnst(t: Ty, n: u64) -> Term {
    Term::leaf(Op::Const(t, n))
}

fn bin(t: Ty, op: BinOp, a: Term, b: Term) -> Term {
    Term {
        op: Op::Bin(t, op),
        ch: vec![a, b],
    }
}

/// Lean's `Silmaril.Wasm.Auto.ESeg.comp2?`: shifts of shifts, unsigned comparisons with `0` and
/// `1`, the `i32` sign test, `eqz` of a signed remainder by `2^k`, signed division by `2^k`.
pub fn comp2_term(t: &Term) -> Option<Term> {
    use crate::term::RelOp;
    // odd masks of booleans (Lean's `boolMask?`, tried first)
    if t.op == Op::Bin(Ty::I32, BinOp::And) {
        let is_bool = |b: &Term| matches!(b.op, Op::Test(_) | Op::Rel(..));
        for (k, b) in [(0, 1), (1, 0)] {
            if let Op::Const(Ty::I32, c) = t.ch[k].op
                && c % 2 == 1
                && is_bool(&t.ch[b])
            {
                return Some(t.ch[b].clone());
            }
        }
    }
    match &t.op {
        Op::Bin(ty, op) => {
            let Op::Const(ct, n) = t.ch[1].op else {
                return None;
            };
            if ct != *ty {
                return None;
            }
            let w = ty.width() as u64;
            match op {
                BinOp::Shl | BinOp::ShrU | BinOp::ShrS => {
                    let inner = &t.ch[0];
                    let Op::Bin(t2, op2) = inner.op else {
                        return None;
                    };
                    let Op::Const(c1, m) = inner.ch[1].op else {
                        return None;
                    };
                    (t2 == *ty && op2 == *op && c1 == *ty && m < w && n < w && m + n < w)
                        .then(|| bin(*ty, *op, inner.ch[0].clone(), cnst(*ty, m + n)))
                }
                BinOp::DivS => {
                    let k = pow2_below(ty.width() - 1, n)? as u64;
                    if k == 0 {
                        return None;
                    }
                    let a = t.ch[0].clone();
                    let sign = bin(*ty, BinOp::ShrS, a.clone(), cnst(*ty, w - 1));
                    let bias = bin(*ty, BinOp::ShrU, sign, cnst(*ty, w - k));
                    Some(bin(
                        *ty,
                        BinOp::ShrS,
                        bin(*ty, BinOp::Add, a, bias),
                        cnst(*ty, k),
                    ))
                }
                _ => None,
            }
        }
        Op::Rel(ty, op) => {
            let Op::Const(ct, n) = t.ch[1].op else {
                return None;
            };
            if ct != *ty {
                return None;
            }
            let a = t.ch[0].clone();
            let test = || Term {
                op: Op::Test(*ty),
                ch: vec![a.clone()],
            };
            let ne0 = || Term {
                op: Op::Rel(*ty, RelOp::Ne),
                ch: vec![a.clone(), cnst(*ty, 0)],
            };
            match (op, n) {
                (RelOp::LtU, 1) | (RelOp::LeU, 0) => Some(test()),
                (RelOp::GtU, 0) | (RelOp::GeU, 1) => Some(ne0()),
                (RelOp::LtS, 0) if *ty == Ty::I32 => {
                    Some(bin(Ty::I32, BinOp::ShrU, a.clone(), cnst(Ty::I32, 31)))
                }
                _ => None,
            }
        }
        Op::Test(ty) => {
            let inner = &t.ch[0];
            let Op::Bin(t2, BinOp::RemS) = inner.op else {
                return None;
            };
            let Op::Const(ct, n) = inner.ch[1].op else {
                return None;
            };
            if t2 != *ty || ct != *ty {
                return None;
            }
            pow2_below(ty.width() - 1, n)?;
            Some(Term {
                op: Op::Test(*ty),
                ch: vec![bin(*ty, BinOp::And, inner.ch[0].clone(), cnst(*ty, n - 1))],
            })
        }
        _ => None,
    }
}

fn comp_term(t: &Term) -> Option<Term> {
    let Op::Bin(ty, op) = t.op else { return None };
    let Op::Const(ct, n) = t.ch[1].op else {
        return None;
    };
    if ct != ty {
        return None;
    }
    let (op2, n2) = comp(ty, op, n)?;
    Some(Term {
        op: Op::Bin(ty, op2),
        ch: vec![t.ch[0].clone(), Term::leaf(Op::Const(ty, n2))],
    })
}

fn fold_term(t: &Term) -> Option<Term> {
    let operand_ty = match &t.op {
        Op::Un(ty, _) | Op::Test(ty) | Op::Bin(ty, _) | Op::Rel(ty, _) => *ty,
        _ => return None,
    };
    let mut vals = vec![];
    for c in &t.ch {
        match c.op {
            Op::Const(ct, v) if ct == operand_ty => vals.push(v),
            _ => return None,
        }
    }
    let (rt, v) = fold(&t.op, &vals)?;
    Some(Term::leaf(Op::Const(rt, v)))
}

fn pmatch(locals: &[Ty], p: &Pat, t: &Term, s: &mut Vec<(u32, Term)>) -> bool {
    match p {
        Pat::Var(ty, n) | Pat::TVar(ty, n) => {
            if t.type_of(locals) != Some(*ty) || (matches!(p, Pat::TVar(..)) && !no_trap(t)) {
                return false;
            }
            match s.iter().find(|(m, _)| m == n) {
                Some((_, e)) => e == t,
                None => {
                    s.push((*n, t.clone()));
                    true
                }
            }
        }
        Pat::Node(op, pch) => {
            &t.op == op
                && pch.len() == t.ch.len()
                && pch
                    .iter()
                    .zip(&t.ch)
                    .all(|(pc, tc)| pmatch(locals, pc, tc, s))
        }
    }
}

fn no_trap(t: &Term) -> bool {
    !matches!(
        t.op,
        Op::Bin(_, BinOp::DivS | BinOp::DivU | BinOp::RemS | BinOp::RemU)
    ) && t.ch.iter().all(no_trap)
}

fn pinst(p: &Pat, s: &[(u32, Term)]) -> Option<Term> {
    match p {
        Pat::Var(_, n) | Pat::TVar(_, n) => s.iter().find(|(m, _)| m == n).map(|(_, e)| e.clone()),
        Pat::Node(op, pch) => {
            let ch = pch
                .iter()
                .map(|c| pinst(c, s))
                .collect::<Option<Vec<_>>>()?;
            Some(Term { op: op.clone(), ch })
        }
    }
}
