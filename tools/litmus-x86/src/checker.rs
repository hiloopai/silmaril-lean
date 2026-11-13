//! An exhaustive axiomatic checker for SC and x86-TSO over candidate executions.
//!
//! The TSO axioms are a transcription of herdtools7's `herd/libdir/x86tso.cat` (pinned copy in
//! `corpus/herdtools7/herd/libdir/x86tso.cat`):
//!
//! ```text
//! acyclic po-loc | rf | fr | co                         (uniproc; amo is empty on x86)
//! empty rmw & (fre; coe)                               (atomicity)
//! acyclic mfence | implied | po_ghb | rfe | fr | co    (tso)
//!   po_ghb  = WW(po) | RM(po)
//!   implied = W→R program order where either end is a locked (atomic) access
//! ```
//!
//! SC is `acyclic po | rf | fr | co` plus the same atomicity axiom.
//!
//! Scope: only tests whose every access covers a whole location of at most 8 bytes (so the
//! location granularity of the events is exact), and whose instructions are plain moves,
//! fences, `xchg`, `[lock] xadd/cmpxchg/inc/dec/add/or/and/sub/xor`. `movnti`, `rep stosb`,
//! partial or mixed-size accesses are rejected (`NotCovered`): those are XL-only tests.
//!
//! This is an independent re-implementation used to cross-check recorded verdicts; it is not
//! herd7 and it is not proved.

use crate::insn::{EvKind, Fence, Insn, Reg, Src};
use crate::model::{Atom, Cond, Model};

/// A memory model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mm {
    Sc,
    Tso,
}

/// The verdict of a test's witness under a model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Allowed,
    Forbidden,
}

impl Verdict {
    /// Lower-case name, as in the corpus index.
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Allowed => "allowed",
            Verdict::Forbidden => "forbidden",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    R,
    W,
    MFence,
}

#[derive(Clone, Debug)]
struct Ev {
    thread: usize,
    /// Position in the thread's event sequence (program order).
    seq: usize,
    kind: Kind,
    loc: usize,
    atomic: bool,
    insn: usize,
}

/// A final state: per-thread registers and per-location values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Final {
    pub regs: Vec<[u64; 16]>,
    pub mem: Vec<u64>,
}

/// The result of a check.
#[derive(Clone, Debug)]
pub struct Outcome {
    pub verdict: Verdict,
    /// Distinct final states of consistent executions.
    pub finals: usize,
    /// Number of consistent executions.
    pub executions: usize,
    /// The distinct final states themselves (the model-allowed outcome set; exported to
    /// JSON for the hardware harness by `export`).
    pub states: std::collections::BTreeSet<Final>,
}

fn mask(size: u64) -> u64 {
    if size >= 8 {
        u64::MAX
    } else {
        (1u64 << (8 * size)) - 1
    }
}

fn read_reg(regs: &[u64; 16], r: Reg) -> u64 {
    regs[r.num as usize] & mask(r.size)
}

fn write_reg(regs: &mut [u64; 16], r: Reg, v: u64) {
    let i = r.num as usize;
    regs[i] = match r.size {
        8 => v,
        4 => v & 0xffff_ffff,
        s => (regs[i] & !mask(s)) | (v & mask(s)),
    };
}

struct Prepared {
    evs: Vec<Ev>,
    /// Per thread, per instruction: indices of its events.
    by_insn: Vec<Vec<Vec<usize>>>,
    locs: usize,
}

/// Why a test is outside the checker's scope.
#[derive(Debug, PartialEq, Eq)]
pub struct NotCovered(pub String);

fn prepare(m: &Model) -> Result<Prepared, NotCovered> {
    let mut evs = Vec::new();
    let mut by_insn = Vec::new();
    let addrs = m.addrs();
    for (t, (insns, _)) in m.threads.iter().enumerate() {
        let mut seq = 0;
        let mut per = Vec::new();
        for (k, ins) in insns.iter().enumerate() {
            let mut here = Vec::new();
            // The checker's events are exactly `Insn::events`, the list the Lean corpus proves
            // equal to the events of the assembled bytes (`Corpus.events_match`).
            let mevs = ins
                .events(&addrs)
                .map_err(|e| NotCovered(e.0))?
                .ok_or_else(|| NotCovered(format!("no MemEvent form: {ins:?}")))?;
            let mut kinds: Vec<(Kind, bool, usize)> = Vec::new();
            for ev in mevs {
                let loc = || -> Result<usize, NotCovered> {
                    m.locs
                        .iter()
                        .position(|l| l.addr == ev.addr && l.size == ev.size && l.size <= 8)
                        .ok_or_else(|| {
                            NotCovered(format!(
                                "partial, mixed-size or wide access at 0x{:x} ({} bytes)",
                                ev.addr, ev.size
                            ))
                        })
                };
                match ev.kind {
                    EvKind::Fence(Fence::M) => kinds.push((Kind::MFence, false, 0)),
                    EvKind::Fence(_) => {}
                    EvKind::Load => kinds.push((Kind::R, ev.locked, loc()?)),
                    EvKind::Store => kinds.push((Kind::W, ev.locked, loc()?)),
                    EvKind::Rmw => {
                        let l = loc()?;
                        kinds.push((Kind::R, ev.locked, l));
                        kinds.push((Kind::W, ev.locked, l));
                    }
                }
            }
            for (kind, atomic, loc) in kinds {
                here.push(evs.len());
                evs.push(Ev {
                    thread: t,
                    seq,
                    kind,
                    loc,
                    atomic,
                    insn: k,
                });
                seq += 1;
            }
            per.push(here);
        }
        by_insn.push(per);
    }
    Ok(Prepared {
        evs,
        by_insn,
        locs: m.locs.len(),
    })
}

/// Final registers per thread and the value of each write event.
type Evaluated = (Vec<[u64; 16]>, Vec<Option<u64>>);

/// Run the threads given a reads-from choice; `None` if values depend cyclically.
fn evaluate(m: &Model, p: &Prepared, rf: &[Option<usize>]) -> Option<Evaluated> {
    let n = p.evs.len();
    let mut wval: Vec<Option<u64>> = vec![None; n];
    let mut regs: Vec<[u64; 16]> = m
        .threads
        .iter()
        .map(|(_, init)| {
            let mut r = [0u64; 16];
            for (k, v) in init {
                r[*k as usize] = *v;
            }
            r
        })
        .collect();
    let mut pc = vec![0usize; m.threads.len()];
    loop {
        let mut progress = false;
        let mut done = true;
        for t in 0..m.threads.len() {
            let insns = &m.threads[t].0;
            while pc[t] < insns.len() {
                let es = &p.by_insn[t][pc[t]];
                let rd = es.iter().copied().find(|&e| p.evs[e].kind == Kind::R);
                let wr = es.iter().copied().find(|&e| p.evs[e].kind == Kind::W);
                let old = match rd {
                    Some(r) => match rf[r] {
                        None => m.locs[p.evs[r].loc].init as u64,
                        Some(w) => match wval[w] {
                            Some(v) => v,
                            None => break,
                        },
                    },
                    None => 0,
                };
                let ins = &insns[pc[t]];
                let size = ins.mem_size();
                let rg = &mut regs[t];
                let new = match ins {
                    Insn::MovRI { dst, imm } => {
                        write_reg(rg, *dst, *imm as u64);
                        None
                    }
                    Insn::MovRR { dst, src } => {
                        let v = read_reg(rg, *src);
                        write_reg(rg, *dst, v);
                        None
                    }
                    Insn::Load { dst, .. } => {
                        write_reg(rg, *dst, old);
                        None
                    }
                    Insn::Lea { dst, base, disp } => {
                        let v = rg[base.num as usize].wrapping_add(*disp as u64);
                        write_reg(rg, *dst, v);
                        None
                    }
                    Insn::Store { src, .. } => Some(match src {
                        Src::Imm(i) => *i as u64,
                        Src::Reg(r) => read_reg(rg, *r),
                    }),
                    Insn::Fence(_) => None,
                    Insn::Xchg { reg, .. } => {
                        let v = read_reg(rg, *reg);
                        write_reg(rg, *reg, old);
                        Some(v)
                    }
                    Insn::Xadd { reg, .. } => {
                        let v = read_reg(rg, *reg);
                        write_reg(rg, *reg, old);
                        Some(old.wrapping_add(v))
                    }
                    Insn::Cmpxchg { reg, .. } => {
                        let acc = Reg {
                            num: 0,
                            size: reg.size,
                        };
                        if read_reg(rg, acc) == old {
                            Some(read_reg(rg, *reg))
                        } else {
                            write_reg(rg, acc, old);
                            Some(old)
                        }
                    }
                    Insn::AluMI { op, imm, .. } => Some(op.apply(old, *imm as u64)),
                    Insn::IncDec { dec, .. } => Some(if *dec {
                        old.wrapping_sub(1)
                    } else {
                        old.wrapping_add(1)
                    }),
                    Insn::Movnti { .. } | Insn::RepStosb => return None,
                };
                if let (Some(w), Some(v)) = (wr, new) {
                    wval[w] = Some(v & mask(size));
                }
                pc[t] += 1;
                progress = true;
            }
            if pc[t] < insns.len() {
                done = false;
            }
        }
        if done {
            return Some((regs, wval));
        }
        if !progress {
            return None;
        }
    }
}

fn acyclic(n: usize, edges: &[(usize, usize)]) -> bool {
    let mut adj = vec![Vec::new(); n];
    let mut indeg = vec![0usize; n];
    for &(a, b) in edges {
        adj[a].push(b);
        indeg[b] += 1;
    }
    let mut stack: Vec<usize> = (0..n).filter(|&i| indeg[i] == 0).collect();
    let mut seen = 0;
    while let Some(v) = stack.pop() {
        seen += 1;
        for &w in &adj[v] {
            indeg[w] -= 1;
            if indeg[w] == 0 {
                stack.push(w);
            }
        }
    }
    seen == n
}

fn eval_cond(m: &Model, c: &Cond, f: &Final) -> bool {
    match c {
        Cond::True => true,
        Cond::Not(a) => !eval_cond(m, a, f),
        Cond::And(a, b) => eval_cond(m, a, f) && eval_cond(m, b, f),
        Cond::Or(a, b) => eval_cond(m, a, f) || eval_cond(m, b, f),
        Cond::Atom(Atom::Reg {
            thread,
            reg,
            bits,
            value,
        }) => {
            let v = f.regs[*thread][*reg as usize];
            let mk = if *bits >= 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            };
            v & mk == *value
        }
        Cond::Atom(Atom::Mem { addr, size, value }) => {
            match m.locs.iter().position(|l| l.addr == *addr) {
                Some(i) if m.locs[i].size == *size => f.mem[i] as u128 == *value,
                _ => false,
            }
        }
    }
}

fn permutations(v: &[usize]) -> Vec<Vec<usize>> {
    if v.len() <= 1 {
        return vec![v.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..v.len() {
        let mut rest = v.to_vec();
        let x = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, x);
            out.push(p);
        }
    }
    out
}

/// Check a test's witness under a memory model.
pub fn check(m: &Model, mm: Mm) -> Result<Outcome, NotCovered> {
    let p = prepare(m)?;
    let n = p.evs.len();
    let reads: Vec<usize> = (0..n).filter(|&e| p.evs[e].kind == Kind::R).collect();
    let writes_of = |l: usize| -> Vec<usize> {
        (0..n)
            .filter(|&e| p.evs[e].kind == Kind::W && p.evs[e].loc == l)
            .collect()
    };
    let rf_choices: Vec<Vec<Option<usize>>> = reads
        .iter()
        .map(|&r| {
            let mut c = vec![None];
            for w in writes_of(p.evs[r].loc) {
                let same_insn =
                    p.evs[w].thread == p.evs[r].thread && p.evs[w].insn == p.evs[r].insn;
                if !same_insn {
                    c.push(Some(w));
                }
            }
            c
        })
        .collect();
    let co_choices: Vec<Vec<Vec<usize>>> =
        (0..p.locs).map(|l| permutations(&writes_of(l))).collect();
    let witness = m.witness();
    let mut finals = std::collections::BTreeSet::new();
    let mut executions = 0usize;
    let mut allowed = false;
    let po = |a: usize, b: usize| p.evs[a].thread == p.evs[b].thread && p.evs[a].seq < p.evs[b].seq;
    // rmw pairs.
    let rmw: Vec<(usize, usize)> = (0..n)
        .filter(|&r| p.evs[r].kind == Kind::R && p.evs[r].atomic)
        .filter_map(|r| {
            (0..n)
                .find(|&w| {
                    p.evs[w].kind == Kind::W
                        && p.evs[w].thread == p.evs[r].thread
                        && p.evs[w].insn == p.evs[r].insn
                })
                .map(|w| (r, w))
        })
        .collect();
    let mut rf_idx = vec![0usize; reads.len()];
    loop {
        let mut rf: Vec<Option<usize>> = vec![None; n];
        for (k, &r) in reads.iter().enumerate() {
            rf[r] = rf_choices[k][rf_idx[k]];
        }
        if let Some((regs, wval)) = evaluate(m, &p, &rf) {
            let mut co_idx = vec![0usize; p.locs];
            loop {
                // co position per write.
                let mut copos = vec![usize::MAX; n];
                for l in 0..p.locs {
                    for (i, &w) in co_choices[l][co_idx[l]].iter().enumerate() {
                        copos[w] = i;
                    }
                }
                let co = |a: usize, b: usize| {
                    p.evs[a].kind == Kind::W
                        && p.evs[b].kind == Kind::W
                        && p.evs[a].loc == p.evs[b].loc
                        && copos[a] < copos[b]
                };
                let fr = |r: usize, w: usize| {
                    p.evs[r].kind == Kind::R
                        && p.evs[w].kind == Kind::W
                        && p.evs[r].loc == p.evs[w].loc
                        && match rf[r] {
                            None => true,
                            Some(src) => copos[src] < copos[w],
                        }
                };
                let mem = |e: usize| p.evs[e].kind != Kind::MFence;
                let mut com = Vec::new();
                for a in 0..n {
                    for (b, src) in rf.iter().enumerate() {
                        if a == b {
                            continue;
                        }
                        if *src == Some(a) || co(a, b) || fr(a, b) {
                            com.push((a, b));
                        }
                    }
                }
                let atomic_ok = rmw.iter().all(|&(r, w)| {
                    !(0..n).any(|w2| {
                        fr(r, w2)
                            && p.evs[w2].thread != p.evs[r].thread
                            && co(w2, w)
                            && p.evs[w2].thread != p.evs[w].thread
                    })
                });
                let ok = atomic_ok
                    && match mm {
                        Mm::Sc => {
                            let mut e = com.clone();
                            for a in 0..n {
                                for b in 0..n {
                                    if mem(a) && mem(b) && po(a, b) {
                                        e.push((a, b));
                                    }
                                }
                            }
                            acyclic(n, &e)
                        }
                        Mm::Tso => {
                            let mut uni = com.clone();
                            for a in 0..n {
                                for b in 0..n {
                                    if mem(a) && mem(b) && po(a, b) && p.evs[a].loc == p.evs[b].loc
                                    {
                                        uni.push((a, b));
                                    }
                                }
                            }
                            let mut ghb: Vec<(usize, usize)> = com
                                .iter()
                                .copied()
                                .filter(|&(a, b)| {
                                    !(rf[b] == Some(a) && p.evs[a].thread == p.evs[b].thread)
                                })
                                .collect();
                            for a in 0..n {
                                for b in 0..n {
                                    if !(mem(a) && mem(b) && po(a, b)) {
                                        continue;
                                    }
                                    let (ka, kb) = (p.evs[a].kind, p.evs[b].kind);
                                    let wr = ka == Kind::W && kb == Kind::R;
                                    let fenced = (0..n).any(|f| {
                                        p.evs[f].kind == Kind::MFence && po(a, f) && po(f, b)
                                    });
                                    let implied = wr && (p.evs[a].atomic || p.evs[b].atomic);
                                    if !wr || fenced || implied {
                                        ghb.push((a, b));
                                    }
                                }
                            }
                            acyclic(n, &uni) && acyclic(n, &ghb)
                        }
                    };
                if ok {
                    executions += 1;
                    let mut memv: Vec<u64> = m.locs.iter().map(|l| l.init as u64).collect();
                    for l in 0..p.locs {
                        if let Some(&last) = co_choices[l][co_idx[l]].last() {
                            memv[l] = wval[last].unwrap_or(0);
                        }
                    }
                    let f = Final {
                        regs: regs.clone(),
                        mem: memv,
                    };
                    if eval_cond(m, &witness, &f) {
                        allowed = true;
                    }
                    finals.insert(f);
                }
                // next co
                let mut k = 0;
                while k < p.locs {
                    co_idx[k] += 1;
                    if co_idx[k] < co_choices[k].len() {
                        break;
                    }
                    co_idx[k] = 0;
                    k += 1;
                }
                if k == p.locs {
                    break;
                }
            }
        }
        let mut k = 0;
        while k < reads.len() {
            rf_idx[k] += 1;
            if rf_idx[k] < rf_choices[k].len() {
                break;
            }
            rf_idx[k] = 0;
            k += 1;
        }
        if k == reads.len() {
            break;
        }
    }
    Ok(Outcome {
        verdict: if allowed {
            Verdict::Allowed
        } else {
            Verdict::Forbidden
        },
        finals: finals.len(),
        executions,
        states: finals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::litmus;

    fn run(src: &str, mm: Mm) -> Verdict {
        let m = Model::resolve(&litmus::parse(src).unwrap()).unwrap();
        check(&m, mm).unwrap().verdict
    }

    const SB: &str = "X86 SB\n{}\n P0 | P1 ;\n MOV [x],$1 | MOV [y],$1 ;\n MOV EAX,[y] | MOV EAX,[x] ;\nexists (0:EAX=0 /\\ 1:EAX=0)\n";
    const SBF: &str = "X86 SB\n{}\n P0 | P1 ;\n MOV [x],$1 | MOV [y],$1 ;\n MFENCE | MFENCE ;\n MOV EAX,[y] | MOV EAX,[x] ;\nexists (0:EAX=0 /\\ 1:EAX=0)\n";

    #[test]
    fn sb() {
        assert_eq!(run(SB, Mm::Tso), Verdict::Allowed);
        assert_eq!(run(SB, Mm::Sc), Verdict::Forbidden);
        assert_eq!(run(SBF, Mm::Tso), Verdict::Forbidden);
    }

    #[test]
    fn n6_store_forwarding() {
        let src = "X86 n6\n{}\n P0 | P1 ;\n MOV [x],$1 | MOV [y],$2 ;\n MOV EAX,[x] | MOV [x],$2 ;\n MOV EBX,[y] | ;\nexists (0:EAX=1 /\\ 0:EBX=0 /\\ x=1)\n";
        assert_eq!(run(src, Mm::Tso), Verdict::Allowed);
        assert_eq!(run(src, Mm::Sc), Verdict::Forbidden);
    }

    #[test]
    fn rmw_atomicity_and_unlocked_inc() {
        let locked =
            "X86_64 T\n{ int x=0; }\n P0 | P1 ;\n lock incl (x) | movl $5,(x) ;\nexists (x=1)\n";
        let plain = "X86_64 T\n{ int x=0; }\n P0 | P1 ;\n incl (x) | movl $5,(x) ;\nexists (x=1)\n";
        assert_eq!(run(locked, Mm::Tso), Verdict::Forbidden);
        assert_eq!(run(plain, Mm::Tso), Verdict::Allowed);
        assert_eq!(run(plain, Mm::Sc), Verdict::Allowed);
    }

    #[test]
    fn cmpxchg_failure_writes_accumulator() {
        let src = "X86_64 T\n{ int x=3; 0:rcx=9; }\n P0 ;\n lock cmpxchgl %ecx,(x) ;\nforall (0:rax=3 /\\ x=3)\n";
        assert_eq!(run(src, Mm::Tso), Verdict::Forbidden);
    }

    #[test]
    fn loose_forms_are_not_covered() {
        let src = "X86_64 T\n{ int x; }\n P0 ;\n movnti %eax,(x) ;\nexists (x=0)\n";
        let m = Model::resolve(&litmus::parse(src).unwrap()).unwrap();
        assert!(check(&m, Mm::Tso).is_err());
        let src = "X86_64 T\n{ uint64_t x; }\n P0 ;\n movl $1,(x+4) ;\nexists (x=0)\n";
        let m = Model::resolve(&litmus::parse(src).unwrap()).unwrap();
        assert!(check(&m, Mm::Tso).is_err());
    }
}
