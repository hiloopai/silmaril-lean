//! C11 litmus specifications (`examples/litmus-c/<shape>/litmus.txt`).
//!
//! A specification names the C source, its shared and result locations, each thread's
//! function and its C-level accesses (with the mode left to the variant), the final
//! condition, and the C11 verdicts expected from the literature. Format, one item per line,
//! `#` comments:
//!
//! ```text
//! name SB
//! source sb.c
//! loc x                 shared int, initially 0
//! result r0             int written once by one thread, read after join
//! thread P0             the next lines are P0's accesses, in program order
//! st x 1                store 1 to x
//! ld y r0               load y, keep the value in r0 (a plain store to r0)
//! faa x 1 [r1]          fetch_add(x, 1), optionally keeping the old value in r1
//! fence                 __atomic_thread_fence(__ATOMIC_SEQ_CST)
//! exists r0=0 /\ r1=0   final condition on locations (a conjunction)
//! c11 sc forbidden RC11 store buffering with seq_cst ...   expected verdict + note
//! ```
//!
//! The variant fixes the C11 mode of every access ([`Variant::modes`]): `na` plain, `rlx`
//! relaxed, `ra` release stores / acquire loads / acq_rel RMWs, `sc` seq_cst. Fences are
//! always seq_cst. A `faa` in the `na` variant is a plain load and a plain store (the C macro
//! is `o = *p; *p = o + v`).

use crate::litmus::{Error, parse_int};

/// A C11 memory order, or `na` for a plain access.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Na,
    Rlx,
    Acq,
    Rel,
    AcqRel,
    Sc,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::Na => "na",
            Mode::Rlx => "rlx",
            Mode::Acq => "acq",
            Mode::Rel => "rel",
            Mode::AcqRel => "acq_rel",
            Mode::Sc => "sc",
        }
    }
}

/// A compilation variant (`-DMODE=n` in `examples/litmus-c/c11.h`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Variant {
    Na,
    Rlx,
    Ra,
    Sc,
}

/// All variants, in `MODE` order.
pub const VARIANTS: [Variant; 4] = [Variant::Na, Variant::Rlx, Variant::Ra, Variant::Sc];

impl Variant {
    pub fn name(self) -> &'static str {
        match self {
            Variant::Na => "na",
            Variant::Rlx => "rlx",
            Variant::Ra => "ra",
            Variant::Sc => "sc",
        }
    }
    /// The `MODE` macro value.
    pub fn macro_value(self) -> u8 {
        self as u8
    }
    pub fn parse(s: &str) -> Option<Variant> {
        VARIANTS.into_iter().find(|v| v.name() == s)
    }
    /// The modes of (store, load, RMW).
    pub fn modes(self) -> (Mode, Mode, Mode) {
        match self {
            Variant::Na => (Mode::Na, Mode::Na, Mode::Na),
            Variant::Rlx => (Mode::Rlx, Mode::Rlx, Mode::Rlx),
            Variant::Ra => (Mode::Rel, Mode::Acq, Mode::AcqRel),
            Variant::Sc => (Mode::Sc, Mode::Sc, Mode::Sc),
        }
    }
}

/// A C-level operation of the specification (mode not yet fixed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum COp {
    St {
        loc: String,
        val: i64,
    },
    Ld {
        loc: String,
        res: String,
    },
    Faa {
        loc: String,
        val: i64,
        res: Option<String>,
    },
    Fence,
}

/// The kind of a C11 access.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AKind {
    Load,
    Store,
    Rmw,
    Fence,
}

impl AKind {
    pub fn name(self) -> &'static str {
        match self {
            AKind::Load => "ld",
            AKind::Store => "st",
            AKind::Rmw => "rmw",
            AKind::Fence => "fence",
        }
    }
}

/// One C11 access of a thread, in program order, with its mode fixed by the variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Access {
    pub kind: AKind,
    /// The location (`None` for fences).
    pub loc: Option<String>,
    pub mode: Mode,
    /// The stored value or RMW operand, when it is a constant.
    pub value: Option<i64>,
    /// For stores: a symbolic description of a stored value that is not a constant
    /// (`"ld#2"`: the value read by access 2; `"ld#2+1"`).
    pub value_of: Option<String>,
    /// For `fetch_add`: the operation.
    pub rmw_op: Option<&'static str>,
    /// `true` for the plain store of a result location (thread-private until join).
    pub result: bool,
}

/// The role of a location.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Shared,
    Result,
}

/// A parsed specification.
#[derive(Clone, Debug)]
pub struct Spec {
    pub name: String,
    pub source: String,
    pub locs: Vec<(String, Role)>,
    /// Per thread: function name and operations.
    pub threads: Vec<(String, Vec<COp>)>,
    /// Final condition: a conjunction of `loc = value`.
    pub exists: Vec<(String, u64)>,
    /// Expected C11 verdicts: (variant, verdict word, note).
    pub c11: Vec<(Variant, String, String)>,
}

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

impl Spec {
    /// Parse a specification.
    pub fn parse(src: &str) -> Result<Spec, Error> {
        let mut s = Spec {
            name: String::new(),
            source: String::new(),
            locs: Vec::new(),
            threads: Vec::new(),
            exists: Vec::new(),
            c11: Vec::new(),
        };
        for (n, line) in src.lines().enumerate() {
            let l = line.split('#').next().unwrap_or("").trim();
            if l.is_empty() {
                continue;
            }
            let ctx = |m: &str| Error(format!("line {}: {m}", n + 1));
            let w: Vec<&str> = l.split_whitespace().collect();
            let known = |s: &Spec, x: &str| s.locs.iter().any(|(m, _)| m == x);
            match w.as_slice() {
                ["name", v] => s.name = v.to_string(),
                ["source", v] => s.source = v.to_string(),
                ["loc", v] => s.locs.push((v.to_string(), Role::Shared)),
                ["result", v] => s.locs.push((v.to_string(), Role::Result)),
                ["thread", f] => s.threads.push((f.to_string(), Vec::new())),
                ["exists", rest @ ..] => {
                    for atom in rest.join(" ").split("/\\") {
                        let (a, b) = atom.split_once('=').ok_or_else(|| ctx("bad exists atom"))?;
                        let (a, b) = (a.trim(), b.trim());
                        if !known(&s, a) {
                            return Err(ctx(&format!("unknown location `{a}`")));
                        }
                        s.exists.push((a.to_string(), parse_int(b)? as u64));
                    }
                }
                ["c11", v, verdict, note @ ..] => {
                    let v = Variant::parse(v).ok_or_else(|| ctx("bad variant"))?;
                    if !["allowed", "forbidden", "racy"].contains(verdict) {
                        return Err(ctx("c11 verdict must be allowed, forbidden or racy"));
                    }
                    s.c11.push((v, verdict.to_string(), note.join(" ")));
                }
                [op, args @ ..] => {
                    let shared = |x: &str| s.locs.iter().any(|(m, r)| m == x && *r == Role::Shared);
                    let result = |x: &str| s.locs.iter().any(|(m, r)| m == x && *r == Role::Result);
                    let c = match (*op, args) {
                        ("st", [x, v]) if shared(x) => COp::St {
                            loc: x.to_string(),
                            val: parse_int(v)? as i64,
                        },
                        ("ld", [x, r]) if shared(x) && result(r) => COp::Ld {
                            loc: x.to_string(),
                            res: r.to_string(),
                        },
                        ("faa", [x, v]) if shared(x) => COp::Faa {
                            loc: x.to_string(),
                            val: parse_int(v)? as i64,
                            res: None,
                        },
                        ("faa", [x, v, r]) if shared(x) && result(r) => COp::Faa {
                            loc: x.to_string(),
                            val: parse_int(v)? as i64,
                            res: Some(r.to_string()),
                        },
                        ("fence", []) => COp::Fence,
                        _ => return Err(ctx(&format!("bad line `{l}`"))),
                    };
                    let Some((_, ops)) = s.threads.last_mut() else {
                        return Err(ctx("access before the first `thread`"));
                    };
                    ops.push(c);
                }
                [] => {}
            }
        }
        if s.name.is_empty() || s.source.is_empty() || s.threads.is_empty() {
            return err("specification needs name, source and at least one thread");
        }
        for (v, _, _) in &s.c11 {
            if s.c11.iter().filter(|(w, _, _)| w == v).count() > 1 {
                return err(format!("two c11 verdicts for variant {}", v.name()));
            }
        }
        Ok(s)
    }

    /// The C11 accesses of thread `t` under a variant, in program order.
    pub fn accesses(&self, t: usize, v: Variant) -> Vec<Access> {
        let (mst, mld, mrmw) = v.modes();
        let mut out: Vec<Access> = Vec::new();
        let acc = |kind, loc: &str, mode, value: Option<i64>, value_of: Option<String>| Access {
            kind,
            loc: Some(loc.to_string()),
            mode,
            value,
            value_of,
            rmw_op: None,
            result: false,
        };
        for op in &self.threads[t].1 {
            match op {
                COp::St { loc, val } => out.push(acc(AKind::Store, loc, mst, Some(*val), None)),
                COp::Ld { loc, res } => {
                    out.push(acc(AKind::Load, loc, mld, None, None));
                    let k = out.len() - 1;
                    let mut r = acc(AKind::Store, res, Mode::Na, None, Some(format!("ld#{k}")));
                    r.result = true;
                    out.push(r);
                }
                COp::Faa { loc, val, res } => {
                    let k = if v == Variant::Na {
                        out.push(acc(AKind::Load, loc, Mode::Na, None, None));
                        let k = out.len() - 1;
                        out.push(acc(
                            AKind::Store,
                            loc,
                            Mode::Na,
                            None,
                            Some(format!("ld#{k}+{val}")),
                        ));
                        k
                    } else {
                        let mut a = acc(AKind::Rmw, loc, mrmw, Some(*val), None);
                        a.rmw_op = Some("fetch_add");
                        out.push(a);
                        out.len() - 1
                    };
                    if let Some(res) = res {
                        let mut r = acc(AKind::Store, res, Mode::Na, None, Some(format!("ld#{k}")));
                        r.result = true;
                        out.push(r);
                    }
                }
                COp::Fence => out.push(Access {
                    kind: AKind::Fence,
                    loc: None,
                    mode: Mode::Sc,
                    value: None,
                    value_of: None,
                    rmw_op: None,
                    result: false,
                }),
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SB: &str = "name SB\nsource sb.c\nloc x\nloc y\nresult r0\nresult r1\nthread P0\nst x 1\nld y r0\nthread P1\nst y 1 # c\nfence\nfaa x 1 r1\nexists r0=0 /\\ r1=0\nc11 sc forbidden note here\n";

    #[test]
    fn parse_and_expand() {
        let s = Spec::parse(SB).unwrap();
        assert_eq!(s.threads.len(), 2);
        assert_eq!(s.exists, vec![("r0".into(), 0), ("r1".into(), 0)]);
        assert_eq!(s.c11[0].2, "note here");
        let a = s.accesses(0, Variant::Ra);
        assert_eq!(a.len(), 3);
        assert_eq!((a[0].kind, a[0].mode), (AKind::Store, Mode::Rel));
        assert_eq!((a[1].kind, a[1].mode), (AKind::Load, Mode::Acq));
        assert!(a[2].result && a[2].value_of.as_deref() == Some("ld#1"));
        let b = s.accesses(1, Variant::Na);
        let k: Vec<AKind> = b.iter().map(|a| a.kind).collect();
        assert_eq!(
            k,
            vec![
                AKind::Store,
                AKind::Fence,
                AKind::Load,
                AKind::Store,
                AKind::Store
            ]
        );
        assert_eq!(b[1].mode, Mode::Sc);
        assert_eq!(s.accesses(1, Variant::Sc)[2].kind, AKind::Rmw);
    }

    #[test]
    fn rejects() {
        assert!(Spec::parse("name a\nsource a.c\nloc x\nthread P0\nld x x\n").is_err());
        assert!(Spec::parse("name a\nsource a.c\nloc x\nst x 1\n").is_err());
        assert!(Spec::parse("name a\nsource a.c\nloc x\nthread P0\nexists q=1\n").is_err());
    }
}
