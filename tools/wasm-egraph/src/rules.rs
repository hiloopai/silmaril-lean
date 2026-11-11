//! The rewrite library, read from `rules.sexp` in the order of
//! `Silmaril.Wasm.Auto.Rules.library` (schema `k` at i32 is rule `2k`, at i64 `2k + 1`).

use crate::sexp::{self, Sexp};
use crate::term::{Op, OpName, Ty, parse_const};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Var(Ty, u32),
    /// A total variable: matches only terms without division or remainder.
    TVar(Ty, u32),
    Node(Op, Vec<Pat>),
}

impl Pat {
    #[cfg(test)]
    pub fn vars(&self, out: &mut Vec<(Ty, u32)>) {
        match self {
            Pat::Var(t, n) => out.push((*t, *n)),
            Pat::TVar(..) => {}
            Pat::Node(_, ch) => ch.iter().for_each(|c| c.vars(out)),
        }
    }

    /// The variable numbers of a pattern (total or not).
    pub fn all_vars(&self, out: &mut Vec<u32>) {
        match self {
            Pat::Var(_, n) | Pat::TVar(_, n) => out.push(*n),
            Pat::Node(_, ch) => ch.iter().for_each(|c| c.all_vars(out)),
        }
    }

    /// The text form shared with Lean's `Pat.sexp`.
    pub fn text(&self) -> String {
        match self {
            Pat::Var(_, n) => format!("?{n}"),
            Pat::TVar(_, n) => format!("?{n}!"),
            Pat::Node(Op::Const(t, n), _) => format!("({}.const {n})", t.name()),
            Pat::Node(op, ch) => {
                let mut s = format!("({}", op.wat());
                for c in ch {
                    s.push(' ');
                    s.push_str(&c.text());
                }
                s.push(')');
                s
            }
        }
    }

    fn parse(s: &Sexp, t: Ty) -> Result<Pat, String> {
        if let Some(a) = s.atom() {
            let n = a
                .strip_prefix('?')
                .ok_or_else(|| format!("bad pattern atom {a}"))?;
            if let Some(m) = n.strip_suffix('!') {
                return Ok(Pat::TVar(
                    t,
                    m.parse().map_err(|_| format!("bad variable {a}"))?,
                ));
            }
            return Ok(Pat::Var(
                t,
                n.parse().map_err(|_| format!("bad variable {a}"))?,
            ));
        }
        let items = s.list().ok_or("bad pattern")?;
        let head = items[0]
            .atom()
            .ok_or("bad pattern head")?
            .replace("T.", &format!("{}.", t.name()));
        match Op::parse_name(&head).ok_or_else(|| format!("unknown op {head}"))? {
            OpName::Lget => Err("patterns have no locals".into()),
            OpName::Const(ct) => {
                let v = items[1].atom().ok_or("bad constant")?;
                let n = match v {
                    "ones" => ct.mask(),
                    "width" => ct.width() as u64,
                    _ => parse_const(ct, v)?,
                };
                Ok(Pat::Node(Op::Const(ct, n), vec![]))
            }
            OpName::Op(op) => {
                let ch = items[1..]
                    .iter()
                    .map(|c| Pat::parse(c, t))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Pat::Node(op, ch))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub name: String,
    pub is_ref: bool,
    pub lhs: Pat,
    pub rhs: Pat,
}

impl Rule {
    /// One line of `wasm-egraph rules`, the same text as Lean's `Rule.sexp`.
    pub fn text(&self) -> String {
        format!(
            "{} {} {} {}",
            self.name,
            if self.is_ref { "ref" } else { "eq" },
            self.lhs.text(),
            self.rhs.text()
        )
    }
}

pub const RULES_SEXP: &str = include_str!("../rules.sexp");

/// The library, instantiated at i32 and i64, interleaved.
pub fn library() -> Vec<Rule> {
    let mut out = vec![];
    for s in sexp::parse_all(RULES_SEXP).expect("rules.sexp parses") {
        let l = s.list().expect("a rule is a list");
        let name = l[0].atom().expect("rule name").to_string();
        let is_ref = l[1].atom() == Some("ref");
        for t in [Ty::I32, Ty::I64] {
            out.push(Rule {
                name: name.clone(),
                is_ref,
                lhs: Pat::parse(&l[2], t).expect("lhs parses"),
                rhs: Pat::parse(&l[3], t).expect("rhs parses"),
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn library_parses_and_vars_are_covered() {
        let lib = super::library();
        assert_eq!(lib.len() % 2, 0);
        for r in &lib {
            let (mut l, mut rr) = (vec![], vec![]);
            r.lhs.vars(&mut l);
            r.rhs.vars(&mut rr);
            assert!(rr.iter().all(|v| l.contains(v)), "{}", r.name);
            if !r.is_ref {
                assert!(l.iter().all(|v| rr.contains(v)), "{}", r.name);
            }
        }
    }
}
