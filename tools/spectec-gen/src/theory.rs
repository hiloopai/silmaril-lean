//! Scripts as theories of the SpecTec specification institution
//! (`Silmaril.Wasm.SpecTec.Institution`, `docs/projects/spectec/README.md`), and the comparison of two
//! of them.
//!
//! A script's **signature** is its declared syntax, function, grammar and relation names (a
//! relation with its declaration: every child of its `rel` node but the rules); its **theory**
//! is the set of its rules, each with its relation's declaration (`theoryOf`). Along a change of
//! script (a later version, an errata variant, a later upstream revision) a rule is
//! **retained** when the later script has a relation of the same name and declaration with an
//! identical rule, and **dropped** otherwise. The dropped rules are exactly the failures of the
//! inclusion of theories to be a theory morphism (`Institution.theoryOf_subset_iff`).

use crate::sexp::SExp;
use std::collections::{BTreeMap, BTreeSet};

/// A relation: its declaration (the children of `rel` that are not rules) and its rules.
pub struct Relation {
    pub decl: Vec<SExp>,
    pub rules: Vec<SExp>,
}

/// The signature and theory of a script.
pub struct Theory {
    /// `(kind, name)` for every `typ`, `def` and `gram` declaration.
    pub names: BTreeSet<(String, String)>,
    /// Relations by name (the first declaration of a name, as `Env.findRel?` reads it).
    pub rels: BTreeMap<String, Relation>,
}

fn quoted(e: &SExp) -> Option<String> {
    match e {
        SExp::Atom(a) if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') => {
            Some(a[1..a.len() - 1].to_string())
        }
        _ => None,
    }
}

fn is_rule(e: &SExp) -> bool {
    matches!(e, SExp::Node(t, _) if t == "rule")
}

/// The name of a rule node (its first child), or `?`.
pub fn rule_name(r: &SExp) -> String {
    match r {
        SExp::Node(_, ks) => ks.first().and_then(quoted).unwrap_or_else(|| "?".into()),
        SExp::Atom(_) => "?".into(),
    }
}

/// The theory of a script, reading through `rec` groups.
pub fn theory(defs: &[SExp]) -> Theory {
    fn walk(defs: &[SExp], th: &mut Theory) {
        for d in defs {
            let SExp::Node(t, ks) = d else { continue };
            match t.as_str() {
                "rec" => walk(ks, th),
                "rel" => {
                    let Some(name) = ks.first().and_then(quoted) else {
                        continue;
                    };
                    let decl = ks.iter().filter(|k| !is_rule(k)).cloned().collect();
                    let rules = ks.iter().filter(|k| is_rule(k)).cloned().collect();
                    th.rels.entry(name).or_insert(Relation { decl, rules });
                }
                "typ" | "def" | "gram" => {
                    if let Some(name) = ks.first().and_then(quoted) {
                        th.names.insert((t.clone(), name));
                    }
                }
                _ => {}
            }
        }
    }
    let mut th = Theory {
        names: BTreeSet::new(),
        rels: BTreeMap::new(),
    };
    walk(defs, &mut th);
    th
}

/// The comparison of two theories.
#[derive(Default)]
pub struct Diff {
    /// Relations in both with the same declaration.
    pub rels_kept: usize,
    /// Relations in both whose declaration changed (every rule of theirs is dropped).
    pub rels_redeclared: Vec<String>,
    pub rels_removed: Vec<String>,
    pub rels_added: Vec<String>,
    pub rules_retained: usize,
    /// `(relation, rule)` of every dropped rule.
    pub rules_dropped: Vec<(String, String)>,
    pub rules_added: usize,
    /// `(kind, name)` declared on one side only.
    pub names_removed: Vec<(String, String)>,
    pub names_added: Vec<(String, String)>,
}

impl Diff {
    /// The inclusion of theories is a theory morphism: nothing dropped.
    pub fn is_morphism(&self) -> bool {
        self.rules_dropped.is_empty()
    }
}

/// Compare the theory of `a` with that of a later script `b`.
pub fn diff(a: &Theory, b: &Theory) -> Diff {
    let mut d = Diff::default();
    for (name, ra) in &a.rels {
        match b.rels.get(name) {
            None => {
                d.rels_removed.push(name.clone());
                d.rules_dropped
                    .extend(ra.rules.iter().map(|r| (name.clone(), rule_name(r))));
            }
            Some(rb) if rb.decl != ra.decl => {
                d.rels_redeclared.push(name.clone());
                d.rules_dropped
                    .extend(ra.rules.iter().map(|r| (name.clone(), rule_name(r))));
                d.rules_added += rb.rules.len();
            }
            Some(rb) => {
                d.rels_kept += 1;
                for r in &ra.rules {
                    if rb.rules.contains(r) {
                        d.rules_retained += 1;
                    } else {
                        d.rules_dropped.push((name.clone(), rule_name(r)));
                    }
                }
                d.rules_added += rb.rules.iter().filter(|r| !ra.rules.contains(r)).count();
            }
        }
    }
    for (name, rb) in &b.rels {
        if !a.rels.contains_key(name) {
            d.rels_added.push(name.clone());
            d.rules_added += rb.rules.len();
        }
    }
    d.names_removed = a.names.difference(&b.names).cloned().collect();
    d.names_added = b.names.difference(&a.names).cloned().collect();
    d
}

/// One line summarising a comparison.
pub fn summary(label: &str, a: &Theory, d: &Diff) -> String {
    let rules: usize = a.rels.values().map(|r| r.rules.len()).sum();
    format!(
        "{label}: {} | rules {}/{rules} retained, {} dropped, {} added | relations {} kept, {} \
         redeclared, {} removed, {} added | typ/def/gram {} removed, {} added",
        if d.is_morphism() {
            "theory morphism"
        } else {
            "partial"
        },
        d.rules_retained,
        d.rules_dropped.len(),
        d.rules_added,
        d.rels_kept,
        d.rels_redeclared.len(),
        d.rels_removed.len(),
        d.rels_added.len(),
        d.names_removed.len(),
        d.names_added.len(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_stream;

    #[test]
    fn retained_dropped_added() {
        let a = parse_stream(
            "(rel \"R\" \"%\" (tup) (rule \"a\" \"%\" (tup)) (rule \"b\" \"%\" (tup)))\n\
             (rel \"S\" \"%\" (tup) (rule \"c\" \"%\" (tup)))\n(typ \"t\")\n",
        )
        .unwrap();
        let b = parse_stream(
            "(rel \"R\" \"%\" (tup) (rule \"a\" \"%\" (tup)) (rule \"b2\" \"%\" (tup)))\n\
             (rel \"S\" \"%~>%\" (tup) (rule \"c\" \"%\" (tup)))\n(typ \"u\")\n",
        )
        .unwrap();
        let d = diff(&theory(&a), &theory(&b));
        assert_eq!(d.rules_retained, 1);
        assert_eq!(
            d.rules_dropped,
            [
                ("R".to_string(), "b".to_string()),
                ("S".to_string(), "c".to_string())
            ]
        );
        assert_eq!(d.rules_added, 2);
        assert_eq!(d.rels_redeclared, ["S"]);
        assert_eq!(d.names_removed, [("typ".to_string(), "t".to_string())]);
        assert!(!d.is_morphism());
        assert!(diff(&theory(&a), &theory(&a)).is_morphism());
    }
}
