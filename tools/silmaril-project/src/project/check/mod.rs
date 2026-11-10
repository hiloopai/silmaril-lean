//! `sil project check`: scope, rules R1–R11, W1–W3 and P1–P6, the artifact registry, sids, the DAG
//! and status propagation.
//!
//! Every cross-reference rule lives here (Lean checks only what needs elaboration). The result
//! is the diagnostics, the human-readable lines (summary, root, group vectors) and the
//! [`Database`] that `sqlite` writes. [`run`] chains the phases:
//!
//! 1. [`scope`]: R1 and R2 ([`Ctx`]), the DAG ([`scope::Graph`]: nodes from
//!    [`super::sources::NODE_SOURCES`], edges from [`super::edges::EDGE_KINDS`]), R6, the scope
//!    and R7 ([`scope::Scope`]);
//! 2. [`blobs`]: the artifact registries in scope (layer 2), later R3 and W2;
//!    [`provenance`]: the local registry's derivations (P1–P6); [`records`]: the local records
//!    files (lint, R11);
//! 3. [`refs`]: the in-scope records and R4 ([`refs::Kept`]);
//! 4. [`status`]: R5 (answers from [`super::sources::ANSWER_SOURCES`]), propagation to a
//!    fixpoint, the summaries, R10 and W1, W3;
//! 5. [`rows`]: R8, sids and R9, the database and the summary lines.

mod blobs;
mod provenance;
mod records;
mod refs;
mod rows;
mod scope;
mod status;

use super::{Project, schema::*};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Default)]
pub struct Outcome {
    pub errors: BTreeSet<String>,
    pub warnings: BTreeSet<String>,
    /// Summary, root and group vectors, in print order.
    pub lines: Vec<String>,
    pub db: Database,
}

impl Outcome {
    fn error(&mut self, at: impl AsRef<str>, msg: impl AsRef<str>) {
        self.errors
            .insert(format!("{}: {}", at.as_ref(), msg.as_ref()));
    }
    fn warn(&mut self, at: impl AsRef<str>, msg: impl AsRef<str>) {
        self.warnings
            .insert(format!("{}: {}", at.as_ref(), msg.as_ref()));
    }
}

// ---------------------------------------------------------------- names

/// The longest name, in bytes.
pub const MAX_NAME: usize = 200;

/// A silmaril id: `/`-separated segments `[a-z0-9][a-z0-9._-]*` (`Silmaril.Problems.validId`).
pub fn valid_id(id: &str) -> bool {
    !id.is_empty()
        && id.split('/').all(|s| {
            let mut cs = s.chars();
            cs.next()
                .is_some_and(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
                && cs.all(|c| {
                    c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, '.' | '_' | '-')
                })
        })
}

/// `validName`: dot-separated segments `[a-z][a-z0-9_-]*` or `[0-9]+`, at most
/// [`MAX_NAME`] bytes. A leading `.` is reserved for relative names.
pub fn name_error(name: &str) -> Option<&'static str> {
    if name.is_empty() {
        return Some("empty name");
    }
    if name.len() > MAX_NAME {
        return Some("longer than 200 bytes");
    }
    if name.starts_with('.') {
        return Some("relative names (a leading '.') are reserved");
    }
    let segment_ok = |s: &str| {
        let b = s.as_bytes();
        !b.is_empty()
            && (b.iter().all(u8::is_ascii_digit)
                || (b[0].is_ascii_lowercase()
                    && b.iter().all(|c| {
                        c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, b'_' | b'-')
                    })))
    };
    if !name.split('.').all(segment_ok) {
        return Some("not a dotted name (segments [a-z][a-z0-9_-]* or [0-9]+)");
    }
    None
}

/// A problem name: a name, or a legacy silmaril id containing `/`.
pub(crate) fn problem_name_error(name: &str) -> Option<&'static str> {
    if name.contains('/') && valid_id(name) {
        None
    } else {
        name_error(name)
    }
}

// ---------------------------------------------------------------- statuses

/// The summary of a set of established statuses at an arity, with its verdict and whether it
/// is a soundness alarm. The set is closed under THM ⇒ SAT and UNS ⇒ CSA at arity 0.
pub fn summarize(e: &BTreeSet<&str>, arity: i64) -> (&'static str, &'static str, bool) {
    let has = |s: &str| e.contains(s);
    if (has("THM") && has("CSA")) || (has("UNS") && has("SAT")) {
        ("UNK", "unknown", true)
    } else if has("THM") {
        ("THM", "holds", false)
    } else if has("SAT") && has("CSA") {
        ("contingent", "fails", false)
    } else if has("UNS") {
        ("UNS", if arity == 0 { "fails" } else { "unknown" }, false)
    } else if has("CSA") {
        ("CSA", "fails", false)
    } else if has("SAT") {
        ("SAT", "unknown", false)
    } else {
        ("OPN", "unknown", false)
    }
}

// ---------------------------------------------------------------- the check

/// What every phase reads: the project, the dump, and its records by `(kind, key)` (R2).
pub(super) struct Ctx<'a> {
    pub p: &'a Project,
    pub dump: &'a Dump,
    pub recs: BTreeMap<(&'a str, &'a str), &'a Record>,
    /// Where records files wrote dump records ([`records::origins`]).
    pub origins: BTreeMap<(String, String), String>,
}

impl<'a> Ctx<'a> {
    /// Where to report about the dump record `kind name`: its records file and line, with the
    /// kind as written there, else `kind name`.
    pub fn at(&self, kind: &str, name: &str) -> String {
        self.origins
            .get(&(kind.to_string(), name.to_string()))
            .cloned()
            .unwrap_or_else(|| format!("{kind} {name}"))
    }
    pub fn get(&self, kind: &str, key: &str) -> Option<&'a Record> {
        self.recs.get(&(kind, key)).copied()
    }
    pub fn local(&self, module: &str) -> bool {
        self.p.is_local(module)
    }
    pub fn origin(&self, module: &str) -> String {
        if self.local(module) {
            "local"
        } else {
            "imported"
        }
        .to_string()
    }
    /// The first record of a kind and key stands for it (a duplicate is an R2 error).
    pub fn first(&self, r: &Record) -> bool {
        self.recs
            .get(&(r.kind(), r.key()))
            .is_some_and(|x| std::ptr::eq(*x, r))
    }
    pub fn value(&self, name: &str) -> Option<&'a Value> {
        match self.get("value", name) {
            Some(Record::Value(v)) => Some(v),
            _ => None,
        }
    }
}

/// The check, phase by phase. Each phase reads the earlier phases' results and reports into
/// the one [`Outcome`]; a layer adds a phase (or a row to a source table) without touching the
/// others.
pub fn run(p: &Project, dump: &Dump) -> Outcome {
    let mut o = Outcome::default();
    let cx = scope::index(p, dump, &mut o); // R1, R2
    let g = scope::graph(&cx, &mut o); // nodes and edges
    let sc = scope::scope(&cx, &g, &mut o); // R6, scope, R7
    let reg = blobs::registries(&cx, &mut o); // the artifact registries
    let provenance = provenance::check(&cx, &reg, &mut o); // P1–P5
    records::check(&cx, &mut o); // records files, R11
    let kept = refs::follow(&cx, &g, &sc, &reg, &mut o); // in-scope records, R4
    let files = blobs::hash(&cx, &reg, &kept, &mut o); // R3
    let st = status::run(&cx, &g, &sc, &kept, &mut o); // R5, propagation, W1
    blobs::inputs(&cx, &reg, &kept, &mut o); // W2
    rows::run(&cx, &g, &sc, &reg, &kept, &files, &st, &mut o); // R8, R9, the database
    o.lines.extend(provenance); // P6
    o
}

pub(super) fn reach<'a>(
    start: impl IntoIterator<Item = &'a str>,
    adj: &BTreeMap<&'a str, BTreeSet<&'a str>>,
) -> BTreeSet<&'a str> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut work: Vec<&str> = start.into_iter().collect();
    while let Some(n) = work.pop() {
        if seen.insert(n) {
            work.extend(adj.get(n).into_iter().flatten().copied());
        }
    }
    seen
}

/// R6: report each back edge's cycle as a path.
pub(super) fn find_cycles(
    nodes: &BTreeMap<String, super::sources::Node>,
    adj: &BTreeMap<&str, BTreeSet<&str>>,
    o: &mut Outcome,
) {
    fn go<'a>(
        n: &'a str,
        adj: &BTreeMap<&'a str, BTreeSet<&'a str>>,
        state: &mut BTreeMap<&'a str, u8>,
        stack: &mut Vec<&'a str>,
        found: &mut Vec<String>,
    ) {
        state.insert(n, 1);
        stack.push(n);
        for c in adj.get(n).into_iter().flatten() {
            match state.get(c) {
                Some(1) => {
                    let i = stack.iter().position(|s| s == c).unwrap();
                    let mut path: Vec<&str> = stack[i..].to_vec();
                    path.push(c);
                    found.push(path.join(" -> "));
                }
                Some(_) => {}
                None => go(c, adj, state, stack, found),
            }
        }
        stack.pop();
        state.insert(n, 2);
    }
    let (mut state, mut found) = (BTreeMap::new(), Vec::new());
    for n in nodes.keys() {
        if !state.contains_key(n.as_str()) {
            go(n, adj, &mut state, &mut Vec::new(), &mut found);
        }
    }
    for c in &found {
        o.error("dag", format!("cycle: {c}"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_name(name: &str) -> bool {
        name_error(name).is_none()
    }

    #[test]
    fn names() {
        for ok in [
            "demo.config",
            "demo.lib.v1_3_1.safety",
            "some.namespace.problems.5",
            "a-b.c_d",
            "x",
            "12",
        ] {
            assert!(valid_name(ok), "{ok}");
        }
        for bad in [
            "",
            ".rel",
            "a..b",
            "a.",
            "A.b",
            "1a",
            "a/b",
            "a.b c",
            "_a",
            "-a",
            &"a".repeat(201),
        ] {
            assert!(!valid_name(bad), "{bad}");
        }
        assert!(valid_name(&"a".repeat(200)));
        assert_eq!(
            name_error(".x"),
            Some("relative names (a leading '.') are reserved")
        );
        // Legacy ids are problem names only.
        assert!(problem_name_error("zlib/1.3.1/harness-set/x_y").is_none());
        assert!(problem_name_error("zlib").is_none());
        assert!(problem_name_error("Zlib/x").is_some());
        assert!(valid_id("zlib/1.3.1/harness-set/x_y"));
        assert!(!valid_id("a//b"));
    }

    #[test]
    fn summaries() {
        let s = |xs: &[&'static str], a| summarize(&xs.iter().copied().collect(), a);
        assert_eq!(s(&[], 0), ("OPN", "unknown", false));
        assert_eq!(s(&["THM", "SAT"], 0), ("THM", "holds", false));
        assert_eq!(s(&["UNS", "CSA"], 0), ("UNS", "fails", false));
        assert_eq!(s(&["UNS"], 2), ("UNS", "unknown", false));
        assert_eq!(s(&["SAT", "CSA"], 1), ("contingent", "fails", false));
        assert_eq!(s(&["SAT"], 1), ("SAT", "unknown", false));
        assert_eq!(s(&["CSA"], 1), ("CSA", "fails", false));
        assert_eq!(s(&["THM", "UNS"], 1), ("THM", "holds", false));
        assert!(s(&["THM", "CSA"], 1).2);
        assert!(s(&["UNS", "SAT"], 1).2);
    }
}
