//! Phase 3: the in-scope records and R4 (every reference resolves).
//!
//! A record is in scope when it is local, when it is about an in-scope node, or when an
//! in-scope record references it. R4 is checked while following references.

use super::super::edges::edge_kind;
use super::super::sources::node_source;
use super::blobs::Registries;
use super::scope::{Graph, Scope};
use super::{Ctx, Outcome};
use crate::project::schema::*;
use std::collections::{BTreeSet, VecDeque};

/// What a record references: `(field, target kind, target key)`.
type Refs<'a> = Vec<(&'a str, &'static str, String)>;

/// The in-scope records by `(kind, key)` and the blobs they use.
pub(super) struct Kept<'a> {
    pub keep: BTreeSet<(&'a str, &'a str)>,
    pub used_blobs: BTreeSet<String>,
}

impl Kept<'_> {
    /// The record is in scope and stands for its key.
    pub fn kept(&self, cx: &Ctx, r: &Record) -> bool {
        self.keep.contains(&(r.kind(), r.key())) && cx.first(r)
    }
}

pub(super) fn follow<'a>(
    cx: &Ctx<'a>,
    g: &Graph,
    sc: &Scope,
    reg: &Registries,
    o: &mut Outcome,
) -> Kept<'a> {
    let dump = cx.dump;
    let in_scope = &sc.in_scope;
    let mut keep: BTreeSet<(&str, &str)> = BTreeSet::new();
    let mut work: VecDeque<(&str, &str)> = VecDeque::new();
    for r in &dump.records {
        let wanted = match r {
            Record::Judgement(j) => {
                if in_scope.contains(j.name.as_str()) {
                    true
                } else {
                    if cx.local(&j.module) {
                        if g.nodes.contains_key(&j.name) {
                            o.warn(
                                format!("judgement {}", j.name),
                                "problem is out of scope; dropped",
                            );
                        } else {
                            o.error(format!("judgement {}", j.name), "no such problem");
                        }
                    }
                    false
                }
            }
            _ if node_source(r.kind()).is_some() => in_scope.contains(r.key()),
            _ if edge_kind(r.kind()).is_some() => sc
                .scoped
                .iter()
                .any(|e| e.record_kind == r.kind() && e.record_name == r.key()),
            // Markings: about an in-scope problem (a local deprecation may name a spec).
            Record::Finding(f) => in_scope.contains(f.name.as_str()),
            Record::Deprecation(d) => cx.local(&d.module) || in_scope.contains(d.name.as_str()),
            // Answers are read by R5; artifacts are checked against the registries.
            Record::Answer(_) | Record::Artifact(_) => false,
            _ => cx.local(r.module()),
        };
        if wanted && keep.insert((r.kind(), r.key())) {
            work.push_back((r.kind(), r.key()));
        }
    }
    let laws_of = |f: &str| -> Vec<(&str, &str)> {
        dump.records
            .iter()
            .filter(|r| matches!(r, Record::FormatLaw(l) if l.format == f))
            .map(|r| (r.kind(), r.key()))
            .collect()
    };
    let mut used_blobs: BTreeSet<String> = BTreeSet::new();
    let mut need_nodes: Vec<(String, String)> = Vec::new(); // (at, problem)
    while let Some((kind, key)) = work.pop_front() {
        let Some(r) = cx.get(kind, key) else { continue };
        let at = format!("{kind} {key}");
        let mut refs: Refs = Vec::new();
        let mut blob_refs: Vec<(&str, &str)> = Vec::new();
        match r {
            Record::Judgement(j) => {
                if !g.is_prop(&j.name) {
                    o.error(&at, "no such problem");
                }
                refs.extend(j.model.iter().map(|m| ("model", "model", m.clone())));
                refs.extend(j.spec.iter().map(|s| ("spec", "spec", s.clone())));
                refs.extend(j.values.iter().map(|v| ("values", "value", v.clone())));
                blob_refs.extend(j.artifacts.iter().map(|a| ("artifacts", a.as_str())));
                if let Some(e) = &j.expect
                    && expect_code(e).is_none()
                {
                    o.error(
                        &at,
                        format!("expect {e:?} is not one of {}", EXPECT_CODES.join(", ")),
                    );
                }
            }
            Record::Value(v) => {
                refs.push(("format", "format", v.format.clone()));
                for s in &v.sources {
                    refs.push(("sources.format", "format", s.format.clone()));
                    blob_refs.push(("sources.cid", &s.cid));
                }
                if v.sources.is_empty() {
                    o.error(&at, "no sources");
                } else if v.sources[0].format != v.format {
                    o.error(&at, "format is not the format of source 0");
                }
                if v.agrees.len() + 1 != v.sources.len().max(1) {
                    o.error(
                        &at,
                        format!(
                            "{} sources but {} agreement obligations",
                            v.sources.len(),
                            v.agrees.len()
                        ),
                    );
                }
                need_nodes.push((at.clone(), v.parses.clone()));
                need_nodes.extend(v.agrees.iter().map(|a| (at.clone(), a.clone())));
            }
            Record::Spec(s) => {
                refs.extend(s.model.iter().map(|m| ("model", "model", m.clone())));
                // A family name resolves to its default.
                if let Some(f) = &s.format {
                    let kind =
                        if cx.get("format", f).is_none() && cx.get("format_default", f).is_some() {
                            "format_default"
                        } else {
                            "format"
                        };
                    refs.push(("format", kind, f.clone()));
                }
            }
            Record::Format(f) => {
                refs.push(("input", "artifact_type", f.input.clone()));
                refs.extend(f.base.iter().map(|b| ("base", "format", b.clone())));
                for l in laws_of(&f.name) {
                    if keep.insert(l) {
                        work.push_back(l);
                    }
                }
            }
            Record::FormatDefault(d) => {
                refs.push(("format", "format", d.format.clone()));
                if !d.format.starts_with(&format!("{}.", d.name)) {
                    o.error(
                        &at,
                        format!("default {} is not a format of family {}", d.format, d.name),
                    );
                }
            }
            Record::FormatLaw(l) => {
                refs.push(("format", "format", l.format.clone()));
                if l.law == "sound" && l.rel.is_none() {
                    o.error(&at, "law sound needs rel");
                }
                if !["roundtrip", "sound"].contains(&l.law.as_str()) {
                    o.error(&at, format!("law {:?} is not roundtrip or sound", l.law));
                }
            }
            Record::Predicate(d) => {
                refs.extend(d.room.iter().map(|m| ("room", "room", m.clone())));
            }
            Record::Instance(i) => {
                if !g.is_prop(&i.of) || !g.is_prop(&i.name) {
                    o.error(&at, "an instance and its general problem must be problems");
                }
                let general = g.arity_of(&i.of);
                let mut seen = BTreeSet::new();
                for a in &i.args {
                    if a.pos < 0 || a.pos >= general || !seen.insert(a.pos) {
                        o.error(&at, format!("argument position {} is not a free position of {} (arity {general})", a.pos, i.of));
                    }
                    if [a.term.is_some(), a.value.is_some(), a.cid.is_some()]
                        .iter()
                        .filter(|x| **x)
                        .count()
                        != 1
                    {
                        o.error(
                            &at,
                            format!("argument {} needs exactly one of term, value, cid", a.pos),
                        );
                    }
                    refs.extend(a.value.iter().map(|v| ("args.value", "value", v.clone())));
                    blob_refs.extend(a.cid.iter().map(|c| ("args.cid", c.as_str())));
                }
                if g.is_prop(&i.of)
                    && g.is_prop(&i.name)
                    && g.arity_of(&i.name) + seen.len() as i64 != general
                {
                    o.error(
                        &at,
                        format!(
                            "{} has arity {} but fixing {} of {}'s {general} arguments leaves {}",
                            i.name,
                            g.arity_of(&i.name),
                            seen.len(),
                            i.of,
                            general - seen.len() as i64
                        ),
                    );
                }
            }
            _ => {}
        }
        for (field, k2, key2) in refs {
            match cx.get(k2, &key2) {
                None => o.error(&at, format!("{field}: no {k2} {key2}")),
                Some(r2) => {
                    let k = (r2.kind(), r2.key());
                    if keep.insert(k) {
                        work.push_back(k);
                    }
                }
            }
        }
        for (field, b) in blob_refs {
            match reg.resolve(b) {
                None => o.error(&at, format!("{field}: no artifact {b} in the registries")),
                Some(cid) => {
                    used_blobs.insert(cid);
                }
            }
        }
    }
    for (at, n) in need_nodes {
        if !g.is_prop(&n) {
            o.error(&at, format!("obligation {n} is not a problem"));
        }
    }
    Kept { keep, used_blobs }
}
