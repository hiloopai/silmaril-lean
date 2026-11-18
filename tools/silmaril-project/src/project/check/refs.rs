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
            Record::Measure(m) => refs.push(("domain", "language_domain", m.domain.clone())),
            Record::LanguageInterpretation(i) => {
                refs.push(("domain", "language_domain", i.domain.clone()));
            }
            Record::Language(l) => {
                refs.push(("domain", "language_domain", l.domain.clone()));
                language_refs(cx, l, &at, &mut refs, o);
            }
            Record::ConsequenceSystem(c) => consequence_refs(c, &at, &mut refs, o),
            Record::Room(x) => {
                refs.extend(
                    x.institution
                        .iter()
                        .map(|i| ("institution", "institution", i.clone())),
                );
            }
            Record::Institution(x) => {
                hets_check(cx, "hets_logic", &x.hets, &x.hets_relation, &at, o);
            }
            Record::Comorphism(x) => {
                hets_check(cx, "hets_comorphism", &x.hets, &x.hets_relation, &at, o);
                refs.push(("from", "institution", x.src.clone()));
                refs.push(("to", "institution", x.dst.clone()));
                logic_fact_check("comorphism", &x.facts, &at, o);
            }
            Record::Morphism(x) => {
                hets_check(cx, "hets_comorphism", &x.hets, &x.hets_relation, &at, o);
                refs.push(("from", "institution", x.src.clone()));
                refs.push(("to", "institution", x.dst.clone()));
                logic_fact_check("morphism", &x.facts, &at, o);
            }
            Record::Corridor(x) => {
                hets_check(cx, "hets_comorphism", &x.hets, &x.hets_relation, &at, o);
                refs.push(("from", "room", x.src.clone()));
                refs.push(("to", "room", x.dst.clone()));
                logic_fact_check("corridor", &x.facts, &at, o);
            }
            Record::LogicCatalogue(c) => catalogue_check(c, &at, &mut refs, o),
            Record::LogicProperty(p) => {
                if !PROPERTY_ROLES.contains(&p.role.as_str()) {
                    o.error(
                        &at,
                        format!(
                            "role {:?} is not one of {}",
                            p.role,
                            PROPERTY_ROLES.join(", ")
                        ),
                    );
                }
                refs.extend(
                    p.system
                        .iter()
                        .map(|s| ("system", "consequence_system", s.clone())),
                );
                refs.extend(
                    p.target
                        .iter()
                        .map(|s| ("target", "consequence_system", s.clone())),
                );
            }
            Record::LogicProblem(p) => {
                refs.push(("presentation", "presentation", p.presentation.clone()));
                refs.extend(
                    p.system
                        .iter()
                        .map(|s| ("system", "consequence_system", s.clone())),
                );
                refs.extend(
                    p.entailed_by
                        .iter()
                        .map(|s| ("entailed_by", "consequence_system", s.clone())),
                );
                if p.derived.is_null() && p.entailed.is_null() && p.truth.is_null() {
                    o.error(
                        &at,
                        "a problem states at least one claim (derived, entailed or truth)",
                    );
                }
            }
            Record::LogicRow(r) => {
                let list = |v: &serde_json::Value| -> Vec<String> {
                    v.as_array()
                        .map(|a| {
                            a.iter()
                                .filter_map(|x| x.as_str().map(String::from))
                                .collect()
                        })
                        .unwrap_or_default()
                };
                for (key, kind, v) in [
                    ("systems", "consequence_system", &r.systems),
                    ("presentations", "presentation", &r.presentations),
                    ("properties", "logic_property", &r.properties),
                    ("problems", "logic_problem", &r.problems),
                ] {
                    refs.extend(list(v).into_iter().map(|n| (key, kind, n)));
                }
                refs.extend(
                    r.institution
                        .iter()
                        .map(|s| ("institution", "institution", s.clone())),
                );
            }
            Record::LogicExclusion(x) => {
                if !EXCLUSION_CATEGORIES.contains(&x.category.as_str()) {
                    o.error(
                        &at,
                        format!(
                            "category {:?} is not one of {}",
                            x.category,
                            EXCLUSION_CATEGORIES.join(", ")
                        ),
                    );
                }
                let n = |v: &serde_json::Value| v.as_array().map_or(0, Vec::len) as i64;
                let listed = n(&x.decls) + n(&x.modules);
                if listed > 0 && listed != x.count {
                    o.error(
                        &at,
                        format!(
                            "count {} but {listed} declarations or modules are listed",
                            x.count
                        ),
                    );
                }
                if x.reason.trim().is_empty() {
                    o.error(&at, "an exclusion needs a reason");
                }
            }
            Record::LogicAudit(a) => {
                if let Some(r) = &a.registered {
                    let k: &'static str = match a.object.as_str() {
                        "institution" => "institution",
                        "comorphism" => "comorphism",
                        "morphism" => "morphism",
                        "room" => "room",
                        _ => "corridor",
                    };
                    refs.push(("registered", k, r.clone()));
                }
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

/// The references of a `language` record, and its shape: the fields its `op` needs, and
/// operands, interpretation and measure over the language's own domain (the ill-typed
/// combinations Lean also rejects).
fn language_refs<'a>(
    cx: &Ctx<'a>,
    l: &'a Language,
    at: &str,
    refs: &mut Refs<'a>,
    o: &mut Outcome,
) {
    if !LANGUAGE_OPS.contains(&l.op.as_str()) {
        o.error(
            at,
            format!("op {:?} is not one of {}", l.op, LANGUAGE_OPS.join(", ")),
        );
    }
    let need = |o: &mut Outcome, field: &str, v: &Option<String>| {
        if v.is_none() {
            o.error(at, format!("op {} needs `{field}`", l.op));
        }
    };
    let n = l.args.len();
    match l.op.as_str() {
        "decl" if n > 0 => o.error(at, "op decl takes no args"),
        "format" => need(o, "format", &l.format),
        "artifact" => {
            need(o, "value", &l.value);
            need(o, "interpretation", &l.interpretation);
        }
        "union" | "inter" if n < 2 => o.error(at, format!("op {} needs at least two args", l.op)),
        "diff" if n != 2 => o.error(at, "op diff needs exactly two args"),
        "regex" => {
            need(o, "regex", &l.regex);
            if l.semantics.is_none() {
                o.error(at, "op regex needs `semantics` (list or monoid)");
            }
        }
        "within" => {
            need(o, "measure", &l.measure);
            if n != 1 || l.bound.is_none() {
                o.error(at, "op within needs one arg and a bound");
            }
        }
        _ => {}
    }
    refs.extend(l.format.iter().map(|f| ("format", "format", f.clone())));
    refs.extend(l.value.iter().map(|v| ("value", "value", v.clone())));
    for (field, kind, name) in [
        (
            "interpretation",
            "language_interpretation",
            &l.interpretation,
        ),
        ("measure", "measure", &l.measure),
    ] {
        let Some(name) = name else { continue };
        refs.push((field, kind, name.clone()));
        let dom = match cx.get(kind, name) {
            Some(Record::LanguageInterpretation(i)) => Some(&i.domain),
            Some(Record::Measure(m)) => Some(&m.domain),
            _ => None,
        };
        if let Some(d) = dom
            && *d != l.domain
        {
            o.error(
                at,
                format!("{field} {name} is over the domain {d}, not {}", l.domain),
            );
        }
    }
    for a in &l.args {
        refs.push(("args", "language", a.clone()));
        if let Some(Record::Language(m)) = cx.get("language", a)
            && m.domain != l.domain
        {
            o.error(
                at,
                format!(
                    "args: language {a} is over the domain {}, not {}",
                    m.domain, l.domain
                ),
            );
        }
    }
}

/// The references of a `consequence_system` record, and its shape: the fields its `op` needs,
/// and its operands' references.
fn consequence_refs<'a>(c: &'a ConsequenceSystem, at: &str, refs: &mut Refs<'a>, o: &mut Outcome) {
    if !CONSEQUENCE_OPS.contains(&c.op.as_str()) {
        o.error(
            at,
            format!("op {:?} is not one of {}", c.op, CONSEQUENCE_OPS.join(", ")),
        );
    }
    let n = c.args.len();
    match c.op.as_str() {
        "decl" | "erase" if n > 0 => o.error(at, format!("op {} takes no args", c.op)),
        "erase" if c.witness.is_none() => o.error(at, "op erase needs `witness`"),
        "union" | "inter" if n < 2 => o.error(at, format!("op {} needs at least two args", c.op)),
        "diff" if n != 2 => o.error(at, "op diff needs exactly two args"),
        "artifact" if n > 0 => o.error(at, "op artifact takes no args"),
        "artifact" if c.value.is_none() || c.interpretation.is_none() => {
            o.error(at, "op artifact needs `value` and `interpretation`")
        }
        _ => {}
    }
    refs.extend(c.value.iter().map(|v| ("value", "value", v.clone())));
    refs.extend(
        c.interpretation
            .iter()
            .map(|i| ("interpretation", "consequence_interpretation", i.clone())),
    );
    // Lean checked that the operands' context and conclusion types are definitionally equal
    // to the system's; the printed types here are display text, not compared.
    refs.extend(
        c.args
            .iter()
            .map(|a| ("args", "consequence_system", a.clone())),
    );
    // Lean checked that the system is over this room's sentences, and that a semantic
    // reading is the room's consequence.
    refs.extend(c.room.iter().map(|r| ("room", "room", r.clone())));
    if c.room.is_none() && (c.room_at.is_some() || c.reading.as_deref() == Some("semantic")) {
        o.error(at, "`room_at` and a semantic `reading` need `room`");
    }
}

/// The facts of an edge state properties known for its kind (Lean checked the statements).
fn logic_fact_check(kind: &str, facts: &[LogicFactSpec], at: &str, o: &mut Outcome) {
    for f in facts {
        if !LOGIC_FACTS.contains(&(kind, f.property.as_str())) {
            o.error(
                at,
                format!("facts: {} is not a property of a {kind}", f.property),
            );
        }
        let bad: Vec<&str> = f
            .axioms
            .iter()
            .map(String::as_str)
            .filter(|a| !STANDARD_AXIOMS.contains(a))
            .collect();
        if !bad.is_empty() {
            o.error(
                at,
                format!(
                    "facts: {} has non-standard axioms: {}",
                    f.proof,
                    bad.join(", ")
                ),
            );
        }
    }
}

/// `hets` names an entry of the pinned Hets logic graph (a `hets_logic` for a node, a
/// `hets_comorphism` for an edge, by its Hets spelling), and `hets_relation` is one of
/// [`HETS_RELATIONS`].
fn hets_check(
    cx: &Ctx,
    kind: &str,
    hets: &Option<String>,
    rel: &Option<String>,
    at: &str,
    o: &mut Outcome,
) {
    let Some(h) = hets else { return };
    if !rel.as_deref().is_some_and(|r| HETS_RELATIONS.contains(&r)) {
        o.error(
            at,
            format!("hets_relation must be one of {}", HETS_RELATIONS.join(", ")),
        );
    }
    let known = cx.dump.records.iter().any(|r| match r {
        Record::HetsLogic(l) => kind == "hets_logic" && &l.hets_name == h,
        Record::HetsComorphism(c) => kind == "hets_comorphism" && &c.hets_name == h,
        _ => false,
    });
    if !known {
        o.error(
            at,
            format!("hets: no {kind} spelled {h:?} in the pinned Hets logic graph"),
        );
    }
}

/// A catalogue entry: a known status; a registered or represented entry names registered records
/// (`kind:name`) and has evidence; any other entry has a reason and names no record; a prospective
/// entry has no evidence.
fn catalogue_check<'a>(c: &'a LogicCatalogue, at: &str, refs: &mut Refs<'a>, o: &mut Outcome) {
    if !CATALOGUE_STATUSES.contains(&c.status.as_str()) {
        o.error(
            at,
            format!(
                "status {:?} is not one of {}",
                c.status,
                CATALOGUE_STATUSES.join(", ")
            ),
        );
    }
    let list = |v: &serde_json::Value| -> Vec<String> {
        v.as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|x| x.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default()
    };
    let records = list(&c.records);
    let evidence = list(&c.evidence);
    let held = matches!(c.status.as_str(), "registered" | "represented");
    if held && records.is_empty() {
        o.error(at, format!("status {} names no record", c.status));
    }
    if !held && !records.is_empty() {
        o.error(at, format!("status {} names records", c.status));
    }
    if !held && c.reason.as_deref().unwrap_or("").is_empty() {
        o.error(at, format!("status {} needs a reason", c.status));
    }
    if (c.status == "prospective") != evidence.is_empty() {
        o.error(
            at,
            "an entry has evidence exactly when it is not prospective",
        );
    }
    for r in records {
        let Some((k, n)) = r.split_once(':') else {
            o.error(at, format!("records: {r:?} is not kind:name"));
            continue;
        };
        let kind: &'static str = match k {
            "institution" => "institution",
            "comorphism" => "comorphism",
            "morphism" => "morphism",
            "room" => "room",
            "corridor" => "corridor",
            _ => {
                o.error(at, format!("records: {k} is not a logic-graph kind"));
                continue;
            }
        };
        refs.push(("records", kind, n.to_string()));
    }
}
