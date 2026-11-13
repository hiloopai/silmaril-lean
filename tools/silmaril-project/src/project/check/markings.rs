//! Phase 4b: the markings ([`crate::project::schema::markings`]): deprecations and findings.
//!
//! - M1: a deprecation names a problem, group or spec, has a `reason`, and each of its
//!   `superseded_by` is a problem, group or spec other than itself (a deprecation without a
//!   replacement is a warning, W4).
//! - M2: a finding names an in-scope problem whose verdict is `fails`; its keys follow
//!   [`finding_key_errors`] (the `error`-only keys, a `model_gap`'s `pointer`).
//! - M3: a `spec_bug` finding's problem is deprecated (by itself, through its judgement's spec,
//!   or as an instance of a deprecated problem); an `error` finding's problem is not.
//!
//! A problem is *deprecated* when its own deprecation, its judgement's spec's, or (along
//! instance edges, transitively) its general problem's says so; `deprecated_problems` records
//! which. Deprecation does not change statuses or verdicts.

use super::refs::Kept;
use super::scope::{Graph, Scope};
use super::status::Status;
use super::{Ctx, Outcome};
use crate::project::schema::*;
use std::collections::BTreeMap;

/// The markings of the in-scope problems, and their rows.
#[derive(Default)]
pub(super) struct Marks {
    /// Every deprecated in-scope node: `(via_kind, via)`.
    pub deprecated: BTreeMap<String, (&'static str, String)>,
    pub deprecation_rows: Vec<DeprecationRow>,
    pub replacement_rows: Vec<Replacement>,
    pub deprecated_rows: Vec<DeprecatedProblem>,
    pub finding_rows: Vec<FindingRow>,
    pub version_rows: Vec<FindingVersion>,
}

impl Marks {
    /// Whether the project marks anything (the report prints marking lines only then).
    pub fn any(&self) -> bool {
        !self.deprecation_rows.is_empty() || !self.finding_rows.is_empty()
    }
}

/// What a deprecation or replacement names: `problem`, `group` or `spec`.
fn what(cx: &Ctx, g: &Graph, sc: &Scope, name: &str) -> Option<&'static str> {
    if sc.in_scope.contains(name) {
        return Some(if g.is_prop(name) { "problem" } else { "group" });
    }
    cx.get("spec", name).map(|_| "spec")
}

pub(super) fn run(
    cx: &Ctx,
    g: &Graph,
    sc: &Scope,
    kept: &Kept,
    st: &Status,
    o: &mut Outcome,
) -> Marks {
    let mut m = Marks::default();
    let mut deprecated_specs: BTreeMap<&str, ()> = BTreeMap::new();
    // M1: deprecations.
    for r in &cx.dump.records {
        let Record::Deprecation(d) = r else { continue };
        let at = cx.at("deprecation", &d.name);
        if !kept.kept(cx, r) {
            if cx.local(&d.module) {
                o.error(&at, "no such problem, group or spec");
            }
            continue;
        }
        let Some(kind) = what(cx, g, sc, &d.name) else {
            if g.nodes.contains_key(&d.name) {
                o.warn(&at, "problem is out of scope; dropped");
            } else {
                o.error(&at, "no such problem, group or spec");
            }
            continue;
        };
        let reason = d.reason.clone().unwrap_or_default();
        if reason.trim().is_empty() {
            o.error(&at, "a deprecation needs a `reason`");
        }
        if d.superseded_by.is_empty() {
            o.warn(
                &at,
                "deprecated without a replacement (`superseded_by`) (W4)",
            );
        }
        for (pos, s) in d.superseded_by.iter().enumerate() {
            if *s == d.name {
                o.error(&at, "superseded_by: a deprecation cannot supersede itself");
                continue;
            }
            match what(cx, g, sc, s) {
                None => o.error(&at, format!("superseded_by: no problem, group or spec {s}")),
                Some(k) => m.replacement_rows.push(Replacement {
                    name: d.name.clone(),
                    pos: pos as i64,
                    replacement: s.clone(),
                    kind: k.into(),
                }),
            }
        }
        m.deprecation_rows.push(DeprecationRow {
            name: d.name.clone(),
            kind: kind.into(),
            reason,
            module: d.module.clone(),
            origin: cx.origin(&d.module),
        });
        if kind == "spec" {
            deprecated_specs.insert(d.name.as_str(), ());
        } else {
            m.deprecated
                .insert(d.name.clone(), ("self", d.name.clone()));
        }
    }
    // Deprecation through a judgement's spec, then along instance edges to a fixpoint.
    for n in &sc.in_scope {
        if m.deprecated.contains_key(*n) {
            continue;
        }
        if let Some(Record::Judgement(j)) = cx.get("judgement", n)
            && kept.keep.contains(&("judgement", *n))
            && let Some(s) = &j.spec
            && deprecated_specs.contains_key(s.as_str())
        {
            m.deprecated.insert(n.to_string(), ("spec", s.clone()));
        }
    }
    let instances: Vec<&Instance> = cx
        .dump
        .records
        .iter()
        .filter(|r| kept.kept(cx, r))
        .filter_map(|r| match r {
            Record::Instance(i) if sc.in_scope.contains(i.name.as_str()) => Some(i),
            _ => None,
        })
        .collect();
    loop {
        let new: Vec<(String, String)> = instances
            .iter()
            .filter(|i| !m.deprecated.contains_key(&i.name) && m.deprecated.contains_key(&i.of))
            .map(|i| (i.name.clone(), i.of.clone()))
            .collect();
        if new.is_empty() {
            break;
        }
        for (n, of) in new {
            m.deprecated.insert(n, ("instance", of));
        }
    }
    m.deprecated_rows = m
        .deprecated
        .iter()
        .map(|(n, (k, via))| DeprecatedProblem {
            problem: n.clone(),
            via_kind: k.to_string(),
            via: via.clone(),
        })
        .collect();

    // M2, M3: findings.
    for r in &cx.dump.records {
        let Record::Finding(f) = r else { continue };
        let at = cx.at("finding", &f.name);
        if !kept.kept(cx, r) || !g.is_prop(&f.name) {
            if cx.local(&f.module) {
                if g.nodes.contains_key(&f.name) && !g.is_prop(&f.name) {
                    o.error(&at, "a finding is about a problem, not a group");
                } else if g.is_prop(&f.name) {
                    o.warn(&at, "problem is out of scope; dropped");
                } else {
                    o.error(&at, "no such problem");
                }
            }
            continue;
        }
        if !CLASSIFICATIONS.contains(&f.classification.as_str()) {
            o.error(
                &at,
                format!(
                    "classification {:?} is not one of {}",
                    f.classification,
                    CLASSIFICATIONS.join(", ")
                ),
            );
            continue;
        }
        for why in f.key_errors() {
            o.error(&at, why);
        }
        if let Some(d) = &f.disclosure_status
            && !DISCLOSURE_STATES.contains(&d.as_str())
        {
            o.error(
                &at,
                format!(
                    "disclosure_status {d:?} is not one of {}",
                    DISCLOSURE_STATES.join(", ")
                ),
            );
        }
        let (summary, verdict) = st
            .summaries
            .get(f.name.as_str())
            .copied()
            .unwrap_or(("OPN", "unknown"));
        if verdict != "fails" {
            o.error(
                &at,
                format!(
                    "a finding classifies a refutation, but the verdict is {verdict} ({summary}); \
                     remove the finding or refute the problem"
                ),
            );
        }
        match (f.classification.as_str(), m.deprecated.get(&f.name)) {
            ("spec_bug", None) => o.error(
                &at,
                "a spec_bug needs the problem (or its spec) to be deprecated: add a \
                 `[[deprecation]]` with the reason and `superseded_by` (M3)",
            ),
            ("error", Some((k, via))) => o.error(
                &at,
                format!(
                    "an error is a defect of the code under a correct spec, but the problem is \
                     deprecated ({}); classify the refutation as spec_bug (M3)",
                    via_text(k, via)
                ),
            ),
            _ => {}
        }
        m.finding_rows.push(FindingRow {
            problem: f.name.clone(),
            classification: f.classification.clone(),
            note: f.note.clone(),
            pointer: f.pointer.clone(),
            fixed_in: f.fixed_in.clone(),
            disclosure_status: f.disclosure_status.clone(),
            module: f.module.clone(),
            origin: cx.origin(&f.module),
        });
        m.version_rows
            .extend(
                f.affected_versions
                    .iter()
                    .enumerate()
                    .map(|(pos, v)| FindingVersion {
                        problem: f.name.clone(),
                        pos: pos as i64,
                        version: v.clone(),
                    }),
            );
    }
    m
}

/// `by its own deprecation`, `through spec S`, `as an instance of P`.
pub(super) fn via_text(kind: &str, via: &str) -> String {
    match kind {
        "self" => "by its own deprecation".into(),
        "spec" => format!("through its spec {via}"),
        _ => format!("as an instance of {via}"),
    }
}

/// The report lines: the counts (after the verdicts) and one line per deprecation and finding
/// (at the end). Empty when the project marks nothing.
pub(super) fn lines(m: &Marks, st: &Status) -> (Vec<String>, Vec<String>) {
    if !m.any() {
        return (Vec::new(), Vec::new());
    }
    let mut head = Vec::new();
    let count = |k: &str| m.deprecation_rows.iter().filter(|d| d.kind == k).count();
    let class = |c: &str| {
        m.finding_rows
            .iter()
            .filter(|f| f.classification == c)
            .count()
    };
    let unclassified = st
        .summaries
        .iter()
        .filter(|(n, d)| {
            d.1 == "fails"
                && !m.deprecated.contains_key(**n)
                && !m.finding_rows.iter().any(|f| f.problem == **n)
        })
        .count();
    head.push(format!(
        "markings: {} deprecations ({} problems, {} groups, {} specs), {} problems deprecated; \
         findings: {} error, {} spec_bug, {} model_gap, {} unclear; {unclassified} failing problems \
         not deprecated and unclassified",
        m.deprecation_rows.len(),
        count("problem"),
        count("group"),
        count("spec"),
        m.deprecated.keys().filter(|n| st.summaries.contains_key(n.as_str())).count(),
        class("error"),
        class("spec_bug"),
        class("model_gap"),
        class("unclear"),
    ));
    let live: Vec<&(&str, &str)> = st
        .summaries
        .iter()
        .filter(|(n, _)| !m.deprecated.contains_key(**n))
        .map(|(_, d)| d)
        .collect();
    let c = |v: &str| live.iter().filter(|d| d.1 == v).count();
    head.push(format!(
        "verdicts without the deprecated: {} holds, {} fails, {} unknown ({} problems)",
        c("holds"),
        c("fails"),
        c("unknown"),
        live.len()
    ));

    let mut tail = Vec::new();
    for d in &m.deprecation_rows {
        let by: Vec<&str> = m
            .replacement_rows
            .iter()
            .filter(|r| r.name == d.name)
            .map(|r| r.replacement.as_str())
            .collect();
        let by = if by.is_empty() {
            "no replacement".to_string()
        } else {
            format!("superseded by {}", by.join(", "))
        };
        let spread = if d.kind == "spec" {
            let n = m
                .deprecated
                .values()
                .filter(|(k, v)| *k == "spec" && *v == d.name)
                .count();
            format!("; deprecates {n} problems")
        } else {
            String::new()
        };
        tail.push(format!(
            "deprecated {} {}: {} ({by}{spread})",
            d.kind, d.name, d.reason
        ));
    }
    let mut findings: Vec<&FindingRow> = m.finding_rows.iter().collect();
    let rank = |c: &str| {
        CLASSIFICATIONS
            .iter()
            .position(|x| *x == c)
            .unwrap_or(usize::MAX)
    };
    findings.sort_by(|a, b| {
        (rank(&a.classification), &a.pointer, &a.problem).cmp(&(
            rank(&b.classification),
            &b.pointer,
            &b.problem,
        ))
    });
    for f in findings {
        let summary = st.summaries.get(f.problem.as_str()).map_or("OPN", |d| d.0);
        let mut parts: Vec<String> = Vec::new();
        if f.classification == "model_gap"
            && let Some(p) = &f.pointer
        {
            parts.push(format!("missing {p}"));
        }
        parts.extend(f.note.clone());
        let mut extra: Vec<String> = Vec::new();
        let versions: Vec<&str> = m
            .version_rows
            .iter()
            .filter(|v| v.problem == f.problem)
            .map(|v| v.version.as_str())
            .collect();
        if !versions.is_empty() {
            extra.push(format!("affects {}", versions.join(", ")));
        }
        extra.extend(f.fixed_in.as_ref().map(|v| format!("fixed in {v}")));
        extra.extend(
            f.disclosure_status
                .as_ref()
                .map(|d| format!("disclosure {d}")),
        );
        if f.classification != "model_gap" {
            extra.extend(f.pointer.as_ref().map(|p| format!("see {p}")));
        }
        if let Some((k, via)) = m.deprecated.get(&f.problem) {
            extra.push(format!("deprecated {}", via_text(k, via)));
        }
        let mut line = format!("finding {} {} [{summary}]", f.classification, f.problem);
        if !parts.is_empty() {
            line += &format!(": {}", parts.join("; "));
        }
        if !extra.is_empty() {
            line += &format!(" ({})", extra.join("; "));
        }
        tail.push(line);
    }
    (head, tail)
}
