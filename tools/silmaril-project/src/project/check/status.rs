//! Phase 4: R5 (answers establish statuses), propagation along the edge kinds to a fixpoint
//!, the summaries (R10: soundness alarms), W1 (expectations) and W3 (empty domains).

use super::super::edges::{Dir, EDGE_KINDS, Rule, fixed_values};
use super::super::sources::ANSWER_SOURCES;
use super::refs::Kept;
use super::scope::{Graph, Scope};
use super::{Ctx, Outcome, summarize};
use crate::project::schema::*;
use std::collections::{BTreeMap, BTreeSet};

/// Per problem, its established statuses with the first reason found `(via_kind, via)`.
pub(super) type Statuses = BTreeMap<String, BTreeMap<&'static str, (String, String)>>;

pub(super) struct Status<'a> {
    pub statuses: Statuses,
    /// The in-scope problems (not groups).
    pub props: Vec<&'a str>,
    /// `(summary, verdict)` per in-scope problem.
    pub summaries: BTreeMap<&'a str, (&'static str, &'static str)>,
    pub answer_rows: Vec<AnswerRow>,
    pub axiom_rows: Vec<AnswerAxiom>,
    pub status_rows: Vec<StatusRow>,
    pub summary_rows: Vec<SummaryRow>,
}

fn summary_of(g: &Graph, st: &Statuses, n: &str) -> (&'static str, &'static str, bool) {
    let e: BTreeSet<&str> = st
        .get(n)
        .map(|m| m.keys().copied().collect())
        .unwrap_or_default();
    summarize(&e, g.arity_of(n))
}

pub(super) fn run<'a>(
    cx: &Ctx,
    g: &Graph,
    sc: &Scope<'a>,
    kept: &Kept,
    o: &mut Outcome,
) -> Status<'a> {
    // R5: answers and solutions establish statuses.
    let mut statuses: Statuses = BTreeMap::new();
    let mut answer_rows = Vec::new();
    let mut axiom_rows = Vec::new();
    for a in ANSWER_SOURCES.iter().flat_map(|s| (s.answers)(cx.dump)) {
        let at = format!("answer {}", a.decl);
        if !g.is_prop(a.problem) {
            o.error(&at, format!("no problem {}", a.problem));
            continue;
        }
        let Some(&status) = ANSWER_STATUSES.iter().find(|s| **s == a.status) else {
            o.error(
                &at,
                format!(
                    "status {:?} is not THM, SAT, UNS or CSA ({})",
                    a.status, a.source
                ),
            );
            continue;
        };
        if !sc.in_scope.contains(a.problem) {
            continue;
        }
        let bad: Vec<&str> = a
            .axioms
            .iter()
            .filter(|x| !STANDARD_AXIOMS.contains(&x.as_str()))
            .map(String::as_str)
            .collect();
        if bad.is_empty() {
            statuses
                .entry(a.problem.to_string())
                .or_default()
                .entry(status)
                .or_insert((a.source.to_string(), a.decl.to_string()));
        } else {
            o.error(&at, format!("non-standard axioms: {}", bad.join(", ")));
        }
        answer_rows.push(AnswerRow {
            decl: a.decl.into(),
            problem: a.problem.into(),
            status: status.into(),
            source: a.source.into(),
            witness: a
                .witness
                .map(|w| serde_json::to_string(w).unwrap_or_default()),
            module: a.module.into(),
            tier: "kernel".into(),
        });
        let set: BTreeSet<&String> = a.axioms.iter().collect();
        axiom_rows.extend(set.into_iter().map(|x| AnswerAxiom {
            decl: a.decl.into(),
            axiom: x.clone(),
        }));
    }

    // Propagate statuses to a fixpoint (all rules are monotone).
    let props: Vec<&str> = sc
        .in_scope
        .iter()
        .copied()
        .filter(|n| g.nodes[*n].kind == "prop")
        .collect();
    loop {
        let add = round(cx, g, sc, &props, &statuses);
        let mut changed = false;
        for (n, st, kind, via) in add {
            let m = statuses.entry(n).or_default();
            if !m.contains_key(st) {
                m.insert(st, (kind, via));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut status_rows = Vec::new();
    let mut summary_rows = Vec::new();
    let mut summaries: BTreeMap<&str, (&'static str, &'static str)> = BTreeMap::new();
    for n in &props {
        let (s, verdict, alarm) = summary_of(g, &statuses, n);
        let m = statuses.get(*n);
        if alarm {
            let why: Vec<String> = m
                .into_iter()
                .flatten()
                .map(|(st, (k, via))| format!("{st} by {k} {via}"))
                .collect();
            o.error(
                format!("problem {n}"),
                format!("soundness alarm: {}", why.join(", ")),
            );
        }
        if g.arity_of(n) > 0 && m.is_some_and(|m| m.contains_key("THM") && m.contains_key("UNS")) {
            o.warn(
                format!("problem {n}"),
                "THM and UNS: the argument domain is empty",
            );
        }
        for (st, (k, via)) in m.into_iter().flatten() {
            status_rows.push(StatusRow {
                problem: n.to_string(),
                status: st.to_string(),
                via_kind: k.clone(),
                via: via.clone(),
                tier: "kernel".into(),
            });
        }
        summary_rows.push(SummaryRow {
            problem: n.to_string(),
            summary: s.into(),
            verdict: verdict.into(),
            tier: "kernel".into(),
        });
        summaries.insert(n, (s, verdict));
    }

    // W1: expectations.
    for r in cx.dump.records.iter().filter(|r| kept.kept(cx, r)) {
        if let Record::Judgement(j) = r
            && let Some(e) = &j.expect
            && let Some((s, _)) = summaries.get(j.name.as_str())
        {
            let e = expect_code(e).unwrap_or(e);
            let established = statuses.get(&j.name).is_some_and(|m| m.contains_key(e));
            let ok = *s == "OPN"
                || *s == e
                || established
                || (*s == "contingent" && (e == "SAT" || e == "CSA"));
            if !ok {
                o.warn(
                    format!("problem {}", j.name),
                    format!("expect {e} but the summary is {s}"),
                );
            }
        }
    }

    Status {
        statuses,
        props,
        summaries,
        answer_rows,
        axiom_rows,
        status_rows,
        summary_rows,
    }
}

/// One propagation round: the arity-0 closure (THM ⇒ SAT, UNS ⇒ CSA), then each edge kind's
/// rule in table order. Returns `(problem, status, via_kind, via)`.
fn round(
    cx: &Ctx,
    g: &Graph,
    sc: &Scope,
    props: &[&str],
    statuses: &Statuses,
) -> Vec<(String, &'static str, String, String)> {
    let mut add: Vec<(String, &'static str, String, String)> = Vec::new();
    let has = |n: &str, s: &str| statuses.get(n).is_some_and(|m| m.contains_key(s));
    let v = |n: &str| summary_of(g, statuses, n).1;
    for n in props {
        if g.arity_of(n) == 0 {
            for (from, to) in [("THM", "SAT"), ("UNS", "CSA")] {
                if has(n, from) {
                    add.push((n.to_string(), to, "arity0".into(), from.into()));
                }
            }
        }
    }
    for ek in EDGE_KINDS {
        match ek.rule {
            Rule::Declared => {}
            Rule::ChildFails(st) => {
                for e in g.edges.iter().filter(|e| e.record_kind == ek.record) {
                    if v(&e.child) == "fails" {
                        add.push((
                            e.parent.clone(),
                            st,
                            ek.record.into(),
                            e.record_name.clone(),
                        ));
                    }
                }
            }
            Rule::AllChildrenHold(st) => {
                // All edges, so a record with a missing child never counts as proved.
                let mut recs: BTreeMap<(&str, &str), Vec<&str>> = BTreeMap::new();
                for e in g.edges.iter().filter(|e| e.record_kind == ek.record) {
                    recs.entry((&e.parent, &e.record_name))
                        .or_default()
                        .push(&e.child);
                }
                for ((parent, rec), cs) in recs {
                    if cs.iter().all(|c| v(c) == "holds") {
                        add.push((parent.into(), st, ek.record.into(), rec.into()));
                    }
                }
            }
            Rule::Transfer(rules) => {
                for e in sc.scoped.iter().filter(|e| e.record_kind == ek.record) {
                    let (general, inst) = (e.parent.as_str(), e.child.as_str());
                    let parses = cx.get(ek.record, &e.record_name).is_some_and(|r| {
                        fixed_values(r)
                            .into_iter()
                            .all(|x| cx.value(x).is_some_and(|x| v(&x.parses) == "holds"))
                    });
                    for &(dir, st, needs_parse) in rules {
                        let (from, to) = match dir {
                            Dir::Down => (general, inst),
                            Dir::Up => (inst, general),
                        };
                        if (parses || !needs_parse) && has(from, st) {
                            add.push((to.into(), st, ek.record.into(), e.record_name.clone()));
                        }
                    }
                }
            }
        }
    }
    add
}
