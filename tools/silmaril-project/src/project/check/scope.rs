//! Phase 1 (layer 0): R1, R2, the DAG, R6, the scope and R7.

use super::super::edges::{edge_kind, fixed_values, parts};
use super::super::sid;
use super::super::sources::{Existing, Node, node_source};
use super::{Ctx, Outcome, find_cycles, name_error, problem_name_error, reach};
use crate::project::{Project, schema::*};
use std::collections::{BTreeMap, BTreeSet};

/// R1 (schemas and the project sid) and R2 (names and uniqueness): the records by key.
pub(super) fn index<'a>(p: &'a Project, dump: &'a Dump, o: &mut Outcome) -> Ctx<'a> {
    if let Some(m) = &p.manifest {
        if m.schema != MANIFEST_SCHEMA {
            o.error(
                "silmaril.toml",
                format!("schema {:?} is not {MANIFEST_SCHEMA:?}", m.schema),
            );
        }
        match &m.sid {
            None => o.error(
                "silmaril.toml",
                "no project `sid` (run `sil project init` in a new project)",
            ),
            Some(s) if sid::parse(s).is_none() => o.error(
                "silmaril.toml",
                format!("sid {s:?} is not 64 lowercase hex digits"),
            ),
            _ => {}
        }
    }
    if dump.schema != DUMP_SCHEMA {
        o.error(
            "dump",
            format!("schema {:?} is not {DUMP_SCHEMA:?}", dump.schema),
        );
    }

    let mut recs: BTreeMap<(&str, &str), &Record> = BTreeMap::new();
    for r in &dump.records {
        let at = format!("{} {}", r.kind(), r.key());
        let bad = match r {
            Record::Predicate(_) | Record::Instance(_) => problem_name_error(r.key()),
            Record::Artifact(a) => a.name.as_deref().and_then(name_error),
            _ if object_kind(r.kind()).is_some() || matches!(r, Record::Group(_)) => {
                name_error(r.key())
            }
            _ => None,
        };
        if let Some(why) = bad {
            o.error(&at, format!("invalid name: {why}"));
        }
        match recs.get(&(r.kind(), r.key())) {
            Some(prev) => o.error(
                &at,
                format!("declared twice (in {} and {})", prev.module(), r.module()),
            ),
            None => {
                recs.insert((r.kind(), r.key()), r);
            }
        }
    }
    let origins = super::records::origins(p);
    let cx = Ctx {
        p,
        dump,
        recs,
        origins,
    };
    for r in &dump.records {
        if let Record::FormatDefault(d) = r
            && cx.get("format", &d.name).is_some()
        {
            o.error(
                format!("format_default {}", d.name),
                "a name is either a format or a family, not both",
            );
        }
    }
    cx
}

/// The DAG of the whole dump: nodes (silmaril's problems, then the node sources) and edges
/// (the edge kinds).
pub(super) struct Graph {
    pub nodes: BTreeMap<String, Node>,
    pub edges: Vec<Edge>,
}

impl Graph {
    pub fn is_prop(&self, n: &str) -> bool {
        self.nodes.get(n).is_some_and(|n| n.kind == "prop")
    }
    pub fn arity_of(&self, n: &str) -> i64 {
        self.nodes.get(n).map_or(0, |n| n.arity)
    }
    /// The sid kind of a node.
    pub fn object_kind(&self, n: &str) -> &'static str {
        if self.nodes[n].kind == "group" {
            "group"
        } else {
            "problem"
        }
    }
}

pub(super) fn graph(cx: &Ctx, o: &mut Outcome) -> Graph {
    let dump = cx.dump;
    let mut nodes: BTreeMap<String, Node> = BTreeMap::new();
    for pr in &dump.problems {
        if let Some(why) = problem_name_error(&pr.name) {
            o.error(
                format!("problem {}", pr.name),
                format!("invalid name: {why}"),
            );
        }
        if nodes
            .insert(pr.name.clone(), Node::closed(&pr.decl, &pr.module))
            .is_some()
        {
            o.error(format!("problem {}", pr.name), "declared twice");
        }
    }
    for r in &dump.records {
        let Some(src) = node_source(r.kind()) else {
            continue;
        };
        let Some(node) = (src.node)(r) else { continue };
        let at = format!("{} {}", r.kind(), r.key());
        match (src.existing, nodes.get_mut(r.key())) {
            (Existing::Refine, Some(n)) => {
                if node.arity != 0 {
                    o.error(
                        &at,
                        format!("arity {} but also a @[problem] (arity 0)", node.arity),
                    );
                }
                n.room = node.room;
            }
            (existing, old) => {
                let replaced = old.is_some();
                if !replaced && let Some(why) = (src.check)(r) {
                    o.error(&at, why);
                }
                nodes.insert(r.key().to_string(), node);
                if let (Existing::Error(why), true) = (existing, replaced) {
                    o.error(&at, why);
                }
            }
        }
    }
    for r in &dump.records {
        if let Record::Judgement(j) = r
            && let Some(n) = nodes.get_mut(&j.name)
            && n.kind == "prop"
        {
            n.sid_override = j.sid.clone();
        }
    }

    let mut edges: Vec<Edge> = Vec::new();
    for r in &dump.records {
        let (Some(ek), Some((parent, children, via))) = (edge_kind(r.kind()), parts(r)) else {
            continue;
        };
        for (pos, child) in children.into_iter().enumerate() {
            edges.push(Edge {
                record_kind: r.kind().into(),
                record_name: r.key().into(),
                pos: pos as i64,
                parent: parent.into(),
                child: child.clone(),
                kind: ek.kind.into(),
                via: via.cloned(),
            });
        }
    }
    Graph { nodes, edges }
}

/// What is in scope: the local nodes and everything below them, and the edges between them.
pub(super) struct Scope<'a> {
    /// The edges that pass R6.
    pub adj: BTreeMap<&'a str, BTreeSet<&'a str>>,
    pub local_nodes: BTreeSet<&'a str>,
    pub in_scope: BTreeSet<&'a str>,
    /// The R6-good edges with both ends in scope.
    pub scoped: Vec<&'a Edge>,
    pub root: Option<&'a str>,
    pub detached_reason: BTreeMap<&'a str, Option<String>>,
}

impl Scope<'_> {
    pub fn detached(&self, n: &str) -> bool {
        self.detached_reason.contains_key(n)
    }
}

/// R6 (endpoints, group placement, cycles), the scope and R7 (one root, reachability).
pub(super) fn scope<'a>(cx: &Ctx<'a>, g: &'a Graph, o: &mut Outcome) -> Scope<'a> {
    let (dump, nodes) = (cx.dump, &g.nodes);
    let mut good: Vec<&Edge> = Vec::new();
    for e in &g.edges {
        let at = cx.at(&e.record_kind, &e.record_name);
        let (pk, ck) = (nodes.get(&e.parent), nodes.get(&e.child));
        if pk.is_none() {
            o.error(
                &at,
                format!("parent {} is not a problem or group", e.parent),
            );
        }
        if ck.is_none() {
            o.error(&at, format!("child {} is not a problem or group", e.child));
        }
        let (Some(pn), Some(cn)) = (pk, ck) else {
            continue;
        };
        let ek = edge_kind(&e.record_kind).expect("an edge comes from an edge kind");
        if cn.kind == "group" && pn.kind != "group" {
            o.error(
                &at,
                format!("group {} is the child of problem {}", e.child, e.parent),
            );
        } else if !ek.groups && (pn.kind == "group" || cn.kind == "group") {
            o.error(&at, format!("{} edge between groups", e.kind));
        } else if ek.closed && (pn.arity != 0 || cn.arity != 0) {
            o.error(
                &at,
                "decompositions and refutation routes are between arity-0 problems",
            );
        } else {
            good.push(e);
        }
    }
    let mut adj: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for e in &good {
        adj.entry(&e.parent).or_default().insert(&e.child);
    }
    find_cycles(nodes, &adj, o);
    // Scope also follows instances up to their general problem (statuses flow both ways).
    let mut scope_adj = adj.clone();
    for e in good
        .iter()
        .filter(|e| edge_kind(&e.record_kind).is_some_and(|k| k.scope_up))
    {
        scope_adj.entry(&e.child).or_default().insert(&e.parent);
    }
    // ...and to the parse obligations of the values it fixes.
    for r in &dump.records {
        let Some((_, children, _)) = parts(r) else {
            continue;
        };
        for a in fixed_values(r) {
            if let Some(v) = cx.value(a)
                && nodes.contains_key(&v.parses)
            {
                for c in &children {
                    scope_adj.entry(c.as_str()).or_default().insert(&v.parses);
                }
            }
        }
    }

    let local_nodes: BTreeSet<&str> = nodes
        .iter()
        .filter(|(_, n)| cx.local(&n.module))
        .map(|(id, _)| id.as_str())
        .collect();
    let in_scope = reach(local_nodes.iter().copied(), &scope_adj);
    let scoped: Vec<&Edge> = good
        .iter()
        .copied()
        .filter(|e| in_scope.contains(e.parent.as_str()) && in_scope.contains(e.child.as_str()))
        .collect();
    let parents: BTreeSet<&str> = scoped.iter().map(|e| e.child.as_str()).collect();

    // R7: one local root, everything local reachable or detached.
    let roots: Vec<&str> = dump
        .records
        .iter()
        .filter(|r| matches!(r, Record::Root(_)) && cx.local(r.module()))
        .map(|r| r.key())
        .collect();
    let detached_reason: BTreeMap<&str, Option<String>> = dump
        .records
        .iter()
        .filter_map(|r| match r {
            Record::Detached(d) => Some((d.name.as_str(), d.reason.clone())),
            _ => None,
        })
        .collect();
    for d in detached_reason.keys() {
        if !nodes.contains_key(*d) {
            o.error(cx.at("detached", d), "not a problem or group");
        }
    }
    let mut root = None;
    match roots.as_slice() {
        [] if local_nodes.is_empty() => {}
        [] => o.error(
            "project",
            "no root record (one `silmaril root` is required)",
        ),
        [r] => root = Some(*r),
        many => o.error(
            "project",
            format!("{} roots: {}", many.len(), many.join(", ")),
        ),
    }
    if let Some(r) = root {
        if !nodes.contains_key(r) {
            o.error(format!("root {r}"), "not a problem or group");
        } else {
            if parents.contains(r) {
                o.error(format!("root {r}"), "has a parent");
            }
            let reached = reach([r], &scope_adj);
            for n in &local_nodes {
                let at = if nodes[*n].kind == "group" {
                    cx.at("group", n)
                } else {
                    format!("problem {n}")
                };
                match (reached.contains(n), detached_reason.contains_key(n)) {
                    (false, false) => {
                        o.error(&at, format!("not reachable from root {r} and not detached"))
                    }
                    (true, true) => o.warn(&at, "detached but reachable from the root"),
                    _ => {}
                }
            }
        }
    }
    Scope {
        adj,
        local_nodes,
        in_scope,
        scoped,
        root,
        detached_reason,
    }
}
