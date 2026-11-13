//! Phase 5: R8 (imports), sids and R9 (sids are unique), the database rows in DDL
//! order, and the summary lines.

use super::super::{hash, sid};
use super::blobs::{Files, Registries};
use super::markings::{self, Marks};
use super::refs::Kept;
use super::scope::{Graph, Scope};
use super::status::Status;
use super::{Ctx, Outcome, reach};
use crate::project::schema::*;
use std::collections::{BTreeMap, BTreeSet};

/// The `objects` and `projects` rows, built as sids are assigned.
struct Objects<'c, 'a> {
    cx: &'c Ctx<'a>,
    objects: Vec<Object>,
    projects: BTreeMap<String, ProjectRow>,
    /// A package whose sid is missing is reported once (the local one by R1).
    missing_sid: BTreeSet<String>,
    sid_of: BTreeMap<(String, String), String>,
}

impl Objects<'_, '_> {
    /// The sid of the object `(kind, name)` declared in `module`: its override, else derived
    /// from its package's project sid.
    fn add(
        &mut self,
        o: &mut Outcome,
        kind: &str,
        name: &str,
        module: &str,
        over: Option<&String>,
    ) -> String {
        let p = self.cx.p;
        let at = format!("{kind} {name}");
        let project = p.package_of(module);
        let project_sid = project.as_deref().and_then(|pk| match p.project_sid(pk) {
            Ok(s) => Some(s),
            Err(e) => {
                if self.missing_sid.insert(pk.to_string()) {
                    o.error(format!("package {pk}"), e);
                }
                None
            }
        });
        if project.is_none() {
            o.error(&at, format!("no package owns module {module}"));
        }
        let pname = project.unwrap_or_default();
        if let Some(ps) = project_sid {
            let local = self.cx.local(module);
            self.projects
                .entry(pname.clone())
                .or_insert_with(|| p.project_row(&pname, ps, local));
        }
        let (sid, source) = match over {
            Some(s) => {
                if sid::parse(s).is_none() {
                    o.error(&at, format!("sid {s:?} is not 64 lowercase hex digits"));
                }
                (s.clone(), "override")
            }
            None => (
                sid::derive(kind, &project_sid.unwrap_or([0; 32]), name),
                "derived",
            ),
        };
        self.objects.push(Object {
            sid: sid.clone(),
            kind: kind.into(),
            name: name.into(),
            project: pname,
            module: module.into(),
            origin: self.cx.origin(module),
            sid_source: source.into(),
        });
        self.sid_of.insert((kind.into(), name.into()), sid.clone());
        sid
    }
}

/// The rows of the record-backed tables (each a record struct with its sid and origin).
#[derive(Default)]
struct RecordRows {
    artifact_types: Vec<ArtifactType>,
    formats: Vec<Format>,
    defaults: Vec<FormatDefault>,
    laws: Vec<FormatLaw>,
    values: Vec<Value>,
    value_sources: Vec<ValueSource>,
    specs: Vec<Spec>,
    models: Vec<Model>,
    rooms: Vec<Room>,
}

fn record_rows(
    cx: &Ctx,
    reg: &Registries,
    kept: &Kept,
    objs: &mut Objects,
    o: &mut Outcome,
) -> RecordRows {
    let mut rows = RecordRows::default();
    for r in cx.dump.records.iter().filter(|r| kept.kept(cx, r)) {
        let org = cx.origin(r.module());
        let mut obj = |o: &mut Outcome, name: &str, over: &Option<String>| {
            objs.add(
                o,
                object_kind(r.kind()).unwrap_or(""),
                name,
                r.module(),
                over.as_ref(),
            )
        };
        match r {
            Record::ArtifactType(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.artifact_types.push(ArtifactType {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::Format(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.formats.push(Format {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::FormatDefault(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.defaults.push(FormatDefault {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::FormatLaw(x) => rows.laws.push(FormatLaw {
                origin: org,
                ..x.clone()
            }),
            Record::Value(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                for (pos, s) in x.sources.iter().enumerate() {
                    rows.value_sources.push(ValueSource {
                        value: x.name.clone(),
                        pos: pos as i64,
                        cid: reg.resolve_or_keep(&s.cid),
                        format: s.format.clone(),
                        decl: s.decl.clone(),
                        obligation: if pos == 0 {
                            x.parses.clone()
                        } else {
                            x.agrees.get(pos - 1).cloned().unwrap_or_default()
                        },
                    });
                }
                rows.values.push(Value {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::Spec(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.specs.push(Spec {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::Model(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.models.push(Model {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            Record::Room(x) => {
                let sid = obj(o, &x.name, &x.sid_override);
                rows.rooms.push(Room {
                    sid,
                    origin: org,
                    ..x.clone()
                });
            }
            _ => {}
        }
    }
    rows
}

/// The rows of the node tables: problems, their arguments and inputs, instance arguments.
#[derive(Default)]
struct NodeRows {
    problems: Vec<ProblemRow>,
    args: Vec<ProblemArg>,
    inputs: Vec<ProblemInput>,
    instance_args: Vec<InstanceArgRow>,
}

fn node_rows(
    cx: &Ctx,
    g: &Graph,
    sc: &Scope,
    reg: &Registries,
    kept: &Kept,
    sid_of: &BTreeMap<(String, String), String>,
) -> NodeRows {
    let judgement = |n: &str| match cx.get("judgement", n) {
        Some(Record::Judgement(j)) if kept.keep.contains(&("judgement", n)) => Some(j),
        _ => None,
    };
    let mut rows = NodeRows::default();
    for n in &sc.in_scope {
        let node = &g.nodes[*n];
        let j = judgement(n);
        rows.problems.push(ProblemRow {
            sid: sid_of
                .get(&(g.object_kind(n).to_string(), n.to_string()))
                .cloned()
                .unwrap_or_default(),
            name: n.to_string(),
            kind: node.kind.into(),
            decl: node.decl.clone(),
            arity: (node.kind == "prop").then_some(node.arity),
            room: node.room.clone(),
            module: node.module.clone(),
            origin: cx.origin(&node.module),
            model: j.and_then(|j| j.model.clone()),
            spec: j.and_then(|j| j.spec.clone()),
            expect: j
                .and_then(|j| j.expect.as_deref())
                .map(|e| expect_code(e).unwrap_or(e).to_string()),
            detached: sc.detached(n),
            detached_reason: sc.detached_reason.get(n).cloned().flatten(),
            title: j
                .and_then(|j| j.title.clone())
                .or_else(|| node.title.clone()),
            doc: j.and_then(|j| j.doc.clone()).or_else(|| node.doc.clone()),
        });
        rows.args.extend(node.args.iter().map(|a| ProblemArg {
            problem: n.to_string(),
            pos: a.pos,
            name: a.name.clone(),
            r#type: a.r#type.clone(),
        }));
        let inputs = j.into_iter().flat_map(|j| {
            j.values.iter().map(|v| (Some(v.clone()), None)).chain(
                j.artifacts
                    .iter()
                    .map(|a| (None, Some(reg.resolve_or_keep(a)))),
            )
        });
        for (pos, (value, cid)) in inputs.enumerate() {
            rows.inputs.push(ProblemInput {
                problem: n.to_string(),
                pos: pos as i64,
                value,
                cid,
            });
        }
        if let Some(Record::Instance(i)) = cx.get("instance", n) {
            rows.instance_args
                .extend(i.args.iter().map(|a| InstanceArgRow {
                    problem: n.to_string(),
                    pos: a.pos,
                    term: a.term.clone(),
                    value: a.value.clone(),
                    cid: a.cid.as_deref().map(|c| reg.resolve_or_keep(c)),
                }));
        }
    }
    rows
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run(
    cx: &Ctx,
    g: &Graph,
    sc: &Scope,
    reg: &Registries,
    kept: &Kept,
    files: &Files,
    st: &Status,
    marks: &Marks,
    o: &mut Outcome,
) {
    let p = cx.p;

    // R8: imports.
    let mut import_rows: BTreeMap<String, (Option<String>, Option<String>)> = BTreeMap::new();
    for i in p.manifest.iter().flat_map(|m| &m.imports) {
        match p.packages.get(&i.package) {
            None => o.error(
                "silmaril.toml",
                format!("import {}: not in lake-manifest.json", i.package),
            ),
            Some(pk) => {
                import_rows.insert(i.package.clone(), (pk.url.clone(), pk.rev.clone()));
            }
        }
    }

    // sids: nodes, then the in-scope records that declare objects.
    let mut objs = Objects {
        cx,
        objects: Vec::new(),
        projects: BTreeMap::new(),
        missing_sid: p.manifest.iter().map(|_| p.name.clone()).collect(),
        sid_of: BTreeMap::new(),
    };
    for n in &sc.in_scope {
        let node = &g.nodes[*n];
        objs.add(
            o,
            g.object_kind(n),
            n,
            &node.module,
            node.sid_override.as_ref(),
        );
    }
    let recs = record_rows(cx, reg, kept, &mut objs, o);
    let in_scope_blobs = reg.in_scope(kept);
    let artifact_rows: Vec<ArtifactRow> = in_scope_blobs
        .iter()
        .map(|(cid, b)| ArtifactRow {
            sid: hash::blake3_of_cid(cid).unwrap_or_default(),
            cid: (*cid).clone(),
            r#type: b.entry.r#type.clone(),
            name: b.entry.name.clone(),
            size: b.entry.size,
            sha256: b.entry.sha256.clone(),
            git_sha1: b.entry.git_sha1.clone(),
            registry: b.registry.clone(),
            doc: b.entry.doc.clone(),
        })
        .collect();
    // R9: sids are unique.
    let mut by_sid: BTreeMap<&str, String> = BTreeMap::new();
    for (sid, what) in objs
        .objects
        .iter()
        .map(|x| (x.sid.as_str(), format!("{} {}", x.kind, x.name)))
        .chain(
            artifact_rows
                .iter()
                .map(|a| (a.sid.as_str(), format!("artifact {}", a.cid))),
        )
    {
        if let Some(prev) = by_sid.insert(sid, what.clone()) {
            o.error(format!("sid {sid}"), format!("shared by {prev} and {what}"));
        }
    }
    let local_sid = p
        .manifest
        .as_ref()
        .and_then(|m| m.sid.as_deref())
        .and_then(sid::parse);
    if let Some(ps) = local_sid {
        objs.projects
            .entry(p.name.clone())
            .or_insert_with(|| p.project_row(&p.name, ps, true));
    }
    if let Some(row) = objs.projects.get_mut(&p.name) {
        row.root = sc.root.map(String::from);
    }
    for (pk, (url, rev)) in &import_rows {
        match p.project_sid(pk) {
            Ok(ps) => {
                let row = objs
                    .projects
                    .entry(pk.clone())
                    .or_insert_with(|| p.project_row(pk, ps, false));
                row.url = url.clone();
                row.rev = rev.clone();
            }
            Err(e) => {
                if objs.missing_sid.insert(pk.clone()) {
                    o.error(format!("package {pk}"), e);
                }
            }
        }
    }

    let nodes = node_rows(cx, g, sc, reg, kept, &objs.sid_of);
    let edge_rows: Vec<Edge> = sc.scoped.iter().map(|e| (*e).clone()).collect();
    let meta = [
        ("dump_schema", cx.dump.schema.clone()),
        ("modules", p.modules.join(",")),
        ("roots", p.roots.join(",")),
        ("schema", DB_SCHEMA.to_string()),
        ("toolchain", cx.dump.toolchain.clone()),
    ]
    .map(|(k, v)| Meta {
        key: k.into(),
        value: v,
    });
    let szs: Vec<Szs> = SZS
        .iter()
        .map(|(c, n, v)| Szs {
            code: c.to_string(),
            name: n.to_string(),
            verdict: v.to_string(),
        })
        .collect();
    let paths: Vec<ArtifactPath> = files
        .paths
        .iter()
        .map(|((pk, path), cid)| ArtifactPath {
            package: pk.clone(),
            path: path.clone(),
            artifact: hash::blake3_of_cid(cid).unwrap_or_default(),
        })
        .collect();
    let projects: Vec<ProjectRow> = objs.projects.into_values().collect();
    // The order of `schema::tables`.
    let db = &mut o.db;
    db.push(&meta);
    db.push(&projects);
    db.push(&objs.objects);
    db.push(&artifact_rows);
    db.push(&paths);
    db.push(&files.facts);
    db.push(&recs.artifact_types);
    db.push(&recs.formats);
    db.push(&recs.defaults);
    db.push(&recs.laws);
    db.push(&recs.values);
    db.push(&recs.value_sources);
    db.push(&recs.specs);
    db.push(&recs.models);
    db.push(&recs.rooms);
    db.push(&nodes.problems);
    db.push(&nodes.args);
    db.push(&nodes.inputs);
    db.push(&nodes.instance_args);
    db.push(&st.answer_rows);
    db.push(&st.axiom_rows);
    db.push(&edge_rows);
    db.push(&szs);
    db.push(&st.status_rows);
    db.push(&st.summary_rows);
    db.push(&marks.deprecation_rows);
    db.push(&marks.replacement_rows);
    db.push(&marks.deprecated_rows);
    db.push(&marks.finding_rows);
    db.push(&marks.version_rows);

    lines(
        g,
        sc,
        kept,
        st,
        marks,
        artifact_rows.len(),
        edge_rows.len(),
        o,
    );
}

/// The summary line, the root, each predicate's statuses and each group's vector.
#[allow(clippy::too_many_arguments)]
fn lines(
    g: &Graph,
    sc: &Scope,
    kept: &Kept,
    st: &Status,
    marks: &Marks,
    n_artifacts: usize,
    n_edges: usize,
    o: &mut Outcome,
) {
    let summaries = &st.summaries;
    let count = |v: &str| summaries.values().filter(|d| d.1 == v).count();
    let local: Vec<&str> = sc
        .local_nodes
        .iter()
        .copied()
        .filter(|n| g.nodes[*n].kind == "prop")
        .collect();
    let count_local = |v: &str| {
        local
            .iter()
            .filter(|n| summaries.get(**n).is_some_and(|d| d.1 == v))
            .count()
    };
    let groups = sc
        .in_scope
        .iter()
        .filter(|n| g.nodes[**n].kind == "group")
        .count();
    o.lines.push(format!(
        "summary: {} problems ({} local), {groups} groups, {} records, {n_edges} edges, {n_artifacts} artifacts",
        st.props.len(),
        local.len(),
        kept.keep.len(),
    ));
    o.lines.push(format!(
        "verdicts: {} holds, {} fails, {} unknown (all {} problems); {} holds, {} fails, {} unknown ({} local)",
        count("holds"),
        count("fails"),
        count("unknown"),
        st.props.len(),
        count_local("holds"),
        count_local("fails"),
        count_local("unknown"),
        local.len(),
    ));
    let (head, tail) = markings::lines(marks, st);
    o.lines.extend(head);
    o.lines
        .push(format!("root: {}", sc.root.unwrap_or("(none)")));
    let dep = |n: &str| {
        if marks.deprecated.contains_key(n) {
            "[deprecated]"
        } else {
            ""
        }
    };
    for n in st.props.iter().filter(|n| g.arity_of(n) > 0) {
        let codes: Vec<&str> = st
            .statuses
            .get(*n)
            .map(|m| m.keys().copied().collect())
            .unwrap_or_default();
        o.lines.push(format!(
            "predicate {n} (arity {}): status {} [{}], verdict {}{}",
            g.arity_of(n),
            summaries[n].0,
            codes.join(" "),
            summaries[n].1,
            if dep(n).is_empty() {
                ""
            } else {
                ", deprecated"
            },
        ));
    }
    for n in sc.in_scope.iter().filter(|n| g.nodes[**n].kind == "group") {
        let mut kids: Vec<&Edge> = sc
            .scoped
            .iter()
            .copied()
            .filter(|e| e.parent == *n)
            .collect();
        kids.sort_by(|a, b| {
            (&a.record_kind, &a.record_name, a.pos).cmp(&(&b.record_kind, &b.record_name, b.pos))
        });
        let v: Vec<String> = kids
            .iter()
            .map(|e| {
                // a nested group shows the verdicts of the problems below it
                let s = summaries.get(e.child.as_str()).map_or_else(
                    || {
                        let below = reach([e.child.as_str()], &sc.adj);
                        let c = |v: &str| {
                            below
                                .iter()
                                .filter(|n| summaries.get(**n).is_some_and(|d| d.1 == v))
                                .count()
                        };
                        format!(
                            "group({} holds, {} fails, {} unknown)",
                            c("holds"),
                            c("fails"),
                            c("unknown")
                        )
                    },
                    |x| x.0.to_string(),
                );
                format!("{}={s}{}", e.child, dep(&e.child))
            })
            .collect();
        o.lines.push(format!("group {n}: [{}]", v.join(", ")));
    }
    o.lines.extend(tail);
}
