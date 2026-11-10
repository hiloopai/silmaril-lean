//! Records files (`silmaril.records.v0.2`, [`records`]): every `*.toml` records file under the
//! local package's `silmaril/` is linted (the schema checks, with `path:line:col`), and then
//! R11: every named record of a records file is in the dump with the same `title`, `doc`,
//! `expect`, `reason` and `children`. A file that no module loads, or a module not rebuilt
//! after the file changed, fails R11.

use super::{Ctx, Outcome};
use crate::project::schema::records::{self, RecordTable};
use crate::project::schema::*;
use serde_json::Value as Json;

/// A text field of a dump record, for R11.
fn text_field<'a>(r: &'a Record, key: &str) -> Option<&'a str> {
    let f = match (r, key) {
        (Record::Judgement(j), "title") => &j.title,
        (Record::Judgement(j), "doc") => &j.doc,
        (Record::Judgement(j), "expect") => &j.expect,
        (Record::Group(g), "title") => &g.title,
        (Record::Group(g), "doc") => &g.doc,
        (Record::Detached(d), "reason") => &d.reason,
        (Record::ArtifactType(x), "doc") => &x.doc,
        (Record::Format(x), "doc") => &x.doc,
        (Record::Value(x), "doc") => &x.doc,
        (Record::Model(x), "doc") => &x.doc,
        (Record::Spec(x), "doc") => &x.doc,
        (Record::Room(x), "doc") => &x.doc,
        _ => return None,
    };
    f.as_deref()
}

/// R11 for one table.
fn compare(cx: &Ctx, at: &str, t: &RecordTable, o: &mut Outcome) {
    let Some(name) = &t.name else { return };
    // the record the table declares, and the record that carries its judgement fields
    let (kind, fields_kind) = match t.kind.as_str() {
        "instance" => ("instance", "judgement"),
        k @ ("artifact_type" | "format" | "format_default" | "value" | "model" | "spec"
        | "room" | "judgement" | "detached" | "group" | "children") => (k, k),
        _ => return,
    };
    if cx.get(kind, name).is_none() {
        o.error(
            at,
            format!(
                "{kind} {name} is not in the dump (R11): load the file with `silmaril load` from a \
                 module in `modules`, rebuild it, and dump again"
            ),
        );
        return;
    }
    let stale = |o: &mut Outcome, key: &str, here: &str, there: &str| {
        o.error(
            at,
            format!(
                "{} {name}: `{key}` is {here} here and {there} in the dump (R11: stale dump? \
                 rebuild the loading module and dump again)",
                t.kind
            ),
        )
    };
    for key in ["title", "doc", "expect", "reason"] {
        let Some(Json::String(here)) = t.keys.get(key) else {
            continue;
        };
        let there = cx.get(fields_kind, name).and_then(|r| text_field(r, key));
        // `expect` in any case is the code Lean records
        let same = match (key, there) {
            ("expect", Some(t)) => expect_code(here).is_some_and(|c| expect_code(t) == Some(c)),
            _ => there == Some(here.as_str()),
        };
        if !same {
            stale(
                o,
                key,
                &format!("{here:?}"),
                &there.map_or("absent".into(), |s| format!("{s:?}")),
            );
        }
    }
    if let Some(Json::Array(cs)) = t.keys.get("children") {
        let here: Vec<&str> = cs.iter().filter_map(Json::as_str).collect();
        let there: Option<Vec<&str>> = match cx.get("children", name) {
            Some(Record::Children(c)) => Some(c.children.iter().map(String::as_str).collect()),
            _ => None,
        };
        if there.as_deref() != Some(here.as_slice()) {
            stale(
                o,
                "children",
                &format!("{here:?}"),
                &there.map_or("absent".into(), |c| format!("{c:?}")),
            );
        }
    }
}

/// Where each dump record of a records file was written: `(dump kind, name)` to
/// `path:line: <kind as written> <name>`. A `[[group]]` gives the dump records `group` and
/// `children`, an `[[instance]]` also a `judgement`.
pub(super) fn origins(
    p: &crate::project::Project,
) -> std::collections::BTreeMap<(String, String), String> {
    let extra = records::project_kinds(p.manifest.as_ref());
    let mut out = std::collections::BTreeMap::new();
    for (path, text) in p.records_files() {
        for t in records::lint(&text, &extra).tables {
            let Some(name) = &t.name else { continue };
            let at = format!("{path}:{}: {} {name}", t.line, t.kind);
            let kinds: &[&str] = match t.kind.as_str() {
                "group" => &["group", "children"],
                "instance" => &["instance", "judgement"],
                k => &[k],
            };
            for k in kinds {
                out.entry((k.to_string(), name.clone()))
                    .or_insert_with(|| at.clone());
            }
        }
    }
    out
}

pub(super) fn check(cx: &Ctx, o: &mut Outcome) {
    let p = cx.p;
    let extra = records::project_kinds(p.manifest.as_ref());
    let mut linted = Vec::new();
    for (path, text) in p.records_files() {
        let l = records::lint(&text, &extra);
        for d in &l.diags {
            o.error(format!("{path}:{}:{}", d.line, d.col), &d.msg);
        }
        linted.push((path, l));
    }
    for (path, line, msg) in records::duplicates(linted.iter().map(|(p, l)| (p.as_str(), l))) {
        o.error(format!("{path}:{line}"), msg);
    }
    for (path, l) in &linted {
        for t in &l.tables {
            compare(cx, &format!("{path}:{}", t.line), t, o);
        }
        if let Some(r) = &l.root
            && cx.get("root", r).is_none()
        {
            o.error(path, format!("root {r} is not in the dump (R11)"));
        }
    }
}
