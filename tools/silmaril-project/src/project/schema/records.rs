//! Records files (`silmaril.records.v0.2`): a project's records written as TOML, which Lean's
//! `silmaril load "PATH"` reads (`Silmaril/Project/Registry/Load/Defs.lean`). This module is the
//! schema, defined once:
//!
//! - [`RECORD_KINDS`] lists every kind a records file may hold, in the order Lean runs them,
//!   with its keys ([`Key`]: name, type, required, doc). Lean mirrors only the order
//!   (`loadKinds`; the test `lean_load_order_matches` compares the two).
//! - [`lint`] checks one file against it, with `line:col` positions and no Lean
//!   (`sil project lint`, and the first step of `sil project check`).
//! - [`json_schema`] prints it as JSON Schema (`sil project schema`), for editors and other
//!   tools; the committed copy is `docs/schemas/silmaril-records.v0.2.schema.json`.
//!
//! A records file is another spelling of the `silmaril <kind> …` commands: every key is the
//! record field of the same name, except the three spellings that Lean resolves (constants,
//! value sources and instance arguments, see [`Ty`]).

use super::{CLASSIFICATIONS, DISCLOSURE_STATES, EXPECT_CODES, Manifest};
use crate::project::check::{name_error, problem_name_error};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use std::ops::Range;
use toml::de::{DeTable, DeValue};

pub const RECORDS_SCHEMA: &str = "silmaril.records.v0.2";
/// The directory, relative to the package root, whose `*.toml` records files `sil project lint`
/// and `check` read by default.
pub const RECORDS_DIR: &str = "silmaril";

/// The type of a key's value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    /// Any string.
    Text,
    /// A dotted name (`validName`).
    Name,
    /// A problem or group name: a dotted name or a legacy silmaril id with `/`.
    Problem,
    /// An array of problem or group names.
    Problems,
    /// An array of value names.
    Names,
    /// An array of strings (CIDs or registry names).
    Texts,
    /// A Lean constant, resolved like an identifier in the command.
    Const,
    /// An imported Lean module.
    Module,
    /// One of [`EXPECT_CODES`].
    Expect,
    /// `roundtrip` or `sound`.
    Law,
    /// A sid: 64 lowercase hex digits.
    Sid,
    /// A value source: a CID, a registry path or a registry name.
    Source,
    /// The extra sources of a value: `[{ format, source }]`.
    Sources,
    /// Instance arguments: `{ <binder name or position> = <reference> }`; a reference is a name,
    /// an integer, a boolean, `{ str = "…" }` or an application `["f", <reference>, …]`.
    Args,
    /// Tool-only data (`meta = { … }`): any table. Lean ignores it, and so does R11; it is for
    /// other tools (provenance, the source a record was converted from).
    Meta,
    /// One of [`CLASSIFICATIONS`] (a finding's classification).
    Classification,
    /// One of [`DISCLOSURE_STATES`].
    Disclosure,
}

/// One key of a kind.
#[derive(Debug, Clone, Copy)]
pub struct Key {
    pub name: &'static str,
    pub ty: Ty,
    pub required: bool,
    pub doc: &'static str,
}

/// One kind: its keys, and a description.
#[derive(Debug, Clone, Copy)]
pub struct KindSpec {
    pub kind: &'static str,
    pub doc: &'static str,
    pub keys: &'static [Key],
}

const fn req(name: &'static str, ty: Ty, doc: &'static str) -> Key {
    Key {
        name,
        ty,
        required: true,
        doc,
    }
}
const fn opt(name: &'static str, ty: Ty, doc: &'static str) -> Key {
    Key {
        name,
        ty,
        required: false,
        doc,
    }
}

const DOC: Key = opt("doc", Ty::Text, "A description");
const TITLE: Key = opt("title", Ty::Text, "A one-line title");
const SID: Key = opt("sid", Ty::Sid, "A sid override (64 lowercase hex digits)");
const MODEL: Key = opt("model", Ty::Name, "The model class (a `model` record)");
const SPEC: Key = opt("spec", Ty::Name, "The spec (a `spec` record)");
const VALUES: Key = opt("values", Ty::Names, "The values the problem is about");
const ARTIFACTS: Key = opt(
    "artifacts",
    Ty::Texts,
    "Artifacts the problem reads (CIDs or names)",
);
const EXPECT: Key = opt("expect", Ty::Expect, "The expected status");
/// Every kind also takes `meta`: tool-only data that Lean does not read.
pub const META: Key = opt(
    "meta",
    Ty::Meta,
    "Tool-only data (any table): not read by Lean, not compared by `sil project check`",
);

/// The key `name` of `spec`, or [`META`] (which every kind takes).
pub fn key_of(spec: &KindSpec, name: &str) -> Option<&'static Key> {
    if name == META.name {
        return Some(&META);
    }
    spec.keys.iter().find(|k| k.name == name)
}

/// Every kind of a records file, in the order `silmaril load` runs them. Project-defined kinds
/// (listed in `silmaril.toml` `kinds`) run after these and before `root`.
pub const RECORD_KINDS: &[KindSpec] = &[
    KindSpec {
        kind: "artifact_type",
        doc: "An artifact type: `decl : ArtifactType`",
        keys: &[
            req("name", Ty::Name, "The type's name"),
            req("decl", Ty::Const, "The `ArtifactType`"),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "format",
        doc: "A format: `decl : Format T V` for a registered artifact type `T`",
        keys: &[
            req("name", Ty::Name, "The format's name"),
            req("decl", Ty::Const, "The `Format`"),
            opt("base", Ty::Name, "The format it is built on"),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "format_default",
        doc: "A format family and its default format (`<family>.…`)",
        keys: &[
            req("name", Ty::Name, "The family"),
            req("format", Ty::Name, "The default format"),
            SID,
        ],
    },
    KindSpec {
        kind: "format_law",
        doc: "A proved law of a format: `proof : RoundTrip F` or `SoundFor F rel`",
        keys: &[
            opt("name", Ty::Name, "Default: the proof's name"),
            req("format", Ty::Name, "The format"),
            req("law", Ty::Law, "`roundtrip` or `sound`"),
            req("proof", Ty::Const, "The theorem"),
            opt("rel", Ty::Const, "The relation of a `sound` law"),
        ],
    },
    KindSpec {
        kind: "value",
        doc: "A named value: an artifact read with a format, its obligation `N.parses`, and \
              `N.agrees.k` for each extra source",
        keys: &[
            req("name", Ty::Name, "The value's name"),
            req("format", Ty::Name, "The format (or a family)"),
            req(
                "source",
                Ty::Source,
                "The artifact: a CID, a registry path or a registry name",
            ),
            opt(
                "sources",
                Ty::Sources,
                "Extra sources that must agree with it",
            ),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "model",
        doc: "A model class",
        keys: &[
            req("name", Ty::Name, "The model's name"),
            req("decl", Ty::Const, "The class"),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "spec",
        doc: "A spec over a model class and a format",
        keys: &[
            req("name", Ty::Name, "The spec's name"),
            req("decl", Ty::Const, "The spec"),
            MODEL,
            opt("format", Ty::Name, "The format of the values it is about"),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "room",
        doc: "A room: `decl : Silmaril.Logic.Institution.Room`",
        keys: &[
            req("name", Ty::Name, "The room's name"),
            req("decl", Ty::Const, "The room"),
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "instance",
        doc: "An instance of a problem over arguments: fix some of its arguments. The other \
              keys go to the instance's judgement",
        keys: &[
            req("name", Ty::Problem, "The instance's name"),
            req("of", Ty::Problem, "The problem"),
            req(
                "args",
                Ty::Args,
                "The fixed arguments, by binder name or position",
            ),
            MODEL,
            SPEC,
            VALUES,
            ARTIFACTS,
            EXPECT,
            TITLE,
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "tasks",
        doc: "Every `Task.x : Prop` of a module as the open problem `<prefix>.x_in_snake_case`; \
              the other keys go to each judgement",
        keys: &[
            req("module", Ty::Module, "The module"),
            req("prefix", Ty::Name, "The problems' prefix"),
            MODEL,
            SPEC,
            VALUES,
            ARTIFACTS,
            TITLE,
            DOC,
        ],
    },
    KindSpec {
        kind: "judgement",
        doc: "Metadata of an existing problem",
        keys: &[
            req("name", Ty::Problem, "The problem"),
            MODEL,
            SPEC,
            VALUES,
            ARTIFACTS,
            EXPECT,
            TITLE,
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "detached",
        doc: "A problem that is not part of the project's verification",
        keys: &[
            req("name", Ty::Problem, "The problem"),
            opt("reason", Ty::Text, "Why"),
        ],
    },
    KindSpec {
        kind: "deprecation",
        doc: "A wrong problem, group or spec, kept for the record: why it is wrong and what \
              replaces it. A `spec_bug` finding needs its problem (or the problem's spec, or the \
              general problem it is an instance of) to be deprecated",
        keys: &[
            req("name", Ty::Problem, "The deprecated problem, group or spec"),
            req("reason", Ty::Text, "Why it is wrong"),
            opt(
                "superseded_by",
                Ty::Problems,
                "The corrected problems, groups or specs that replace it",
            ),
        ],
    },
    KindSpec {
        kind: "finding",
        doc: "The classification of a failing problem's refutation: a genuine defect of the \
              code under test (`error`, on a problem that is not deprecated), a wrong \
              statement (`spec_bug`, on a deprecated one), a gap of the machine model \
              (`model_gap`, with a `pointer` to the missing instruction or feature) or `unclear`",
        keys: &[
            req("name", Ty::Problem, "The refuted problem"),
            req(
                "classification",
                Ty::Classification,
                "`error`, `spec_bug`, `model_gap` or `unclear`",
            ),
            opt("note", Ty::Text, "What the refutation shows"),
            opt(
                "pointer",
                Ty::Text,
                "What it points at: the missing instruction or feature (required for \
                 `model_gap`), a bug report, a commit",
            ),
            opt(
                "affected_versions",
                Ty::Texts,
                "`error` only: the versions the defect affects",
            ),
            opt(
                "fixed_in",
                Ty::Text,
                "`error` only: the first fixed version",
            ),
            opt(
                "disclosure_status",
                Ty::Disclosure,
                "`error` only: `private`, `reported` or `public`",
            ),
        ],
    },
    KindSpec {
        kind: "decomposition",
        doc: "A proved edge `c₁ → … → cₙ → p`: one theorem (`proof`) or every such theorem of a \
              module (`module`)",
        keys: &[
            opt("name", Ty::Text, "Default: the proof's name"),
            opt("proof", Ty::Const, "The theorem"),
            opt(
                "module",
                Ty::Module,
                "Every theorem of this shape in the module",
            ),
        ],
    },
    KindSpec {
        kind: "refutation_route",
        doc: "A proved edge `¬c → ¬p`: one theorem (`proof`) or every such theorem of a module \
              (`module`)",
        keys: &[
            opt("name", Ty::Text, "Default: the proof's name"),
            opt("proof", Ty::Const, "The theorem"),
            opt(
                "module",
                Ty::Module,
                "Every theorem of this shape in the module",
            ),
        ],
    },
    KindSpec {
        kind: "group",
        doc: "A group: a DAG node without a statement, whose result is its children's",
        keys: &[
            req("name", Ty::Problem, "The group's name"),
            opt(
                "children",
                Ty::Problems,
                "Its children (problems or groups)",
            ),
            TITLE,
            DOC,
            SID,
        ],
    },
    KindSpec {
        kind: "children",
        doc: "Declared, unproved sub-edges of a problem",
        keys: &[
            req("name", Ty::Problem, "The parent"),
            req("children", Ty::Problems, "The children"),
        ],
    },
];

/// The kind's spec.
pub fn kind_spec(kind: &str) -> Option<&'static KindSpec> {
    RECORD_KINDS.iter().find(|k| k.kind == kind)
}

// ---------------------------------------------------------------- lint

/// One problem in a records file, at a 1-based `line:col`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Diag {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

/// A records table that passed [`lint`]: its kind, its name (if any), its keys after the
/// defaults, and where it starts.
#[derive(Debug, Clone)]
pub struct RecordTable {
    pub kind: String,
    pub name: Option<String>,
    pub keys: BTreeMap<String, Json>,
    pub line: usize,
}

/// The result of [`lint`]: the diagnostics, the tables and the `root`.
#[derive(Debug, Default)]
pub struct Linted {
    pub diags: Vec<Diag>,
    pub tables: Vec<RecordTable>,
    pub root: Option<String>,
}

/// `(line, col)`, 1-based, of a byte offset.
fn line_col(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

/// A TOML value as JSON (dates and floats as their text).
fn to_json(v: &DeValue) -> Json {
    match v {
        DeValue::String(s) => Json::String(s.to_string()),
        DeValue::Integer(i) => {
            let s = i.as_str().replace('_', "");
            let digits = s.trim_start_matches('+');
            let digits = ["0x", "0o", "0b"]
                .iter()
                .find_map(|p| digits.strip_prefix(p))
                .unwrap_or(digits);
            let n = i64::from_str_radix(digits, i.radix()).ok();
            n.map_or_else(|| Json::String(s.clone()), |n| json!(n))
        }
        DeValue::Float(f) => Json::String(f.as_str().to_string()),
        DeValue::Boolean(b) => Json::Bool(*b),
        DeValue::Datetime(d) => Json::String(d.to_string()),
        DeValue::Array(a) => Json::Array(a.iter().map(|x| to_json(x.get_ref())).collect()),
        DeValue::Table(t) => Json::Object(
            t.iter()
                .map(|(k, v)| (k.get_ref().to_string(), to_json(v.get_ref())))
                .collect(),
        ),
    }
}

/// The candidate closest to `word` by edit distance, if it is close enough to be a typo.
pub fn did_you_mean<'a>(
    word: &str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    fn distance(a: &str, b: &str) -> usize {
        let b: Vec<char> = b.chars().collect();
        let mut row: Vec<usize> = (0..=b.len()).collect();
        for (i, ca) in a.chars().enumerate() {
            let mut prev = row[0];
            row[0] = i + 1;
            for (j, cb) in b.iter().enumerate() {
                let cur = row[j + 1];
                row[j + 1] = (prev + usize::from(ca != *cb)).min(row[j] + 1).min(cur + 1);
                prev = cur;
            }
        }
        row[b.len()]
    }
    let max = (word.chars().count() / 3).max(1);
    candidates
        .into_iter()
        .map(|c| (distance(word, c), c))
        .filter(|(d, _)| *d <= max)
        .min()
        .map(|(_, c)| c)
}

/// ` (did you mean `x`?)`, or nothing.
fn hint<'a>(word: &str, candidates: impl IntoIterator<Item = &'a str>) -> String {
    did_you_mean(word, candidates).map_or_else(String::new, |c| format!(" (did you mean `{c}`?)"))
}

fn is_sid(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

fn is_lean_name(s: &str) -> bool {
    !s.is_empty()
        && s.split('.')
            .all(|seg| !seg.is_empty() && !seg.contains(char::is_whitespace))
}

/// Why `v` is not a reference (an instance argument), if it is not.
fn reference_error(v: &Json) -> Option<String> {
    match v {
        Json::String(s) if is_lean_name(s) => None,
        Json::String(s) => Some(format!("{s:?} is not a name")),
        Json::Number(_) | Json::Bool(_) => None,
        Json::Object(m) if m.len() == 1 && m.get("str").is_some_and(Json::is_string) => None,
        Json::Object(_) => Some("a table reference is `{ str = \"…\" }`".into()),
        Json::Array(xs) => match xs.split_first() {
            Some((Json::String(f), args)) if !args.is_empty() && is_lean_name(f) => {
                args.iter().find_map(reference_error)
            }
            _ => Some("an application is `[\"f\", <argument>, …]`".into()),
        },
        Json::Null => Some("null is not a reference".into()),
    }
}

/// Why `v` does not have type `ty`, if it does not.
fn type_error(ty: Ty, v: &Json) -> Option<String> {
    let names = |v: &Json, check: fn(&str) -> Option<&'static str>| -> Option<String> {
        let Json::Array(xs) = v else {
            return Some("must be an array of names".into());
        };
        xs.iter().find_map(|x| match x {
            Json::String(s) => check(s).map(|why| format!("{s:?}: {why}")),
            _ => Some("must be an array of names".into()),
        })
    };
    match ty {
        Ty::Text | Ty::Source => (!v.is_string()).then(|| "must be a string".into()),
        Ty::Const | Ty::Module => match v {
            Json::String(s) if is_lean_name(s) => None,
            _ => Some("must be a Lean name (a string)".into()),
        },
        Ty::Name => match v {
            Json::String(s) => name_error(s).map(|why| format!("{s:?}: {why}")),
            _ => Some("must be a name (a string)".into()),
        },
        Ty::Problem => match v {
            Json::String(s) => problem_name_error(s).map(|why| format!("{s:?}: {why}")),
            _ => Some("must be a name (a string)".into()),
        },
        Ty::Problems => names(v, problem_name_error),
        Ty::Names => names(v, name_error),
        Ty::Texts => match v {
            Json::Array(xs) if xs.iter().all(Json::is_string) => None,
            _ => Some("must be an array of strings".into()),
        },
        Ty::Expect => match v {
            Json::String(s) if super::expect_code(s).is_some() => None,
            _ => Some(format!(
                "must be one of {} (in any case)",
                EXPECT_CODES.join(", ")
            )),
        },
        Ty::Law => match v {
            Json::String(s) if s == "roundtrip" || s == "sound" => None,
            _ => Some("must be `roundtrip` or `sound`".into()),
        },
        Ty::Sid => match v {
            Json::String(s) if is_sid(s) => None,
            _ => Some("must be 64 lowercase hex digits".into()),
        },
        Ty::Sources => {
            let ok = |x: &Json| {
                x.as_object().is_some_and(|m| {
                    m.len() == 2
                        && m.get("format")
                            .is_some_and(|f| type_error(Ty::Name, f).is_none())
                        && m.get("source").is_some_and(Json::is_string)
                })
            };
            match v {
                Json::Array(xs) if xs.iter().all(ok) => None,
                _ => Some("must be an array `[{ format = \"…\", source = \"…\" }]`".into()),
            }
        }
        Ty::Meta => (!v.is_object()).then(|| "must be a table".into()),
        Ty::Classification => match v {
            Json::String(s) if CLASSIFICATIONS.contains(&s.as_str()) => None,
            _ => Some(format!("must be one of {}", CLASSIFICATIONS.join(", "))),
        },
        Ty::Disclosure => match v {
            Json::String(s) if DISCLOSURE_STATES.contains(&s.as_str()) => None,
            _ => Some(format!("must be one of {}", DISCLOSURE_STATES.join(", "))),
        },
        Ty::Args => match v {
            Json::Object(m) if !m.is_empty() => m
                .iter()
                .find_map(|(k, r)| reference_error(r).map(|why| format!("`{k}`: {why}"))),
            _ => Some("must be a non-empty table `{ <binder or position> = <reference> }`".into()),
        },
    }
}

/// The kinds a project may add (`silmaril.toml` `kinds`): their tables are not checked.
pub fn project_kinds(m: Option<&Manifest>) -> Vec<String> {
    m.and_then(|m| m.kinds.clone()).unwrap_or_default()
}

/// Check one records file. `extra_kinds` are project-defined kinds (opaque tables).
pub fn lint(text: &str, extra_kinds: &[String]) -> Linted {
    let mut out = Linted::default();
    let diag = |out: &mut Linted, span: Range<usize>, msg: String| {
        let (line, col) = line_col(text, span.start);
        out.diags.push(Diag { line, col, msg });
    };
    let doc = match DeTable::parse(text) {
        Ok(d) => d,
        Err(e) => {
            let at = e.span().map_or(0, |s| s.start);
            diag(&mut out, at..at, format!("not TOML: {}", e.message()));
            return out;
        }
    };
    let top = doc.get_ref();
    match top.get("schema").map(|v| (v.span(), v.get_ref())) {
        Some((_, DeValue::String(s))) if s.as_ref() == RECORDS_SCHEMA => {}
        Some((sp, _)) => diag(&mut out, sp, format!("schema must be {RECORDS_SCHEMA:?}")),
        None => diag(
            &mut out,
            0..0,
            format!("a records file starts with `schema = {RECORDS_SCHEMA:?}`"),
        ),
    }
    // the defaults, by kind
    let mut defaults: BTreeMap<String, BTreeMap<String, Json>> = BTreeMap::new();
    if let Some(d) = top.get("defaults") {
        match d.get_ref() {
            DeValue::Table(t) => {
                for (k, v) in t.iter() {
                    let kind = k.get_ref().to_string();
                    let Some(spec) = kind_spec(&kind) else {
                        let h = hint(&kind, RECORD_KINDS.iter().map(|k| k.kind));
                        diag(
                            &mut out,
                            k.span(),
                            format!("defaults: unknown kind `{kind}`{h}"),
                        );
                        continue;
                    };
                    let DeValue::Table(keys) = v.get_ref() else {
                        diag(
                            &mut out,
                            v.span(),
                            format!("`defaults.{kind}` must be a table"),
                        );
                        continue;
                    };
                    let mut m = BTreeMap::new();
                    for (key, val) in keys.iter() {
                        let key_name = key.get_ref().to_string();
                        match key_of(spec, &key_name) {
                            None => {
                                let h = hint(&key_name, spec.keys.iter().map(|k| k.name));
                                diag(
                                    &mut out,
                                    key.span(),
                                    format!("defaults.{kind}: `{kind}` has no key `{key_name}`{h}"),
                                )
                            }
                            Some(x) if x.name == "name" => diag(
                                &mut out,
                                key.span(),
                                format!("defaults.{kind}: `name` cannot have a default"),
                            ),
                            Some(x) => {
                                let j = to_json(val.get_ref());
                                if let Some(why) = type_error(x.ty, &j) {
                                    diag(
                                        &mut out,
                                        val.span(),
                                        format!("defaults.{kind}.{key_name} {why}"),
                                    );
                                }
                                m.insert(key_name, j);
                            }
                        }
                    }
                    defaults.insert(kind, m);
                }
            }
            _ => diag(
                &mut out,
                d.span(),
                "`defaults` must be a table `[defaults.<kind>]`".into(),
            ),
        }
    }
    for (k, v) in top.iter() {
        let key = k.get_ref().to_string();
        match key.as_str() {
            "schema" | "defaults" => continue,
            "root" => match v.get_ref() {
                DeValue::String(s) => match problem_name_error(s.as_ref()) {
                    None => out.root = Some(s.to_string()),
                    Some(why) => diag(&mut out, v.span(), format!("root {s:?}: {why}")),
                },
                _ => diag(&mut out, v.span(), "`root` must be a group name".into()),
            },
            _ => {
                let spec = kind_spec(&key);
                let opaque = extra_kinds.contains(&key);
                if spec.is_none() && !opaque {
                    let kinds: Vec<&str> = RECORD_KINDS.iter().map(|k| k.kind).collect();
                    let tops = ["schema", "root", "defaults"];
                    let h = hint(
                        &key,
                        kinds
                            .iter()
                            .copied()
                            .chain(tops)
                            .chain(extra_kinds.iter().map(String::as_str)),
                    );
                    diag(
                        &mut out,
                        k.span(),
                        format!(
                            "unknown key or kind `{key}`{h}: a records file has `schema`, `root`, \
                         `[defaults.<kind>]` and `[[<kind>]]` for {} (or a kind listed in \
                         silmaril.toml `kinds`)",
                            kinds.join(", ")
                        ),
                    );
                    continue;
                }
                let DeValue::Array(xs) = v.get_ref() else {
                    diag(
                        &mut out,
                        v.span(),
                        format!("`{key}` must be an array of tables `[[{key}]]`"),
                    );
                    continue;
                };
                for x in xs.iter() {
                    let DeValue::Table(t) = x.get_ref() else {
                        diag(
                            &mut out,
                            x.span(),
                            format!("`{key}` entries must be tables `[[{key}]]`"),
                        );
                        continue;
                    };
                    let (line, _) = line_col(text, x.span().start);
                    let mut keys: BTreeMap<String, Json> =
                        defaults.get(&key).cloned().unwrap_or_default();
                    let mut ok = true;
                    for (fk, fv) in t.iter() {
                        let name = fk.get_ref().to_string();
                        let j = to_json(fv.get_ref());
                        if let Some(spec) = spec {
                            match key_of(spec, &name) {
                                None => {
                                    let known: Vec<&str> =
                                        spec.keys.iter().map(|k| k.name).collect();
                                    let h = hint(&name, known.iter().copied().chain(["meta"]));
                                    diag(
                                        &mut out,
                                        fk.span(),
                                        format!(
                                            "{key}: unknown key `{name}`{h} (the keys are {})",
                                            known.join(", ")
                                        ),
                                    );
                                    ok = false;
                                }
                                Some(k) => {
                                    if let Some(why) = type_error(k.ty, &j) {
                                        diag(&mut out, fv.span(), format!("{key}.{name} {why}"));
                                        ok = false;
                                    }
                                }
                            }
                        }
                        keys.insert(name, j);
                    }
                    let name = keys.get("name").and_then(Json::as_str).map(String::from);
                    if let Some(spec) = spec {
                        let label = name
                            .clone()
                            .map_or_else(|| key.clone(), |n| format!("{key} {n}"));
                        for rk in spec.keys.iter().filter(|rk| rk.required) {
                            if !keys.contains_key(rk.name) {
                                diag(
                                    &mut out,
                                    x.span(),
                                    format!("{label}: `{}` is required", rk.name),
                                );
                                ok = false;
                            }
                        }
                        if matches!(key.as_str(), "decomposition" | "refutation_route")
                            && keys.contains_key("proof") == keys.contains_key("module")
                        {
                            diag(
                                &mut out,
                                x.span(),
                                format!("{label}: give exactly one of `proof` and `module`"),
                            );
                            ok = false;
                        }
                        if key == "finding" {
                            for why in super::markings::finding_key_errors(&keys) {
                                diag(&mut out, x.span(), format!("{label}: {why}"));
                                ok = false;
                            }
                        }
                        if key == "format_law"
                            && keys.get("law").and_then(Json::as_str) == Some("sound")
                            && !keys.contains_key("rel")
                        {
                            diag(
                                &mut out,
                                x.span(),
                                format!("{label}: a `sound` law needs `rel`"),
                            );
                            ok = false;
                        }
                    }
                    if ok {
                        out.tables.push(RecordTable {
                            kind: key.clone(),
                            name,
                            keys,
                            line,
                        });
                    }
                }
            }
        }
    }
    out.diags.sort();
    out
}

/// Duplicate `(kind, name)` across the tables of several files: `(file, line, message)`.
pub fn duplicates<'a>(
    files: impl IntoIterator<Item = (&'a str, &'a Linted)>,
) -> Vec<(String, usize, String)> {
    let mut seen: BTreeMap<(String, String), (String, usize)> = BTreeMap::new();
    let mut out = Vec::new();
    for (path, l) in files {
        for t in &l.tables {
            let Some(n) = &t.name else { continue };
            let key = (t.kind.clone(), n.clone());
            if let Some((p, line)) = seen.get(&key) {
                out.push((
                    path.to_string(),
                    t.line,
                    format!("{} {n} is also declared at {p}:{line}", t.kind),
                ));
            } else {
                seen.insert(key, (path.to_string(), t.line));
            }
        }
    }
    out
}

// ---------------------------------------------------------------- JSON Schema

fn ty_schema(ty: Ty) -> Json {
    let name =
        json!({"type": "string", "pattern": "^[a-z0-9][a-z0-9_-]*(\\.[a-z0-9][a-z0-9_-]*)*$"});
    let reference = json!({"$ref": "#/$defs/reference"});
    match ty {
        Ty::Text | Ty::Source | Ty::Const | Ty::Module | Ty::Problem => json!({"type": "string"}),
        Ty::Name => name,
        Ty::Problems | Ty::Texts => json!({"type": "array", "items": {"type": "string"}}),
        Ty::Names => json!({"type": "array", "items": name}),
        Ty::Expect => {
            let any_case: Vec<String> = EXPECT_CODES
                .iter()
                .flat_map(|c| [c.to_string(), c.to_lowercase(), c.to_uppercase()])
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            json!({"enum": any_case})
        }
        Ty::Law => json!({"enum": ["roundtrip", "sound"]}),
        Ty::Sid => json!({"type": "string", "pattern": "^[0-9a-f]{64}$"}),
        Ty::Sources => json!({"type": "array", "items": {
            "type": "object", "additionalProperties": false, "required": ["format", "source"],
            "properties": {"format": {"type": "string"}, "source": {"type": "string"}}}}),
        Ty::Args => {
            json!({"type": "object", "minProperties": 1, "additionalProperties": reference})
        }
        Ty::Meta => json!({"type": "object"}),
        Ty::Classification => json!({"enum": CLASSIFICATIONS}),
        Ty::Disclosure => json!({"enum": DISCLOSURE_STATES}),
    }
}

/// The records file as JSON Schema (draft 2020-12).
pub fn json_schema() -> Json {
    let mut props = serde_json::Map::new();
    props.insert("schema".into(), json!({"const": RECORDS_SCHEMA}));
    props.insert(
        "root".into(),
        json!({"type": "string", "description": "The project's root group"}),
    );
    let mut defaults = serde_json::Map::new();
    for k in RECORD_KINDS {
        let mut kp = serde_json::Map::new();
        for key in k.keys.iter().chain([&META]) {
            let mut s = ty_schema(key.ty);
            s["description"] = json!(key.doc);
            kp.insert(key.name.into(), s);
        }
        let required: Vec<&str> = k
            .keys
            .iter()
            .filter(|x| x.required)
            .map(|x| x.name)
            .collect();
        props.insert(
            k.kind.into(),
            json!({
            "description": k.doc,
            "type": "array",
            "items": {"type": "object", "additionalProperties": false,
                      "properties": kp.clone(), "required": required}}),
        );
        kp.remove("name");
        defaults.insert(
            k.kind.into(),
            json!({"type": "object", "additionalProperties": false, "properties": kp}),
        );
    }
    props.insert(
        "defaults".into(),
        json!({
        "description": "Keys every table of a kind gets unless it sets them",
        "type": "object", "additionalProperties": false, "properties": defaults}),
    );
    json!({
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": format!("https://hiloop.ai/schemas/{RECORDS_SCHEMA}.json"),
        "title": "silmaril records file",
        "description": "A silmaril project's records in TOML, read by Lean's `silmaril load`",
        "type": "object",
        "required": ["schema"],
        "additionalProperties": false,
        "properties": props,
        "$defs": {"reference": {"description": "A name, an integer, a boolean, { str = \"…\" } or an application [\"f\", …]",
            "anyOf": [{"type": "string"}, {"type": "integer"}, {"type": "boolean"},
                {"type": "object", "additionalProperties": false, "required": ["str"], "properties": {"str": {"type": "string"}}},
                {"type": "array", "minItems": 2, "prefixItems": [{"type": "string"}], "items": {"$ref": "#/$defs/reference"}}]}}
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_load_order_matches() {
        let lean = include_str!("../../../../../Silmaril/Project/Registry/Load/Defs.lean");
        let start = lean
            .find("def loadKinds : List String :=")
            .expect("loadKinds");
        let body = &lean[start..];
        let list = &body[body.find('[').unwrap() + 1..body.find(']').unwrap()];
        let lean_kinds: Vec<&str> = list
            .split(',')
            .map(|s| s.trim().trim_matches('"'))
            .filter(|s| !s.is_empty())
            .collect();
        let rust_kinds: Vec<&str> = RECORD_KINDS.iter().map(|k| k.kind).collect();
        assert_eq!(lean_kinds, rust_kinds);
        assert!(lean.contains(&format!("def recordsSchema : String := {RECORDS_SCHEMA:?}")));
    }

    #[test]
    fn a_good_file_lints_clean() {
        let text = r#"schema = "silmaril.records.v0.2"
root = "demo.all"
[defaults.judgement]
model = "demo.models.m"
[[judgement]]
name = "demo.p"
expect = "THM"
[[group]]
name = "demo.all"
children = ["demo.p", "zlib/1.3.1/x"]
[[instance]]
name = "demo.p.five"
of = "demo.p"
args = { n = 5, 1 = ["Nat.succ", 2], s = { str = "x" }, v = "demo.value" }
[[decomposition]]
proof = "Demo.p_of"
"#;
        let l = lint(text, &[]);
        assert!(l.diags.is_empty(), "{:?}", l.diags);
        assert_eq!(l.tables.len(), 4);
        assert_eq!(l.root.as_deref(), Some("demo.all"));
        let j = l.tables.iter().find(|t| t.kind == "judgement").unwrap();
        assert_eq!(j.keys["model"], json!("demo.models.m"));
    }

    #[test]
    fn bad_files_report_positions() {
        let text = r#"schema = "silmaril.records.v0.2"
[[judgement]]
name = "demo.p"
expect = "PROVED"
colour = "red"
[[jugdement]]
name = "x"
[[decomposition]]
name = "d"
[[instance]]
name = "demo.i"
of = "demo.p"
args = { n = ["f"] }
"#;
        let l = lint(text, &[]);
        let msgs: Vec<String> = l
            .diags
            .iter()
            .map(|d| format!("{}:{}: {}", d.line, d.col, d.msg))
            .collect();
        assert!(
            msgs.iter()
                .any(|m| m.starts_with("4:10: judgement.expect must be one of")),
            "{msgs:?}"
        );
        assert!(
            msgs.iter()
                .any(|m| m.starts_with("5:1: judgement: unknown key `colour`")),
            "{msgs:?}"
        );
        assert!(
            msgs.iter().any(|m| m
                .starts_with("6:3: unknown key or kind `jugdement` (did you mean `judgement`?)")),
            "{msgs:?}"
        );
        assert!(
            msgs.iter()
                .any(|m| m.contains("decomposition d: give exactly one of `proof` and `module`")),
            "{msgs:?}"
        );
        assert!(
            msgs.iter()
                .any(|m| m.contains("instance.args `n`: an application")),
            "{msgs:?}"
        );
        assert!(l.tables.is_empty());
        // every kind takes `meta`, a table
        let l = lint(
            "schema = \"silmaril.records.v0.2\"\n[[judgement]]\nname = \"demo.p\"\n\
             meta.origin = { file = \"a.toml\", notes = [\"x\"] }\n[[group]]\nname = \"g\"\nmeta = 1\n",
            &[],
        );
        let msgs: Vec<String> = l
            .diags
            .iter()
            .map(|d| format!("{}:{}: {}", d.line, d.col, d.msg))
            .collect();
        assert_eq!(
            msgs,
            vec!["7:8: group.meta must be a table".to_string()],
            "{msgs:?}"
        );
        // a project kind is opaque
        let l = lint(
            "schema = \"silmaril.records.v0.2\"\n[[segment]]\nname = \"s\"\nanything = 1\n",
            &["segment".into()],
        );
        assert!(l.diags.is_empty(), "{:?}", l.diags);
    }

    #[test]
    fn expect_in_any_case() {
        for (e, code) in [("csa", "CSA"), ("Thm", "THM"), ("CONTINGENT", "contingent")] {
            assert_eq!(super::super::expect_code(e), Some(code));
            let l = lint(
                &format!(
                    "schema = \"silmaril.records.v0.2\"\n[[judgement]]\nname = \"a.p\"\nexpect = \"{e}\"\n"
                ),
                &[],
            );
            assert!(l.diags.is_empty(), "{e}: {:?}", l.diags);
        }
        assert_eq!(super::super::expect_code("proved"), None);
    }

    #[test]
    fn markings_lint() {
        let good = r#"schema = "silmaril.records.v0.2"
[[deprecation]]
name = "demo.old"
reason = "off by one"
superseded_by = ["demo.new", "zlib/1.3.1/x"]
[[finding]]
name = "demo.bug"
classification = "error"
affected_versions = ["1.0"]
fixed_in = "1.1"
disclosure_status = "private"
[[finding]]
name = "demo.gap"
classification = "model_gap"
pointer = "pxor xmm0, xmm0"
"#;
        let l = lint(good, &[]);
        assert!(l.diags.is_empty(), "{:?}", l.diags);
        assert_eq!(l.tables.len(), 3);
        let bad = r#"schema = "silmaril.records.v0.2"
[[deprecation]]
name = "demo.old"
[[finding]]
name = "demo.gap"
classification = "gap"
[[finding]]
name = "demo.x"
classification = "unclear"
fixed_in = "2"
disclosure_status = "secret"
[[finding]]
name = "demo.y"
classification = "model_gap"
"#;
        let msgs: Vec<String> = lint(bad, &[])
            .diags
            .iter()
            .map(|d| format!("{}:{}: {}", d.line, d.col, d.msg))
            .collect();
        for want in [
            "2:1: deprecation demo.old: `reason` is required",
            "6:18: finding.classification must be one of error, spec_bug, model_gap, unclear",
            "7:1: finding demo.x: `fixed_in` is for `error` findings only",
            "11:21: finding.disclosure_status must be one of private, reported, public",
            "12:1: finding demo.y: a `model_gap` needs a `pointer` (the missing instruction or feature)",
        ] {
            assert!(msgs.iter().any(|m| m == want), "{want}: {msgs:?}");
        }
    }

    #[test]
    fn suggestions() {
        assert_eq!(did_you_mean("grup", ["group", "spec"]), Some("group"));
        assert_eq!(did_you_mean("fromat", ["format", "decl"]), Some("format"));
        assert_eq!(did_you_mean("xyz", ["group", "spec"]), None);
        let l = lint(
            "schema = \"silmaril.records.v0.2\"\n[[value]]\nname = \"a.v\"\nfromat = \"json\"\nsource = \"x\"\n",
            &[],
        );
        assert!(
            l.diags.iter().any(|d| d
                .msg
                .starts_with("value: unknown key `fromat` (did you mean `format`?)")),
            "{:?}",
            l.diags
        );
    }

    #[test]
    fn committed_json_schema_is_current() {
        let committed =
            include_str!("../../../../../docs/schemas/silmaril-records.v0.2.schema.json");
        let now = format!(
            "{}\n",
            serde_json::to_string_pretty(&json_schema()).unwrap()
        );
        assert!(
            committed == now,
            "docs/schemas/silmaril-records.v0.2.schema.json is stale: run \
             `sil project schema --out docs/schemas/silmaril-records.v0.2.schema.json`"
        );
    }

    #[test]
    fn json_schema_lists_every_kind() {
        let s = json_schema();
        for k in RECORD_KINDS {
            assert!(
                s["properties"][k.kind]["items"]["properties"].is_object(),
                "{}",
                k.kind
            );
        }
    }
}
