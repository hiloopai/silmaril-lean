//! Layer 0, the problem DAG: the manifest, the dump's own lists, the DAG records
//! (`judgement`, `group`, `children`, `decomposition`, `refutation_route`, `root`, `detached`)
//! and the core tables (projects, objects, problems, answers, edges, statuses).
use super::*;
use serde::Deserialize;

// ---------------------------------------------------------------- silmaril.toml

/// `silmaril.toml`. `schema` and `sid` are required; the rest is defaulted from
/// `lakefile.toml`. `sid` is an `Option` only so that its absence is reported as R1.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub schema: String,
    /// The project sid: 64 lowercase hex digits, random (`sil project init`), never derived.
    pub sid: Option<String>,
    /// Default: `lakefile.toml` `name`.
    pub name: Option<String>,
    pub version: Option<String>,
    pub description: Option<String>,
    /// Modules the dump imports. Default: the `[[lean_lib]]` names.
    pub modules: Option<Vec<String>>,
    /// Module prefixes that are local. Default: the first components of `modules`.
    pub roots: Option<Vec<String>>,
    /// The artifact registry. Default: [`ARTIFACTS_PATH`].
    pub artifacts: Option<String>,
    /// Project-defined record kinds that records files may hold (`[[segment]]`): their tables
    /// are not checked by `sil project lint` (their Lean handler checks them).
    pub kinds: Option<Vec<String>>,
    #[serde(default, rename = "import")]
    pub imports: Vec<Import>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Import {
    /// A Lake package name in `lake-manifest.json`; url and rev are read from there.
    pub package: String,
}

// ---------------------------------------------------------------- the Lean dump

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Dump {
    pub schema: String,
    pub toolchain: String,
    #[serde(default)]
    pub modules: Vec<String>,
    #[serde(default)]
    pub records: Vec<Record>,
    #[serde(default)]
    pub problems: Vec<DumpProblem>,
    #[serde(default)]
    pub solutions: Vec<DumpSolution>,
}

/// A `@[problem "NAME"]` declaration (silmaril's `problems env`): an arity-0 problem.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DumpProblem {
    pub name: String,
    pub decl: String,
    pub module: String,
}

/// A `@[solves "NAME"]` (THM) or `@[refutes "NAME"]` (UNS) theorem with its axioms.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DumpSolution {
    pub problem: String,
    pub decl: String,
    pub module: String,
    /// `solves` | `refutes`.
    pub kind: String,
    #[serde(default)]
    pub axioms: Vec<String>,
}

/// `silmaril judgement NAME …`: metadata of an existing problem.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Judgement {
    pub name: String,
    pub module: String,
    pub model: Option<String>,
    pub spec: Option<String>,
    #[serde(default)]
    pub values: Vec<String>,
    /// CIDs or registry names.
    #[serde(default)]
    pub artifacts: Vec<String>,
    /// One of [`EXPECT_CODES`].
    pub expect: Option<String>,
    pub title: Option<String>,
    pub doc: Option<String>,
    /// The problem's sid override.
    pub sid: Option<String>,
}

/// A DAG node without a statement; its result is its children's summaries.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Group {
    pub name: String,
    pub module: String,
    pub title: Option<String>,
    pub doc: Option<String>,
    pub sid: Option<String>,
}

/// Declared, unproved sub edges `name → children`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Children {
    pub name: String,
    pub module: String,
    pub children: Vec<String>,
}

/// Proved sub edges: `proof : c₁ → … → cₙ → parent` (Lean fills `parent`, `children`).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Decomposition {
    pub name: String,
    pub module: String,
    pub proof: String,
    pub parent: String,
    pub children: Vec<String>,
}

/// A proved refutation edge: `proof : ¬child → ¬parent` (Lean fills `parent`, `child`).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RefutationRoute {
    pub name: String,
    pub module: String,
    pub proof: String,
    pub parent: String,
    pub child: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Root {
    pub name: String,
    pub module: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Detached {
    pub name: String,
    pub module: String,
    pub reason: Option<String>,
}

// Derived tables.

table! {
    /// `schema`, `dump_schema`, `toolchain`, `modules`, `roots` (lists joined by `,`).
    Meta = "meta", key("key") {
        key: String = "TEXT NOT NULL",
        value: String = "TEXT NOT NULL",
    }
}

table! {
    /// The local project, every `[[import]]` and every package that owns an in-scope object.
    ProjectRow = "projects", key("sid"), unique("name") {
        sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
        version: Option<String> = "TEXT",
        description: Option<String> = "TEXT",
        root: Option<String> = "TEXT",
        url: Option<String> = "TEXT",
        rev: Option<String> = "TEXT",
    }
}

table! {
    /// Every named object (artifacts are keyed by content in `artifacts`).
    Object = "objects", key("sid"), unique("kind", "name") {
        sid: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        project: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
        sid_source: String = "TEXT NOT NULL CHECK(sid_source IN ('derived','override'))",
    }
}

table! {
    /// Problems (`prop`, any arity) and groups; model/spec/expect/title come from the
    /// judgement or the group.
    ProblemRow = "problems", key("sid"), unique("name") {
        sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('prop','group'))",
        decl: Option<String> = "TEXT",
        arity: Option<i64> = "INTEGER",
        room: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
        model: Option<String> = "TEXT",
        spec: Option<String> = "TEXT",
        expect: Option<String> = "TEXT",
        detached: bool = "INTEGER NOT NULL",
        detached_reason: Option<String> = "TEXT",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
    }
}

table! {
    /// `@[answers]` (any status), `@[solves]` (THM) and `@[refutes]` (UNS) theorems;
    /// `witness` is a JSON array.
    AnswerRow = "answers", key("decl") {
        decl: String = "TEXT NOT NULL",
        problem: String = "TEXT NOT NULL",
        status: String = "TEXT NOT NULL CHECK(status IN ('THM','SAT','UNS','CSA'))",
        source: String = "TEXT NOT NULL CHECK(source IN ('answers','solves','refutes'))",
        witness: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        tier: String = "TEXT NOT NULL",
    }
}

table! {
    AnswerAxiom = "answer_axioms", key("decl", "axiom") {
        decl: String = "TEXT NOT NULL",
        axiom: String = "TEXT NOT NULL",
    }
}

table! {
    /// One row per (record, child) of a `children`, `decomposition`, `refutation_route` or
    /// `instance` record (an instance edge is general → instance); `via` is the proof or the
    /// instance decl, NULL for declared edges.
    Edge = "edges", key("record_kind", "record_name", "pos") {
        record_kind: String = "TEXT NOT NULL",
        record_name: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        parent: String = "TEXT NOT NULL",
        child: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('sub','refute','instance'))",
        via: Option<String> = "TEXT",
    }
}

table! {
    Szs = "szs", key("code") {
        code: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        verdict: String = "TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown'))",
    }
}

table! {
    /// Every established or derived status, with the first reason found. `via_kind`:
    /// `answers` | `solves` | `refutes` | `arity0` | `instance` | `decomposition` |
    /// `refutation_route`.
    StatusRow = "statuses", key("problem", "status") {
        problem: String = "TEXT NOT NULL",
        status: String = "TEXT NOT NULL",
        via_kind: String = "TEXT NOT NULL",
        via: String = "TEXT NOT NULL",
        tier: String = "TEXT NOT NULL",
    }
}

table! {
    /// The summary of each in-scope problem (groups have none) and its Kleene verdict.
    SummaryRow = "summary", key("problem") {
        problem: String = "TEXT NOT NULL",
        summary: String = "TEXT NOT NULL",
        verdict: String = "TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown'))",
        tier: String = "TEXT NOT NULL",
    }
}
