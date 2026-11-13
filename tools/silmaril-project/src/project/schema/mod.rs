//! Every `sil project` format, one module per layer:
//! [`dag`] (layer 0: manifest, dump, DAG records, core tables), [`relational`] (predicates,
//! answers, instances), [`artifacts`] (the registry and blobs), [`values`] (formats and
//! values), [`rooms`] and [`models`] (models and specs), [`trust`] (decision-procedure and
//! axiom trust, from a separate trust dump). This module holds what the layers
//! share: the schema strings, the closed [`Record`] enum (one line per kind, so an unknown kind
//! is rejected), the [`table!`] macro and the DDL order ([`tables`]).
//!
//! - `silmaril.toml` ([`Manifest`], [`MANIFEST_SCHEMA`]): optional project metadata; when it
//!   exists it must carry the project sid.
//! - `silmaril/artifacts.toml` ([`Artifacts`], [`ARTIFACTS_SCHEMA`]): the artifact registry,
//!   keyed by CID, and how artifacts are built ([`Derivation`]); `sil project lock` writes its
//!   digest fields.
//! - Records files ([`records`], [`records::RECORDS_SCHEMA`]): a project's records in TOML,
//!   read by Lean's `silmaril load`.
//! - The Lean dump ([`Dump`], [`DUMP_SCHEMA`]): what `#silmaril_dump` writes. Records are flat
//!   objects tagged by `kind`; `name`, `module` and `sid` are reserved, every other key is a
//!   field.
//! - The database ([`DB_SCHEMA`]): every table is declared once with [`table!`], which
//!   generates the row struct, its DDL and its SQL values from one field list. Where a record
//!   kind is stored as a table, the record struct *is* the row struct, so adding a plain data
//!   field to a record kind touches only its layer's file.
//!
//! Every object row is keyed by its sid. References between rows are **names** (unique per
//! kind; the `objects` table maps `(kind, name)` to the sid), which keeps the record struct and
//! the row struct one struct and the SQL readable.
//!
//! Every struct read from a file uses `deny_unknown_fields`: an unknown kind or key is an
//! error, so the list of kinds and fields lives only in this module tree.

use serde::Deserialize;

pub const MANIFEST_SCHEMA: &str = "silmaril.project.v0.1";
pub const ARTIFACTS_SCHEMA: &str = "silmaril.artifacts.v0.2";
pub const DUMP_SCHEMA: &str = "silmaril.project-dump.v0.1";
pub const DB_SCHEMA: &str = "silmaril.project-db.v0.2";
/// The default registry path, relative to the package root.
pub const ARTIFACTS_PATH: &str = "silmaril/artifacts.toml";
/// The `checker` of the tool-tier facts `sil project check` records.
pub const CHECKER: &str = concat!(
    "silmaril-project-",
    env!("CARGO_PKG_VERSION"),
    "/project-check-v0.1"
);

/// Axioms a solution or answer may depend on (R5).
pub const STANDARD_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

/// The SZS rows, `(code, name, verdict)`: the Kleene verdict of a problem whose summary is
/// that code (at arity 0 `UNS` is promoted to `CSA`, see `check::summarize`).
/// `contingent` (SAT and CSA) is our label, not an SZS code.
pub const SZS: &[(&str, &str, &str)] = &[
    ("CSA", "CounterSatisfiable", "fails"),
    ("OPN", "Open", "unknown"),
    ("SAT", "Satisfiable", "unknown"),
    ("THM", "Theorem", "holds"),
    ("UNK", "Unknown", "unknown"),
    ("UNS", "Unsatisfiable", "unknown"),
    ("contingent", "Contingent (SAT and CSA)", "fails"),
];

/// Statuses an answer can establish.
pub const ANSWER_STATUSES: [&str; 4] = ["CSA", "SAT", "THM", "UNS"];
/// Codes `expect` may name.
pub const EXPECT_CODES: [&str; 6] = ["CSA", "OPN", "SAT", "THM", "UNS", "contingent"];

/// The code an `expect` names, in any case (`thm` is `THM`), as Lean records it.
pub fn expect_code(s: &str) -> Option<&'static str> {
    EXPECT_CODES
        .iter()
        .copied()
        .find(|c| c.eq_ignore_ascii_case(s))
}

/// One `silmaril <kind> …` record. The variant name is the kind (`snake_case`).
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Record {
    ArtifactType(ArtifactType),
    Artifact(Artifact),
    Format(Format),
    FormatDefault(FormatDefault),
    FormatLaw(FormatLaw),
    Value(Value),
    Spec(Spec),
    Model(Model),
    Room(Room),
    Predicate(Predicate),
    Answer(Answer),
    Instance(Instance),
    Judgement(Judgement),
    Group(Group),
    Children(Children),
    Decomposition(Decomposition),
    RefutationRoute(RefutationRoute),
    Root(Root),
    Detached(Detached),
}

/// Per kind: the field that identifies a record within its kind, and the sid kind of the
/// named object it declares (if any). Objects' names must pass `validName`.
macro_rules! record_kinds {
    ($($v:ident = $kind:literal, key $key:ident, object $obj:expr;)*) => {
        impl Record {
            pub fn kind(&self) -> &'static str { match self { $(Record::$v(_) => $kind),* } }
            /// What identifies the record within its kind (R2 uniqueness).
            pub fn key(&self) -> &str { match self { $(Record::$v(r) => &r.$key),* } }
            pub fn module(&self) -> &str { match self { $(Record::$v(r) => &r.module),* } }
        }
        /// `(record kind, sid kind of the object it declares)`.
        pub const KINDS: &[(&str, Option<&str>)] = &[$(($kind, $obj)),*];
    };
}
record_kinds! {
    ArtifactType = "artifact_type", key name, object Some("artifact_type");
    Artifact = "artifact", key cid, object None;
    Format = "format", key name, object Some("format");
    FormatDefault = "format_default", key name, object Some("family");
    FormatLaw = "format_law", key name, object None;
    Value = "value", key name, object Some("value");
    Spec = "spec", key name, object Some("spec");
    Model = "model", key name, object Some("model");
    Room = "room", key name, object Some("room");
    Predicate = "predicate", key name, object None;
    Answer = "answer", key decl, object None;
    Instance = "instance", key name, object None;
    Judgement = "judgement", key name, object None;
    Group = "group", key name, object None;
    Children = "children", key name, object None;
    Decomposition = "decomposition", key name, object None;
    RefutationRoute = "refutation_route", key name, object None;
    Root = "root", key name, object None;
    Detached = "detached", key name, object None;
}

/// The sid kind of a record kind's object (`None`: the record declares no object, or a
/// problem/group, whose sid kind is `problem`/`group`).
pub fn object_kind(record_kind: &str) -> Option<&'static str> {
    KINDS
        .iter()
        .find(|(k, _)| *k == record_kind)
        .and_then(|(_, o)| *o)
}

// ---------------------------------------------------------------- SQL values and tables

/// One SQL value. The derived order is SQLite's (`NULL < INTEGER < TEXT`, text by bytes).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sql {
    Null,
    Int(i64),
    Text(String),
}

pub trait Col {
    fn sql(&self) -> Sql;
}
impl Col for String {
    fn sql(&self) -> Sql {
        Sql::Text(self.clone())
    }
}
impl Col for i64 {
    fn sql(&self) -> Sql {
        Sql::Int(*self)
    }
}
impl Col for u64 {
    fn sql(&self) -> Sql {
        Sql::Int(i64::try_from(*self).unwrap_or(i64::MAX))
    }
}
impl Col for bool {
    fn sql(&self) -> Sql {
        Sql::Int(i64::from(*self))
    }
}
impl<T: Col> Col for Option<T> {
    fn sql(&self) -> Sql {
        self.as_ref().map_or(Sql::Null, Col::sql)
    }
}

/// A table's shape, from [`table!`].
pub trait Table {
    const NAME: &'static str;
    /// `(column, SQL type and column constraints)`, in column order.
    const COLUMNS: &'static [(&'static str, &'static str)];
    /// The primary key; rows are written in this order.
    const KEY: &'static [&'static str];
    /// Extra `UNIQUE(…)` constraint, if any.
    const UNIQUE: &'static [&'static str];
    fn row(&self) -> Vec<Sql>;
}

/// Declares a row struct and its table. `extra { … }` fields are read from the dump but are
/// not columns (lists stored in their own table, or the record's `sid` override, which is
/// read as `sid_override` because the `sid` column holds the computed sid).
macro_rules! table {
    (
        $(#[$m:meta])* $name:ident = $table:literal, key($($key:literal),+)
        $(, unique($($u:literal),+))? {
            $($(#[$fm:meta])* $f:ident : $t:ty = $sql:literal,)*
        }
        $(extra { $($(#[$em:meta])* $e:ident : $et:ty,)* })?
    ) => {
        $(#[$m])*
        #[derive(Debug, Clone, Default, Deserialize)]
        #[serde(deny_unknown_fields)]
        pub struct $name {
            $($(#[$fm])* pub $f: $t,)*
            $($($(#[$em])* pub $e: $et,)*)?
        }
        impl Table for $name {
            const NAME: &'static str = $table;
            const COLUMNS: &'static [(&'static str, &'static str)] = &[$((stringify!($f), $sql)),*];
            const KEY: &'static [&'static str] = &[$($key),+];
            const UNIQUE: &'static [&'static str] = &[$($($u),+)?];
            fn row(&self) -> Vec<Sql> { vec![$(Col::sql(&self.$f)),*] }
        }
    };
}

// Each layer declares its record structs and tables; [`tables`] fixes the DDL order.
pub mod artifacts;
pub mod dag;
pub mod models;
pub mod records;
pub mod relational;
pub mod rooms;
pub mod trust;
pub mod values;

pub use artifacts::*;
pub use dag::*;
pub use models::*;
pub use relational::*;
pub use rooms::*;
pub use trust::*;
pub use values::*;

/// Views written after the tables (then [`TRUST_VIEWS`]).
pub const VIEWS: &[&str] = &[
    "CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, \
e.record_name, e.pos, e.child, s.summary, s.verdict \
FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' \
LEFT JOIN summary s ON s.problem = e.child;",
];

/// Indexes written after the views, as `(name, table, columns)`: lookups that primary keys and
/// `UNIQUE` constraints do not already cover (edges by parent, child and kind, reverse lookups
/// by problem, value, CID and format, and verdict order). They keep queries over a large
/// database, such as `sil project explore` reading one lazily over HTTP, from scanning whole
/// tables. `objects_kind` duplicates a prefix of `UNIQUE(kind, name)` on purpose: counting by
/// kind scans it instead of the wider unique index (0.75 MB instead of 1.21 MB read on a large project).
pub const INDEXES: &[(&str, &str, &[&str])] = &[
    ("edges_parent", "edges", &["parent", "child", "kind", "via"]),
    ("edges_child", "edges", &["child", "parent"]),
    ("edges_kind", "edges", &["kind"]),
    ("summary_verdict", "summary", &["verdict", "summary"]),
    ("objects_kind", "objects", &["kind"]),
    ("problems_detached", "problems", &["detached", "name"]),
    ("answers_problem", "answers", &["problem"]),
    ("problem_inputs_value", "problem_inputs", &["value"]),
    ("problem_inputs_cid", "problem_inputs", &["cid"]),
    ("instance_args_value", "instance_args", &["value"]),
    ("instance_args_cid", "instance_args", &["cid"]),
    ("value_sources_cid", "value_sources", &["cid"]),
    ("value_sources_obligation", "value_sources", &["obligation"]),
    ("value_sources_format", "value_sources", &["format"]),
    ("value_defs_format", "value_defs", &["format"]),
    ("formats_base", "formats", &["base"]),
    ("format_laws_format", "format_laws", &["format"]),
    ("format_defaults_format", "format_defaults", &["format"]),
    ("artifact_paths_artifact", "artifact_paths", &["artifact"]),
    (
        "trust_uses_procedure",
        "trust_uses",
        &["procedure", "backend", "profile"],
    ),
    ("trust_imports_import", "trust_imports", &["import"]),
    (
        "trust_set_members_member",
        "trust_set_members",
        &["member_kind", "member"],
    ),
    (
        "trust_module_policy_set",
        "trust_module_policy",
        &["set_name"],
    ),
];

/// A table's shape without its row type.
#[derive(Debug, Clone, Copy)]
pub struct TableInfo {
    pub name: &'static str,
    pub columns: &'static [(&'static str, &'static str)],
    pub key: &'static [&'static str],
    pub unique: &'static [&'static str],
}

pub fn info<T: Table>() -> TableInfo {
    TableInfo {
        name: T::NAME,
        columns: T::COLUMNS,
        key: T::KEY,
        unique: T::UNIQUE,
    }
}

/// The column name (`r#type` → `type`).
pub fn column(name: &str) -> &str {
    name.trim_start_matches("r#")
}

/// The database: every table in DDL order with its rows.
#[derive(Debug, Default)]
pub struct Database {
    pub tables: Vec<(TableInfo, Vec<Vec<Sql>>)>,
}

impl Database {
    pub fn push<T: Table>(&mut self, rows: &[T]) {
        self.tables
            .push((info::<T>(), rows.iter().map(Table::row).collect()));
    }
}

/// The table order of the DDL (the empty database). The order is part of the canonical SQL
/// text, so a new layer appends its tables where they read best and re-blesses the goldens.
pub fn tables() -> Vec<TableInfo> {
    vec![
        info::<Meta>(),
        info::<ProjectRow>(),
        info::<Object>(),
        info::<ArtifactRow>(),
        info::<ArtifactPath>(),
        info::<Fact>(),
        info::<ArtifactType>(),
        info::<Format>(),
        info::<FormatDefault>(),
        info::<FormatLaw>(),
        info::<Value>(),
        info::<ValueSource>(),
        info::<Spec>(),
        info::<Model>(),
        info::<Room>(),
        info::<ProblemRow>(),
        info::<ProblemArg>(),
        info::<ProblemInput>(),
        info::<InstanceArgRow>(),
        info::<AnswerRow>(),
        info::<AnswerAxiom>(),
        info::<Edge>(),
        info::<Szs>(),
        info::<StatusRow>(),
        info::<SummaryRow>(),
        info::<TrustInput>(),
        info::<TrustProcedure>(),
        info::<TrustImplementation>(),
        info::<TrustSet>(),
        info::<TrustSetMember>(),
        info::<TrustPolicy>(),
        info::<TrustPolicySet>(),
        info::<TrustModule>(),
        info::<TrustImport>(),
        info::<TrustUse>(),
        info::<TrustUseAxiom>(),
        info::<TrustDeclAxiom>(),
        info::<TrustModulePolicy>(),
    ]
}
