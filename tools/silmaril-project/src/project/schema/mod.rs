//! Every `sil project` format, one module per layer:
//! [`dag`] (layer 0: manifest, dump, DAG records, core tables), [`relational`] (predicates,
//! answers, instances), [`artifacts`] (the registry and blobs), [`values`] (formats and
//! values), [`rooms`] and [`logic`] (the logic graph: institutions, comorphisms, morphisms, rooms
//! and corridors), [`models`] (models and specs), [`languages`] (language domains,
//! measures, interpretations and languages), [`consequence`] (consequence systems), [`markings`] (deprecations, findings and expected-open problems). This module holds what the layers
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
pub const DUMP_SCHEMA: &str = "silmaril.project-dump.v0.2";
/// The dump schemas `check` reads: v0.1 is v0.2 without `locations`.
pub const DUMP_SCHEMAS: [&str; 2] = ["silmaril.project-dump.v0.1", DUMP_SCHEMA];
pub const DB_SCHEMA: &str = "silmaril.project-db.v0.1";
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
    Institution(Institution),
    Comorphism(Comorphism),
    Morphism(Morphism),
    Corridor(Corridor),
    LogicAudit(LogicAudit),
    HetsLogic(HetsLogic),
    HetsComorphism(HetsComorphism),
    LogicPending(LogicPending),
    LogicCatalogue(LogicCatalogue),
    LogicExclusion(LogicExclusion),
    Presentation(Presentation),
    LogicProperty(LogicProperty),
    LogicProblem(LogicProblem),
    LogicRow(LogicRow),
    Machine(Box<Machine>),
    MachineBinding(MachineBinding),
    LanguageDomain(LanguageDomain),
    Measure(Measure),
    LanguageInterpretation(LanguageInterpretation),
    Language(Box<Language>),
    ConsequenceInterpretation(ConsequenceInterpretation),
    ConsequenceSystem(Box<ConsequenceSystem>),
    ConsequenceMatrix(Box<ConsequenceMatrixCell>),
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
    Deprecation(Deprecation),
    Finding(Finding),
    ExpectedOpen(ExpectedOpen),
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
    Institution = "institution", key name, object Some("institution");
    Comorphism = "comorphism", key name, object Some("comorphism");
    Morphism = "morphism", key name, object Some("morphism");
    Corridor = "corridor", key name, object Some("corridor");
    LogicAudit = "logic_audit", key name, object None;
    HetsLogic = "hets_logic", key name, object None;
    HetsComorphism = "hets_comorphism", key name, object None;
    LogicPending = "logic_pending", key name, object None;
    LogicCatalogue = "logic_catalogue", key name, object None;
    LogicExclusion = "logic_exclusion", key name, object None;
    Presentation = "presentation", key name, object None;
    LogicProperty = "logic_property", key name, object None;
    LogicProblem = "logic_problem", key name, object None;
    LogicRow = "logic_row", key name, object None;
    Machine = "machine", key name, object Some("machine");
    MachineBinding = "machine_binding", key name, object None;
    LanguageDomain = "language_domain", key name, object Some("language_domain");
    Measure = "measure", key name, object Some("measure");
    LanguageInterpretation = "language_interpretation", key name, object Some("language_interpretation");
    Language = "language", key name, object Some("language");
    ConsequenceInterpretation = "consequence_interpretation", key name, object Some("consequence_interpretation");
    ConsequenceSystem = "consequence_system", key name, object Some("consequence_system");
    ConsequenceMatrix = "consequence_matrix", key name, object None;
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
    Deprecation = "deprecation", key name, object None;
    Finding = "finding", key name, object None;
    ExpectedOpen = "expected_open", key name, object None;
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
/// A JSON value column holds its compact JSON text.
impl Col for serde_json::Value {
    fn sql(&self) -> Sql {
        Sql::Text(self.to_string())
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
pub mod consequence;
pub mod dag;
pub mod formal;
pub mod languages;
pub mod logic;
pub mod machines;
pub mod markings;
pub mod models;
pub mod records;
pub mod relational;
pub mod rooms;
pub mod values;

pub use artifacts::*;
pub use consequence::*;
pub use dag::*;
pub use formal::*;
pub use languages::*;
pub use logic::*;
pub use machines::*;
pub use markings::*;
pub use models::*;
pub use relational::*;
pub use rooms::*;
pub use values::*;

/// Views written after the tables: the group vectors, the language problems
/// ([`languages::LANGUAGE_VIEWS`]), the consequence problems
/// ([`consequence::CONSEQUENCE_VIEWS`]), then the marking views
/// ([`markings::MARKING_VIEWS`]).
pub const VIEWS: &[&str] = &[
    "CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, \
e.record_name, e.pos, e.child, s.summary, s.verdict \
FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' \
LEFT JOIN summary s ON s.problem = e.child;",
    languages::LANGUAGE_VIEWS[0],
    consequence::CONSEQUENCE_VIEWS[0],
    logic::LOGIC_VIEWS[0],
    logic::LOGIC_VIEWS[1],
    logic::LOGIC_VIEWS[2],
    logic::LOGIC_VIEWS[3],
    logic::LOGIC_VIEWS[4],
    markings::MARKING_VIEWS[0],
    markings::MARKING_VIEWS[1],
    markings::MARKING_VIEWS[2],
    markings::MARKING_VIEWS[3],
    markings::MARKING_VIEWS[4],
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
    // the explorer's status index (explore/table.js `problemIndex`) reads every problem's name,
    // kind, arity and expectation: a covering index, much narrower than the table's rows
    (
        "problems_status",
        "problems",
        &["name", "kind", "arity", "expect"],
    ),
    ("answers_problem", "answers", &["problem"]),
    ("problem_inputs_value", "problem_inputs", &["value"]),
    ("problem_inputs_cid", "problem_inputs", &["cid"]),
    ("instance_args_value", "instance_args", &["value"]),
    ("logic_audit_decl", "logic_audit", &["decl"]),
    ("rooms_institution", "rooms", &["institution"]),
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
        "findings_classification",
        "findings",
        &["classification", "problem"],
    ),
    ("findings_pointer", "findings", &["pointer"]),
    ("deprecated_problems_via", "deprecated_problems", &["via"]),
    (
        "deprecation_replacements_replacement",
        "deprecation_replacements",
        &["replacement"],
    ),
    ("machine_bindings_machine", "machine_bindings", &["machine"]),
    ("languages_domain", "languages", &["domain", "name"]),
    ("languages_decl", "languages", &["decl"]),
    ("languages_term", "languages", &["term"]),
    ("languages_identity", "languages", &["identity_hash"]),
    (
        "language_operands_operand",
        "language_operands",
        &["operand"],
    ),
    ("consequence_systems_term", "consequence_systems", &["term"]),
    (
        "consequence_systems_value",
        "consequence_systems",
        &["value"],
    ),
    (
        "consequence_operands_operand",
        "consequence_operands",
        &["operand"],
    ),
    ("instance_args_term", "instance_args", &["term"]),
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
        info::<Institution>(),
        info::<Comorphism>(),
        info::<Morphism>(),
        info::<Corridor>(),
        info::<LogicEdgeKind>(),
        info::<LogicFact>(),
        info::<LogicAudit>(),
        info::<HetsLogic>(),
        info::<HetsComorphism>(),
        info::<LogicPending>(),
        info::<LogicCatalogue>(),
        info::<LogicExclusion>(),
        info::<Presentation>(),
        info::<LogicProperty>(),
        info::<LogicProblem>(),
        info::<LogicRow>(),
        info::<Machine>(),
        info::<MachineBinding>(),
        info::<LanguageDomain>(),
        info::<Measure>(),
        info::<LanguageInterpretation>(),
        info::<Language>(),
        info::<LanguageOperand>(),
        info::<LanguageShapeRole>(),
        info::<ConsequenceInterpretation>(),
        info::<ConsequenceSystem>(),
        info::<ConsequenceOperand>(),
        info::<ConsequenceShapeRole>(),
        info::<ConsequenceMatrixCell>(),
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
        info::<DeprecationRow>(),
        info::<Replacement>(),
        info::<DeprecatedProblem>(),
        info::<FindingRow>(),
        info::<FindingVersion>(),
        info::<ExpectedOpenRow>(),
        info::<DeclLocation>(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn views_end_with_the_marking_views() {
        assert_eq!(
            &VIEWS[VIEWS.len() - markings::MARKING_VIEWS.len()..],
            markings::MARKING_VIEWS
        );
    }

    const LOC: &str = r#"{"decl": "B.b", "module": "B", "line": 3, "col": 0, "end_line": 4,
        "end_col": 9, "sel_line": 3, "sel_col": 8, "sel_end_line": 3, "sel_end_col": 11}"#;

    #[test]
    fn dumps_with_and_without_locations() {
        // v0.1: no `locations`
        let old: Dump = serde_json::from_str(
            r#"{"schema": "silmaril.project-dump.v0.1", "toolchain": "4", "records": []}"#,
        )
        .unwrap();
        assert!(DUMP_SCHEMAS.contains(&old.schema.as_str()));
        assert!(old.locations.is_empty());
        // v0.2: the locations, in any order and with a repeat, become one row per decl
        let text = format!(
            r#"{{"schema": "{DUMP_SCHEMA}", "toolchain": "4", "locations": [{LOC},
            {{"decl": "A.a", "module": "A", "line": 1, "col": 2, "end_line": 1, "end_col": 30,
              "sel_line": 1, "sel_col": 6, "sel_end_line": 1, "sel_end_col": 9}}, {LOC}]}}"#
        );
        let new: Dump = serde_json::from_str(&text).unwrap();
        assert_eq!(new.locations.len(), 3);
        let rows = location_rows(&new.locations);
        let decls: Vec<&str> = rows.iter().map(|r| r.decl.as_str()).collect();
        assert_eq!(decls, ["A.a", "B.b"]);
        assert_eq!(
            rows[1].row(),
            [
                Sql::Text("B.b".into()),
                Sql::Text("B".into()),
                Sql::Int(3),
                Sql::Int(0),
                Sql::Int(4),
                Sql::Int(9),
                Sql::Int(3),
                Sql::Int(8),
                Sql::Int(3),
                Sql::Int(11),
            ]
        );
        let cols: Vec<&str> = DeclLocation::COLUMNS.iter().map(|c| c.0).collect();
        assert_eq!(
            cols,
            [
                "decl",
                "module",
                "line",
                "col",
                "end_line",
                "end_col",
                "sel_line",
                "sel_col",
                "sel_end_line",
                "sel_end_col"
            ]
        );
        // a location with an unknown key is rejected
        let bad = LOC.replace("\"col\"", "\"column\"");
        assert!(serde_json::from_str::<DeclLocation>(&bad).is_err());
    }

    #[test]
    fn expected_open_reasons_match_the_check_constraint() {
        let (_, ty) = ExpectedOpenRow::COLUMNS
            .iter()
            .find(|(c, _)| *c == "reason")
            .unwrap();
        let quoted: Vec<String> = EXPECTED_OPEN_REASONS
            .iter()
            .map(|r| format!("'{r}'"))
            .collect();
        assert_eq!(
            *ty,
            format!("TEXT NOT NULL CHECK(reason IN ({}))", quoted.join(","))
        );
        let r: Record = serde_json::from_str(
            r#"{"kind": "expected_open", "name": "p", "module": "M", "reason": "consistency",
                "note": "n", "pointer": "u"}"#,
        )
        .unwrap();
        assert_eq!((r.kind(), r.key()), ("expected_open", "p"));
    }
}
