//! Formal rows: a logic's presentations, the roles of its theorems (soundness, consistency, …),
//! its concrete problems, and the row that groups them (Lean:
//! `Silmaril.Project.Registry.Formal.Defs`; docs/projects/formal-rows.md). Lean checked every
//! claim from the theorems' types and computed each problem's S-expression; the rows keep what
//! Lean filled in.
use super::*;

/// The roles of `logic_property` (Lean's `propertyRoles`).
pub const PROPERTY_ROLES: [&str; 5] = [
    "soundness",
    "consistency",
    "nontriviality",
    "satisfiability",
    "inclusion",
];

table! {
    /// `silmaril presentation N := c`: a named, versioned S-expression presentation
    /// (`SExpCodec`) of an abstract syntax (`abstract`), with the codec's own `codec_name` and
    /// `codec_version`, and whether it is a row's default (`is_default`).
    Presentation = "presentations", key("name") {
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        #[serde(rename = "abstract")] abstract_type: String = "TEXT NOT NULL",
        codec_name: String = "TEXT NOT NULL",
        codec_version: String = "TEXT NOT NULL",
        #[serde(rename = "default")] is_default: bool = "INTEGER NOT NULL",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// `silmaril logic_property N := t (role := r) (system := S)`: a theorem whose statement Lean
    /// checked against its role for the registered system `S` (and `target`, for an inclusion),
    /// at `arg` when given; `statement` is the type, `axioms` its axioms (JSON), and the role's
    /// parts (`interpretation`, `falsity`, `context`).
    LogicProperty = "logic_properties", key("name") {
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        role: String = "TEXT NOT NULL CHECK(role IN ('soundness','consistency','nontriviality','satisfiability','inclusion'))",
        system: Option<String> = "TEXT",
        target: Option<String> = "TEXT",
        arg: Option<String> = "TEXT",
        statement: String = "TEXT NOT NULL",
        interpretation: Option<String> = "TEXT",
        falsity: Option<String> = "TEXT",
        context: Option<String> = "TEXT",
        #[serde(default)] axioms: serde_json::Value = "TEXT NOT NULL",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// `silmaril logic_problem N := φ (presentation := P)`: a concrete sentence, its
    /// S-expression in `P` (`sexp`, computed by Lean) and in every registered presentation of the
    /// same abstract syntax (`renderings`, JSON `{presentation: text}`), and its claims, each checked by Lean to
    /// be about `φ`: `derived` (by `system`), `entailed` (by `entailed_by`), `truth` (in a model
    /// of `interpretation`); each is JSON with the proof, statement and axioms.
    LogicProblem = "logic_problems", key("name") {
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        presentation: String = "TEXT NOT NULL",
        sexp: String = "TEXT NOT NULL",
        #[serde(default)] renderings: serde_json::Value = "TEXT NOT NULL",
        sentence: String = "TEXT NOT NULL",
        system: Option<String> = "TEXT",
        entailed_by: Option<String> = "TEXT",
        interpretation: Option<String> = "TEXT",
        #[serde(default)] derived: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] entailed: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] truth: serde_json::Value = "TEXT NOT NULL",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// `silmaril logic_row N`: a logic's row: its systems, interpretations (Lean declarations),
    /// presentations, properties and problems (JSON lists of names), the logic-graph
    /// `institution` it is, its exact `variant`, and its place in the table (`row_order`).
    LogicRow = "logic_rows", key("name") {
        name: String = "TEXT NOT NULL",
        title: String = "TEXT NOT NULL",
        variant: Option<String> = "TEXT",
        institution: Option<String> = "TEXT",
        #[serde(default)] systems: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] interpretations: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] presentations: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] properties: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] problems: serde_json::Value = "TEXT NOT NULL",
        #[serde(rename = "order")] row_order: Option<i64> = "INTEGER",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}
