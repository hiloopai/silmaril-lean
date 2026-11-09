//! Layer 3, formats and values: `format`, `format_default`, `format_law` and `value` records,
//! the value sources and the problem inputs.
use super::*;
use serde::Deserialize;

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Source {
    /// The blob (resolved by Lean from a path, CID or registry name).
    pub cid: String,
    pub path: Option<String>,
    pub package: Option<String>,
    /// The resolved format name.
    pub format: String,
    pub decl: String,
}

table! {
    /// `silmaril format NAME := decl`; Lean fills `input` (an artifact type), `value_type` and
    /// `printer`.
    Format = "formats", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        input: String = "TEXT NOT NULL",
        value_type: String = "TEXT NOT NULL",
        base: Option<String> = "TEXT",
        printer: bool = "INTEGER NOT NULL",
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril format_default FAMILY := FORMAT`: `name` is the family.
    FormatDefault = "format_defaults", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        format: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril format_law FORMAT roundtrip|sound := proof (rel := …)`; `name` is the proof.
    FormatLaw = "format_laws", key("name") {
        name: String = "TEXT NOT NULL",
        format: String = "TEXT NOT NULL",
        law: String = "TEXT NOT NULL CHECK(law IN ('roundtrip','sound'))",
        proof: String = "TEXT NOT NULL",
        rel: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// `silmaril value X : F := SOURCE (| F' := SOURCE')*`; Lean resolves the formats and
    /// fills the obligations (`parses` for source 0, `agrees[k-1]` for source k).
    Value = "value_defs", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        format: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        parses: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra {
        #[serde(default)] agrees: Vec<String>,
        /// Table `value_sources`.
        sources: Vec<Source>,
        #[serde(rename = "sid")] sid_override: Option<String>,
    }
}

table! {
    /// Source `pos` of a value (by CID); its obligation is `parses` (pos 0) or `agrees[pos-1]`.
    ValueSource = "value_sources", key("value", "pos") {
        value: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        cid: String = "TEXT NOT NULL",
        format: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        obligation: String = "TEXT NOT NULL",
    }
}

table! {
    /// The judgement's values and artifacts (exactly one of `value`, `cid` per row).
    ProblemInput = "problem_inputs", key("problem", "pos") {
        problem: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        value: Option<String> = "TEXT",
        cid: Option<String> = "TEXT",
    }
}
