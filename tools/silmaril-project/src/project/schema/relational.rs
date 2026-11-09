//! Layer 1, relational problems: `predicate`, `answer` and `instance` records and their
//! argument tables.
use super::*;
use serde::Deserialize;

/// `@[predicate "NAME"]` or `silmaril problem NAME := d`: a problem
/// `P : α₀ → … → αₙ₋₁ → Prop` (arity 0 also appears in the dump's `problems`).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Predicate {
    pub name: String,
    pub module: String,
    pub decl: String,
    pub arity: i64,
    #[serde(default)]
    pub args: Vec<Arg>,
    /// The room the problem lives in (`silmaril problem N in R := φ`).
    pub room: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Arg {
    pub pos: i64,
    /// `None` for an anonymous binder.
    pub name: Option<String>,
    pub r#type: String,
}

/// `@[answers "NAME" s]`: a theorem of the shape of status `s` (Lean checked the shape).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Answer {
    /// The problem.
    pub name: String,
    pub module: String,
    pub decl: String,
    /// `THM` | `SAT` | `UNS` | `CSA`.
    pub status: String,
    /// Pretty-printed witnesses of a literal `Exists.intro` chain (SAT, CSA).
    pub witness: Option<Vec<String>>,
    #[serde(default)]
    pub axioms: Vec<String>,
}

/// `silmaril instance NAME := GENERAL (args…)`. The instance is itself a problem (declared by
/// its own `predicate` record or `problems` entry); this record adds the `instance` edge.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Instance {
    pub name: String,
    pub module: String,
    /// The general problem.
    pub of: String,
    pub decl: String,
    #[serde(default)]
    pub args: Vec<InstanceArg>,
}

/// A fixed argument: a Lean term, a registered value, or a blob (CID).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstanceArg {
    pub pos: i64,
    pub term: Option<String>,
    pub value: Option<String>,
    pub cid: Option<String>,
}

table! {
    ProblemArg = "problem_args", key("problem", "pos") {
        problem: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        name: Option<String> = "TEXT",
        r#type: String = "TEXT NOT NULL",
    }
}

table! {
    InstanceArgRow = "instance_args", key("problem", "pos") {
        problem: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        term: Option<String> = "TEXT",
        value: Option<String> = "TEXT",
        cid: Option<String> = "TEXT",
    }
}
