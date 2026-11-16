//! Layer 5, consequence systems: `consequence_system` records (Lean:
//! `Silmaril.Project.Registry.Consequence.Defs`), their tables, and the view that relates the
//! standard consequence problems (`silmaril.shapes.consequence.*`) to the systems they are
//! about (docs/projects/consequence-systems.md).
//!
//! A system is a relation `S : Ax → C → Prop` (`Γ ⊢ φ`). Lean checks the types (operands of a
//! construction must have definitionally equal context and conclusion types) and generates
//! the definition of a construction; the rows keep what Lean filled in. What is true of a
//! system (universal, sound for another, …) is a problem with answers, never a column here.
use super::*;

/// The operations of `consequence_system` (Lean's `consequenceOps`).
pub const CONSEQUENCE_OPS: [&str; 6] = ["decl", "union", "inter", "diff", "erase", "artifact"];

/// The standard consequence shapes: `(problem, role of each argument position)`. The roles
/// name what an instance argument is: a type (`type`), the system asked about (`S`), the
/// system it is compared with or translated into (`T`), a translation on contexts (`f`) or
/// conclusions (`g`), the chosen conclusion (`ff`), a context (`ctx`) or a conclusion (`phi`),
/// a measure (`mu`) and its bound (`b`), or a Gentzen rule profile (`rules`).
pub const CONSEQUENCE_SHAPES: &[(&str, &[&str])] = &[
    (
        "silmaril.shapes.consequence.derives",
        &["type", "type", "S", "ctx", "phi"],
    ),
    (
        "silmaril.shapes.consequence.context_universal",
        &["type", "type", "S", "ctx"],
    ),
    (
        "silmaril.shapes.consequence.derives_bottom",
        &["type", "type", "S", "ff", "ctx"],
    ),
    (
        "silmaril.shapes.consequence.sound_at",
        &["type", "type", "S", "T", "ctx", "phi"],
    ),
    (
        "silmaril.shapes.consequence.complete_at",
        &["type", "type", "S", "T", "ctx", "phi"],
    ),
    (
        "silmaril.shapes.consequence.complete_within_at",
        &["type", "type", "S", "T", "mu", "b", "ctx", "phi"],
    ),
    ("silmaril.shapes.consequence.tarski_closed", &["type", "S"]),
    (
        "silmaril.shapes.consequence.gentzen_closed",
        &["type", "rules", "S"],
    ),
    (
        "silmaril.shapes.consequence.artifact_defined",
        &["type", "type", "type", "type", "X", "I", "e"],
    ),
    (
        "silmaril.shapes.consequence.context_free",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.conclusion_free",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.supported_ax",
        &["type", "type", "S", "tt"],
    ),
    (
        "silmaril.shapes.consequence.supported_c",
        &["type", "type", "S", "ff"],
    ),
    (
        "silmaril.shapes.consequence.ctx_perm_inv",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.ctx_set_inv",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.ctx_up_closed",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.ctx_append_extensive",
        &["type", "type", "S"],
    ),
    (
        "silmaril.shapes.consequence.translates_at",
        &[
            "type", "type", "type", "type", "S", "T", "f", "g", "ctx", "phi",
        ],
    ),
    (
        "silmaril.shapes.consequence.reflects_at",
        &[
            "type", "type", "type", "type", "S", "T", "f", "g", "ctx", "phi",
        ],
    ),
];

table! {
    /// `silmaril consequence_system NAME …`; Lean generates or checks `decl` and fills `term`
    /// and the typed shape (`ctx_kind`, `ctx_elem`, `ctx_signed`, the same for conclusions, and
    /// `raw_sequent`; null in a dump written before they existed)
    /// (`decl` as instance arguments print it) and `contexts` and `conclusions` (the types `Ax`
    /// and `C`, printed). `room` names the registered room whose sentences the system relates
    /// (`room_at`: its arguments; `room_term`: the room, printed; `room_lift`: sentences are
    /// `ULift` of the conclusions), checked by Lean; `reading` is `semantic` (checked to be the
    /// room's consequence) or `derivability`.
    ConsequenceSystem = "consequence_systems", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        op: String = "TEXT NOT NULL CHECK(op IN ('decl','union','inter','diff','erase','artifact'))",
        decl: String = "TEXT NOT NULL",
        term: String = "TEXT NOT NULL",
        contexts: String = "TEXT NOT NULL",
        conclusions: String = "TEXT NOT NULL",
        witness: Option<String> = "TEXT",
        value: Option<String> = "TEXT",
        interpretation: Option<String> = "TEXT",
        env_term: Option<String> = "TEXT",
        ctx_kind: Option<String> = "TEXT CHECK(ctx_kind IN ('unit','list','finset','set','other'))",
        ctx_elem: Option<String> = "TEXT",
        ctx_signed: Option<bool> = "INTEGER",
        concl_kind: Option<String> = "TEXT CHECK(concl_kind IN ('unit','list','finset','set','other'))",
        concl_elem: Option<String> = "TEXT",
        concl_signed: Option<bool> = "INTEGER",
        raw_sequent: Option<bool> = "INTEGER",
        room: Option<String> = "TEXT",
        room_at: Option<String> = "TEXT",
        room_term: Option<String> = "TEXT",
        room_lift: Option<bool> = "INTEGER",
        reading: Option<String> = "TEXT CHECK(reading IN ('derivability','semantic'))",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        source: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra {
        /// Table `consequence_operands`: the operands of `union`, `inter` and `diff`.
        #[serde(default)] args: Vec<String>,
        #[serde(rename = "sid")] sid_override: Option<String>,
    }
}

table! {
    /// `silmaril consequence_interpretation NAME := I (abi := A) (environment := E)`, with
    /// `I : V → System Ax C` (`definedness` total) or `I : Interp Env V Ax C` (partial, under
    /// the configuration type `env`); Lean checks that `A` and `E` occur in `I`'s definition and fills
    /// `input` (`V`), `contexts` and `conclusions`. A system `op := artifact` reads a registered
    /// value through one.
    ConsequenceInterpretation = "consequence_interpretations", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        input: String = "TEXT NOT NULL",
        contexts: String = "TEXT NOT NULL",
        conclusions: String = "TEXT NOT NULL",
        abi: Option<String> = "TEXT",
        environment: Option<String> = "TEXT",
        definedness: Option<String> = "TEXT CHECK(definedness IN ('total','partial'))",
        env: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril consequence_matrix NAME := rows`: one row per cell of an evidence matrix (the
    /// protocol track's `SignedMatrix.cells`), copied verbatim. `theorems` is the JSON list of the
    /// listed declarations with their modules; Lean checked only that they exist.
    ConsequenceMatrixCell = "consequence_matrix_cells", key("name") {
        name: String = "TEXT NOT NULL",
        matrix: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        variant: String = "TEXT NOT NULL",
        reading: String = "TEXT NOT NULL",
        reading_module: String = "TEXT NOT NULL",
        theorems: serde_json::Value = "TEXT NOT NULL",
        evidence: String = "TEXT NOT NULL",
        strength: String = "TEXT NOT NULL",
        note: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// Operand `pos` of a constructed consequence system.
    ConsequenceOperand = "consequence_operands", key("system", "pos") {
        system: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        operand: String = "TEXT NOT NULL",
    }
}

table! {
    /// The roles of the arguments of the standard consequence shapes ([`CONSEQUENCE_SHAPES`]).
    ConsequenceShapeRole = "consequence_shape_roles", key("shape", "pos") {
        shape: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        role: String = "TEXT NOT NULL",
    }
}

/// The view `consequence_problems`: one row per argument of an instance of a standard
/// consequence shape that names a registered system (by its defining constant as instance
/// arguments print it, `term`: `«silmaril».x` for a generated `silmaril.x`), with the
/// instance's shape, role (`S` or `T`), expected status, summary and verdict.
pub const CONSEQUENCE_VIEWS: &[&str] = &[
    "CREATE VIEW consequence_problems AS SELECT i.problem AS problem, e.parent AS shape, \
r.role AS role, i.pos AS pos, c.name AS system, p.expect AS expect, p.title AS title, \
s.summary AS summary, s.verdict AS verdict \
FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' \
JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos \
JOIN consequence_systems c ON c.term = i.term \
JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;",
];

/// The rows of `consequence_shape_roles`.
pub fn consequence_role_rows() -> Vec<ConsequenceShapeRole> {
    CONSEQUENCE_SHAPES
        .iter()
        .flat_map(|(shape, roles)| {
            roles
                .iter()
                .enumerate()
                .map(|(pos, role)| ConsequenceShapeRole {
                    shape: (*shape).into(),
                    pos: pos as i64,
                    role: (*role).into(),
                })
        })
        .collect()
}
