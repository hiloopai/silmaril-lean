//! Native decision procedures and axioms: the trust lines (`silmaril.trust.v1` and
//! `silmaril.trust-adapter.v0.1`) and their tables.
//!
//! The model is the core trust framework's (`Silmaril.Prelude.Trust`, `docs/trust.md`):
//!
//! - a **procedure** (`native_decider`) is a named closed `Bool` function; `edge_decide` proves
//!   `f a₁ … aₙ = true` with it, natively (adding the axiom
//!   `<decl>._native.edge.<procedure>.ax_i_j`) or, when it has a kernel fallback, in the kernel;
//! - a **trust set** (`trust_set`, or `standard` in `policy.toml`) names procedures or axioms,
//!   includes other sets, or is `all`; `all` and `none` are built in;
//! - a **scope** (`[[native.scope]]` in `policy.toml`) applies to a module and everything under
//!   it and sets `max`, `default`, `deps` and `axioms`, inheriting what it omits;
//! - a **use** is one `edge_decide`: declaration, module, procedure, native or kernel, profile,
//!   and the native axiom;
//! - per theorem, its axioms (`collectAxioms`, which is transitive), split as the core's
//!   `trust_audit` splits them.
//!
//! The lines are written by `sil project trust-dump` (the core's `#trust_dump`, schema
//! [`CORE_SCHEMA`], plus adapter lines, schema [`ADAPTER_SCHEMA`]) or by hand (fixtures, whose
//! header says so). Every line is one JSON object with a `schema` and a `kind`; each schema may
//! carry only the kinds of [`LINE_KINDS`], and each is converted explicitly.
use super::*;
use serde::Deserialize;

/// The core's provenance schema (`docs/trust.md`, `#trust_dump`).
pub const CORE_SCHEMA: &str = "silmaril.trust.v1";
/// Lines the adapter (`sil project trust-dump`) adds, and lines of a core before v1.
pub const ADAPTER_SCHEMA: &str = "silmaril.trust-adapter.v0.1";
/// `(schema, kinds)`: which kinds each line schema may carry.
pub const LINE_KINDS: &[(&str, &[&str])] = &[
    (
        CORE_SCHEMA,
        &[
            "procedure",
            "use",
            "set",
            "scope",
            "declared_procedure",
            "audit",
        ],
    ),
    (
        ADAPTER_SCHEMA,
        &[
            "header",
            "input",
            "policy",
            "scope",
            "set",
            "procedure",
            "use",
            "module",
            "effective",
            "decl",
            "excluded",
        ],
    ),
];

/// One line of a trust dump.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TrustLine {
    Header(LineHeader),
    Input(LineInput),
    Policy(LinePolicy),
    Scope(LineScope),
    Set(LineSet),
    Procedure(LineProcedure),
    Use(LineUse),
    Module(LineModule),
    Effective(LineEffective),
    Decl(LineDecl),
    Excluded(LineExcluded),
    DeclaredProcedure(LineDeclaredProcedure),
    Audit(LineAudit),
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineHeader {
    /// The core API the driver read: `v1` (`#trust_dump`) or `legacy` (core before v1).
    pub core_api: String,
    /// `Lean.versionString` of the producer.
    pub toolchain: String,
    /// The profile and ceiling the effective sets were computed for.
    pub profile: String,
    pub ceiling: String,
    /// What wrote the lines (`sil project trust-dump` adds itself; a fixture says so).
    pub producer: Option<String>,
    /// `lean` (a producer run) or `fixture` (hand-written). Self-declared.
    pub origin: Option<String>,
    /// Module prefixes the dump describes; imports outside them are `external`.
    #[serde(default)]
    pub roots: Vec<String>,
}

/// A file the dump depends on, by digest at dump time (`lean-toolchain`, `policy.toml`, …).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineInput {
    pub path: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LinePolicy {
    /// As given to `trust_policy` (relative to the loading module).
    pub file: String,
    /// The core's FNV-1a pin of the file.
    pub pin: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineScope {
    pub module: String,
    pub max: Option<String>,
    pub default: Option<String>,
    pub deps: Option<String>,
    pub axioms: Option<String>,
    pub policy_file: Option<String>,
    pub policy_pin: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineSet {
    pub name: String,
    #[serde(default)]
    pub all: bool,
    /// `trust_set` or `policy`.
    pub origin: Option<String>,
    #[serde(default)]
    pub members: Vec<String>,
    #[serde(default)]
    pub includes: Vec<String>,
    /// The core's resolution (`"all"` or names); checked against ours.
    pub resolved: Option<serde_json::Value>,
}

/// `native_decider name := function [with_kernel_fallback] [native f via eq] [format … sound …]`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineProcedure {
    pub name: String,
    pub function: String,
    pub kernel_fallback: bool,
    pub module: String,
    pub format: Option<String>,
    pub sound: Option<String>,
    pub native_function: Option<String>,
    pub native_eq: Option<String>,
    #[serde(default)]
    pub doc: String,
}

/// A checker and its soundness theorem.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LinePair {
    pub check: String,
    pub sound: String,
}

/// A declared two-backend procedure (`ProcDecl`, run by `sil_check`).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineDeclaredProcedure {
    pub name: String,
    pub constant: String,
    pub native: Option<LinePair>,
    pub kernel: Option<LinePair>,
    pub format: Option<String>,
    #[serde(default)]
    pub doc: String,
}

/// A `trust_audit` result (the core's; checked against the adapter's `decl` line).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineAudit {
    pub decl: String,
    pub module: String,
    pub profile: String,
    #[serde(default)]
    pub own_native: Vec<String>,
    #[serde(default)]
    pub dep_native: Vec<String>,
    #[serde(default)]
    pub native_axioms: Vec<String>,
    #[serde(default)]
    pub axioms: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineUse {
    pub decl: String,
    pub module: String,
    pub procedure: String,
    /// `native` | `kernel`.
    pub mode: String,
    pub profile: String,
    pub axiom: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineModule {
    pub name: String,
    #[serde(default)]
    pub imports: Vec<String>,
    pub source: Option<String>,
    pub source_sha256: Option<String>,
}

/// A resolved set: `{"all": true}` or `{"all": false, "names": […]}`.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LineMembers {
    pub all: bool,
    #[serde(default)]
    pub names: Vec<String>,
}

/// The core's `effective` sets of a module and `allowed` for the header's profile and ceiling.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineEffective {
    pub module: String,
    pub max: Option<LineMembers>,
    pub default: Option<LineMembers>,
    pub deps: Option<LineMembers>,
    pub axioms: Option<LineMembers>,
    pub allowed: Option<LineMembers>,
    #[serde(default)]
    pub trace: Vec<String>,
    /// The core could not resolve the policy for this module.
    pub error: Option<String>,
}

/// The core's `axiomReport` of a theorem.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineDecl {
    pub decl: String,
    pub module: String,
    #[serde(default)]
    pub own_native: Vec<String>,
    #[serde(default)]
    pub dep_native: Vec<String>,
    /// Tactics of native runs outside `edge_decide` (`decide +native`, `bv_decide`).
    #[serde(default)]
    pub plain_native: Vec<String>,
    /// Axioms that are not native runs.
    #[serde(default)]
    pub axioms: Vec<String>,
    #[serde(default)]
    pub native_axioms: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LineExcluded {
    pub module: String,
    /// `excluded` | `unsupported`.
    pub coverage: String,
    pub reason: String,
}

// ---------------------------------------------------------------- tables

table! {
    /// Files the dump depends on, with the recorded and the current digest.
    TrustInput = "trust_inputs", key("path") {
        path: String = "TEXT NOT NULL",
        sha256: String = "TEXT NOT NULL",
        disk_sha256: Option<String> = "TEXT",
        status: String = "TEXT NOT NULL CHECK(status IN ('match','changed','missing'))",
    }
}

table! {
    /// Registered procedures: `native_decider`s (`function`, a kernel fallback, an optional
    /// separate native implementation) and declared two-backend procedures (`ProcDecl`: a
    /// native and a kernel checker, each with a soundness theorem, for the same proposition).
    TrustProcedure = "trust_procedures", key("name") {
        name: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('native_decider','declared'))",
        function: String = "TEXT NOT NULL",
        module: Option<String> = "TEXT",
        kernel_fallback: bool = "INTEGER NOT NULL",
        native_function: Option<String> = "TEXT",
        native_eq: Option<String> = "TEXT",
        native_check: Option<String> = "TEXT",
        native_sound: Option<String> = "TEXT",
        kernel_check: Option<String> = "TEXT",
        kernel_sound: Option<String> = "TEXT",
        format: Option<String> = "TEXT",
        sound: Option<String> = "TEXT",
        doc: String = "TEXT NOT NULL",
    }
}

table! {
    /// `origin`: `builtin` (`all`, `none`), `policy` or `trust_set`.
    TrustSet = "trust_sets", key("name") {
        name: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL",
        is_all: bool = "INTEGER NOT NULL",
    }
}

table! {
    /// `member_kind = 'name'`: a procedure or axiom name; `'set'`: an included set.
    TrustSetMember = "trust_set_members", key("set_name", "member_kind", "member") {
        set_name: String = "TEXT NOT NULL",
        member_kind: String = "TEXT NOT NULL CHECK(member_kind IN ('name','set'))",
        member: String = "TEXT NOT NULL",
    }
}

table! {
    /// `[[native.scope]]`: a module and everything under it. `NULL` inherits.
    TrustScope = "trust_scopes", key("module") {
        module: String = "TEXT NOT NULL",
        max: Option<String> = "TEXT",
        default_set: Option<String> = "TEXT",
        deps: Option<String> = "TEXT",
        axioms: Option<String> = "TEXT",
    }
}

table! {
    /// Every module the dump describes or that a described module imports.
    /// `freshness = consistent` when the recorded digests this module's facts depend on (its
    /// source, its described imports' sources, the inputs) still match: evidence of nothing more.
    TrustModule = "trust_modules", key("name") {
        name: String = "TEXT NOT NULL",
        source: Option<String> = "TEXT",
        source_sha256: Option<String> = "TEXT",
        source_status: String = "TEXT NOT NULL CHECK(source_status IN ('match','changed','missing','unrecorded'))",
        freshness: String = "TEXT NOT NULL CHECK(freshness IN ('consistent','stale','unknown'))",
        coverage: String = "TEXT NOT NULL CHECK(coverage IN ('covered','excluded','unsupported','undescribed','external'))",
        policy_trace: Option<String> = "TEXT",
        reason: Option<String> = "TEXT",
    }
}

table! {
    TrustImport = "trust_imports", key("module", "import") {
        module: String = "TEXT NOT NULL",
        import: String = "TEXT NOT NULL",
    }
}

table! {
    /// The effective sets of a module (`max`, `default`, `deps`, `axioms`, and `allowed` for
    /// the dump's profile and ceiling). `member = '*'` is `all`.
    TrustModulePolicy = "trust_module_policy", key("module", "role", "member") {
        module: String = "TEXT NOT NULL",
        role: String = "TEXT NOT NULL CHECK(role IN ('max','default','deps','axioms','allowed'))",
        member: String = "TEXT NOT NULL",
    }
}

table! {
    /// Recorded `edge_decide` runs. `axiom = ''` for a kernel run.
    TrustUse = "trust_uses", key("module", "decl", "procedure", "mode", "profile", "axiom") {
        module: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        procedure: String = "TEXT NOT NULL",
        mode: String = "TEXT NOT NULL CHECK(mode IN ('native','kernel'))",
        profile: String = "TEXT NOT NULL",
        axiom: String = "TEXT NOT NULL",
        /// For a kernel run: `fallback` (the kernel evaluates the native function), `declared`
        /// (the declared kernel checker), or `unregistered` (a kernel checker the registry does
        /// not name: the run adds no axiom, but its identity is not auditable).
        kernel_side: String = "TEXT NOT NULL CHECK(kernel_side IN ('','fallback','declared','unregistered'))",
    }
}

table! {
    /// Theorems the dump audited (also those without axioms).
    TrustDecl = "trust_decls", key("decl") {
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
    }
}

table! {
    /// The axioms of a theorem (transitive), split as the core's audit splits them:
    /// `own_native` and `dep_native` (an `edge_decide` run in the declaration, or inherited),
    /// `plain_native` (a native run outside `edge_decide`) and `other`. `procedure` is the
    /// native procedure or tactic (`''` for `other`).
    TrustDeclAxiom = "trust_decl_axioms", key("module", "decl", "axiom") {
        module: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        axiom: String = "TEXT NOT NULL",
        class: String = "TEXT NOT NULL CHECK(class IN ('own_native','dep_native','plain_native','other'))",
        procedure: String = "TEXT NOT NULL",
    }
}

/// The trust views, written after the core views. Transitive relations are recursive queries;
/// `UNION` keeps them finite on cyclic data.
pub const TRUST_VIEWS: &[&str] = &[
    "CREATE VIEW trust_set_closure AS WITH RECURSIVE c(set_name, member_kind, member) AS (\
SELECT set_name, member_kind, member FROM trust_set_members \
UNION SELECT c.set_name, m.member_kind, m.member FROM c \
JOIN trust_set_members m ON c.member_kind = 'set' AND m.set_name = c.member) \
SELECT set_name, member AS name FROM c WHERE member_kind = 'name' \
UNION SELECT name, '*' FROM trust_sets WHERE is_all = 1 \
UNION SELECT c.set_name, '*' FROM c JOIN trust_sets s ON c.member_kind = 'set' AND s.name = c.member AND s.is_all = 1;",
    "CREATE VIEW trust_module_deps AS WITH RECURSIVE d(module, dep) AS (\
SELECT module, import FROM trust_imports \
UNION SELECT d.module, i.import FROM d JOIN trust_imports i ON i.module = d.dep) \
SELECT module, dep FROM d;",
    "CREATE VIEW trust_coverage_gaps AS SELECT d.module, d.dep, m.coverage, m.reason FROM trust_module_deps d \
JOIN trust_modules m ON m.name = d.dep WHERE m.coverage NOT IN ('covered','external');",
    "CREATE VIEW trust_module_native AS SELECT module, procedure, class, count(DISTINCT decl) AS decls \
FROM trust_decl_axioms WHERE class IN ('own_native','dep_native','plain_native') GROUP BY module, procedure, class;",
    "CREATE VIEW trust_violations AS \
SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'own-native-not-allowed' AS reason FROM trust_decl_axioms x \
JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'own_native' \
AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'allowed' AND p.member IN (x.procedure, '*')) \
UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'dep-native-outside-deps' FROM trust_decl_axioms x \
JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'dep_native' \
AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'deps' AND p.member IN (x.procedure, '*')) \
UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'unregistered-native' FROM trust_decl_axioms x \
JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'plain_native' \
UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'axiom-outside-set' FROM trust_decl_axioms x \
JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'other' \
AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'axioms' AND p.member IN (x.axiom, '*'));",
];
