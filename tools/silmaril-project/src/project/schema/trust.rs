//! Decision-procedure and axiom trust: the trust dump (`silmaril.trust-dump.v0.1`) and its
//! tables.
//!
//! The trust dump is a separate input (`sil project sqlite --trust PATH`), written by the
//! library's trust-policy tooling, not by `#silmaril_dump`. It describes:
//!
//! - **procedures**: backend-independent identities of what may be trusted (an axiom, or a
//!   decision procedure for a proposition);
//! - **implementations**: how a decision procedure is checked (`kernel` or `native`, with a
//!   profile), and whether that implementation exists (`implemented = false` is a registry
//!   entry, not a claim);
//! - **sets**: named, hierarchical sets of `(procedure, backend, profile)` grants;
//! - **policies**: `allow` and `max` sets per scope (root, region, module prefix, module);
//! - **modules**: source digests and direct import edges;
//! - **uses**: direct uses, per declaration, with the backend and profile actually used and the
//!   axioms Lean reported for that use;
//! - **decls**: optionally, every axiom of a declaration, to find axioms no use accounts for;
//! - **excluded**: modules whose uses are not recorded (`excluded`, `unsupported`).
//!
//! Transitive uses are not stored: the views in [`super::VIEWS`] compute them with
//! `WITH RECURSIVE` over `trust_imports` and `trust_set_members`.
use super::*;
use serde::Deserialize;

pub const TRUST_SCHEMA: &str = "silmaril.trust-dump.v0.1";

/// The axioms every root policy allows unless the trust dump says otherwise: the procedures
/// of the built-in set [`STANDARD_SET`]. A policy default, not evidence about uses.
pub const STANDARD_SET: &str = "standard";

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustDump {
    pub schema: String,
    /// The Lean toolchain the uses were collected with (the `lean-toolchain` line).
    pub toolchain: String,
    /// The tool that wrote the dump, with its version.
    pub producer: String,
    /// Files the dump depends on besides module sources (policy files, manifests), by digest.
    #[serde(default)]
    pub inputs: Vec<TrustInputDecl>,
    #[serde(default)]
    pub procedures: Vec<ProcedureDecl>,
    #[serde(default)]
    pub implementations: Vec<ImplementationDecl>,
    #[serde(default)]
    pub sets: Vec<SetDecl>,
    #[serde(default)]
    pub policies: Vec<PolicyDecl>,
    #[serde(default)]
    pub modules: Vec<ModuleDecl>,
    #[serde(default)]
    pub uses: Vec<UseDecl>,
    /// `None`: axioms per declaration were not collected (unattributed axioms are unchecked).
    pub decls: Option<Vec<DeclDecl>>,
    #[serde(default)]
    pub excluded: Vec<ExcludedDecl>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustInputDecl {
    /// Relative to the project directory.
    pub path: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProcedureDecl {
    pub name: String,
    /// `axiom` | `decision`.
    pub kind: String,
    /// The proposition decided, as text (decision procedures).
    pub proposition: Option<String>,
    pub doc: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ImplementationDecl {
    pub procedure: String,
    /// `kernel` | `native`.
    pub backend: String,
    /// `None`: the backend's default profile.
    pub profile: Option<String>,
    /// The Lean declaration that realizes it.
    pub decl: Option<String>,
    pub implemented: bool,
    /// What is trusted beyond the kernel (native: the compiled code path and runtime).
    pub surface: Option<String>,
    pub doc: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SetDecl {
    pub name: String,
    pub doc: Option<String>,
    #[serde(default)]
    pub members: Vec<MemberDecl>,
}

/// `{ procedure, backend?, profile? }` or `{ set }`. A procedure member grants one backend:
/// by default `axiom` for an axiom and `kernel` for a decision procedure; no profile grants
/// every profile of that backend.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MemberDecl {
    pub procedure: Option<String>,
    pub backend: Option<String>,
    pub profile: Option<String>,
    pub set: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PolicyDecl {
    /// `root` | `region` | `prefix` | `module`.
    pub scope: String,
    /// `""` for the root, a region, `A.B.*`, or a module.
    #[serde(default)]
    pub name: String,
    /// `None`: inherited.
    pub allow: Option<Vec<String>>,
    /// `None`: inherited.
    pub max: Option<Vec<String>>,
    /// Where the policy was written (`path:line`).
    pub origin: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModuleDecl {
    pub name: String,
    pub region: Option<String>,
    /// Relative to the project directory.
    pub source: Option<String>,
    pub source_sha256: Option<String>,
    #[serde(default)]
    pub imports: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UseDecl {
    pub module: String,
    pub decl: String,
    pub procedure: String,
    /// `axiom` | `kernel` | `native`.
    pub backend: String,
    pub profile: Option<String>,
    /// The axioms Lean reported for this use (for a native use, the axioms of that
    /// computation, whatever the toolchain names them).
    #[serde(default)]
    pub axioms: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DeclDecl {
    pub module: String,
    pub decl: String,
    #[serde(default)]
    pub axioms: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExcludedDecl {
    pub module: String,
    /// `excluded` | `unsupported`.
    pub coverage: String,
    pub reason: String,
}

// ---------------------------------------------------------------- tables

table! {
    /// Files the trust dump depends on, with the recorded and the current digest.
    TrustInput = "trust_inputs", key("path") {
        path: String = "TEXT NOT NULL",
        sha256: String = "TEXT NOT NULL",
        disk_sha256: Option<String> = "TEXT",
        status: String = "TEXT NOT NULL CHECK(status IN ('match','changed','missing'))",
    }
}

table! {
    TrustProcedure = "trust_procedures", key("name") {
        name: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('axiom','decision'))",
        proposition: Option<String> = "TEXT",
        builtin: bool = "INTEGER NOT NULL",
        doc: Option<String> = "TEXT",
    }
}

table! {
    /// `profile` is `''` for the backend's default profile.
    TrustImplementation = "trust_implementations", key("procedure", "backend", "profile") {
        procedure: String = "TEXT NOT NULL",
        backend: String = "TEXT NOT NULL CHECK(backend IN ('kernel','native'))",
        profile: String = "TEXT NOT NULL",
        decl: Option<String> = "TEXT",
        implemented: bool = "INTEGER NOT NULL",
        surface: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
    }
}

table! {
    TrustSet = "trust_sets", key("name") {
        name: String = "TEXT NOT NULL",
        builtin: bool = "INTEGER NOT NULL",
        doc: Option<String> = "TEXT",
    }
}

table! {
    /// A `set` member has `backend = profile = ''`; a procedure member with `profile = ''`
    /// grants every profile of its backend.
    TrustSetMember = "trust_set_members", key("set_name", "member_kind", "member", "backend", "profile") {
        set_name: String = "TEXT NOT NULL",
        member_kind: String = "TEXT NOT NULL CHECK(member_kind IN ('procedure','set'))",
        member: String = "TEXT NOT NULL",
        backend: String = "TEXT NOT NULL CHECK(backend IN ('','axiom','kernel','native'))",
        profile: String = "TEXT NOT NULL",
    }
}

table! {
    TrustPolicy = "trust_policies", key("scope_kind", "scope") {
        scope_kind: String = "TEXT NOT NULL CHECK(scope_kind IN ('root','region','prefix','module'))",
        scope: String = "TEXT NOT NULL",
        builtin: bool = "INTEGER NOT NULL",
        origin: Option<String> = "TEXT",
    }
}

table! {
    /// The sets a policy declares (inherited ones are in `trust_module_policy`).
    TrustPolicySet = "trust_policy_sets", key("scope_kind", "scope", "role", "set_name") {
        scope_kind: String = "TEXT NOT NULL",
        scope: String = "TEXT NOT NULL",
        role: String = "TEXT NOT NULL CHECK(role IN ('allow','max'))",
        set_name: String = "TEXT NOT NULL",
    }
}

table! {
    /// Every module the dump describes or that a described module imports.
    /// `source_status` compares the recorded source digest with the file now on disk;
    /// `freshness` is `consistent` when every recorded digest this module's uses depend on
    /// (its source, its described imports' sources, the inputs, the toolchain) still matches,
    /// which is evidence of nothing more than that.
    TrustModule = "trust_modules", key("name") {
        name: String = "TEXT NOT NULL",
        region: Option<String> = "TEXT",
        source: Option<String> = "TEXT",
        source_sha256: Option<String> = "TEXT",
        source_status: String = "TEXT NOT NULL CHECK(source_status IN ('match','changed','missing','unrecorded'))",
        freshness: String = "TEXT NOT NULL CHECK(freshness IN ('consistent','stale','unknown'))",
        coverage: String = "TEXT NOT NULL CHECK(coverage IN ('covered','excluded','unsupported','undescribed'))",
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
    /// Direct uses. Axioms use `backend = 'axiom'`, `profile = ''`.
    TrustUse = "trust_uses", key("module", "decl", "procedure", "backend", "profile") {
        module: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        procedure: String = "TEXT NOT NULL",
        backend: String = "TEXT NOT NULL CHECK(backend IN ('axiom','kernel','native'))",
        profile: String = "TEXT NOT NULL",
    }
}

table! {
    TrustUseAxiom = "trust_use_axioms", key("module", "decl", "procedure", "backend", "profile", "axiom") {
        module: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        procedure: String = "TEXT NOT NULL",
        backend: String = "TEXT NOT NULL",
        profile: String = "TEXT NOT NULL",
        axiom: String = "TEXT NOT NULL",
    }
}

table! {
    TrustDeclAxiom = "trust_decl_axioms", key("module", "decl", "axiom") {
        module: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        axiom: String = "TEXT NOT NULL",
    }
}

table! {
    /// The effective `allow` and `max` sets of each described module after inheritance, with
    /// the scope that declared them.
    TrustModulePolicy = "trust_module_policy", key("module", "role", "set_name") {
        module: String = "TEXT NOT NULL",
        role: String = "TEXT NOT NULL CHECK(role IN ('allow','max'))",
        set_name: String = "TEXT NOT NULL",
        scope_kind: String = "TEXT NOT NULL",
        scope: String = "TEXT NOT NULL",
    }
}

/// The trust views, written after the core views. Every transitive relation is a recursive
/// query; `UNION` (not `UNION ALL`) keeps them finite even on cyclic data.
pub const TRUST_VIEWS: &[&str] = &[
    "CREATE VIEW trust_set_closure AS WITH RECURSIVE c(set_name, member_kind, member, backend, profile) AS (\
SELECT set_name, member_kind, member, backend, profile FROM trust_set_members \
UNION SELECT c.set_name, m.member_kind, m.member, m.backend, m.profile FROM c \
JOIN trust_set_members m ON c.member_kind = 'set' AND m.set_name = c.member) \
SELECT set_name, member AS procedure, backend, profile FROM c WHERE member_kind = 'procedure';",
    "CREATE VIEW trust_module_allowed AS SELECT DISTINCT p.module, c.procedure, c.backend, c.profile \
FROM trust_module_policy p JOIN trust_set_closure c ON c.set_name = p.set_name WHERE p.role = 'allow';",
    "CREATE VIEW trust_module_deps AS WITH RECURSIVE d(module, dep) AS (\
SELECT module, import FROM trust_imports \
UNION SELECT d.module, i.import FROM d JOIN trust_imports i ON i.module = d.dep) \
SELECT module, dep FROM d;",
    "CREATE VIEW trust_transitive_uses AS \
SELECT u.module, u.module AS via, u.decl, u.procedure, u.backend, u.profile, 1 AS direct FROM trust_uses u \
UNION SELECT d.module, u.module, u.decl, u.procedure, u.backend, u.profile, 0 FROM trust_module_deps d \
JOIN trust_uses u ON u.module = d.dep WHERE d.dep <> d.module;",
    "CREATE VIEW trust_coverage_gaps AS SELECT d.module, d.dep, m.coverage, m.reason FROM trust_module_deps d \
JOIN trust_modules m ON m.name = d.dep WHERE m.coverage <> 'covered';",
    "CREATE VIEW trust_violations AS \
SELECT t.module, t.via, t.decl, t.procedure, t.backend, t.profile, t.direct, 'not-allowed' AS reason \
FROM trust_transitive_uses t JOIN trust_modules m ON m.name = t.module AND m.coverage = 'covered' \
WHERE NOT EXISTS (SELECT 1 FROM trust_module_allowed a WHERE a.module = t.module AND a.procedure = t.procedure \
AND a.backend = t.backend AND (a.profile = '' OR a.profile = t.profile)) \
UNION SELECT t.module, t.via, t.decl, t.procedure, t.backend, t.profile, t.direct, 'unimplemented' \
FROM trust_transitive_uses t JOIN trust_modules m ON m.name = t.module AND m.coverage = 'covered' \
JOIN trust_implementations i ON i.procedure = t.procedure AND i.backend = t.backend AND i.profile = t.profile \
WHERE i.implemented = 0 \
UNION SELECT x.module, x.module, x.decl, x.axiom, 'axiom', '', 1, 'unattributed-axiom' FROM trust_decl_axioms x \
WHERE NOT EXISTS (SELECT 1 FROM trust_uses u WHERE u.module = x.module AND u.decl = x.decl \
AND u.procedure = x.axiom AND u.backend = 'axiom') \
AND NOT EXISTS (SELECT 1 FROM trust_use_axioms a WHERE a.module = x.module AND a.decl = x.decl AND a.axiom = x.axiom);",
];
