//! The converter from the core's frozen trust export (`silmaril.trust-core.v1`, written by
//! `#trust_export`, `Silmaril.Prelude.Trust.Export`) to the database's internal lines
//! ([`TrustLine`]).
//!
//! Every field of the frozen shape is read (unknown fields are an error: the shape is frozen),
//! and each is mapped explicitly. What the export does not carry is either taken from a file whose
//! digest the export records, or recomputed and cross-checked, never assumed:
//!
//! - the sets of the policy file itself (`standard`) are read from `policy.toml` only if its
//!   SHA-256 equals the export's `inputs.policy_toml_sha256`;
//! - effective sets per module are recomputed with the core's rules by the ingest, whose
//!   per-declaration violation counts must equal the export's `violations`;
//! - a module with no declaration in the export is described but not audited.
//!
//! Procedures of kind `named` (named by a set, not implemented) are kept as such and never
//! granted; `unresolved` must list exactly the set members they account for; a native use with
//! `verified = false` is kept and flagged.

use super::sha256_of;
use crate::project::schema::*;
use serde::Deserialize;
use std::collections::BTreeSet;
use std::path::Path;

pub const CORE_DOC_SCHEMA: &str = "silmaril.trust-core.v1";
/// The producer string of the real exporter.
pub const CORE_EXPORTER: &str = "Silmaril.Prelude.Trust.Export (#trust_export)";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Doc {
    pub schema: String,
    pub toolchain: String,
    pub producer: Producer,
    pub inputs: Inputs,
    pub procedures: Vec<Procedure>,
    pub sets: Vec<Set>,
    pub policies: Vec<Policy>,
    pub modules: Vec<Module>,
    pub uses: Vec<Use>,
    pub declarations: Vec<Declaration>,
    pub unresolved: Vec<Unresolved>,
    pub excluded: Vec<Excluded>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Producer {
    pub tool: String,
    pub profile: String,
    pub ceiling: String,
    pub main_module: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Inputs {
    pub policy_toml_sha256: Option<String>,
    pub regions_toml_sha256: Option<String>,
    pub lean_toolchain_sha256: Option<String>,
    pub exclusions_sha256: Option<String>,
    pub policy_pin: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Procedure {
    pub name: String,
    /// `decider` | `declared` | `tactic` | `named`.
    pub kind: String,
    pub implemented: bool,
    #[serde(default)]
    pub doc: String,
    pub module: Option<String>,
    pub format: Option<String>,
    pub sound: Option<String>,
    pub constant: Option<String>,
    #[serde(default)]
    pub backends: Vec<Backend>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Backend {
    /// `native` | `kernel`.
    pub role: String,
    pub function: Option<String>,
    pub equation: Option<String>,
    pub axiom_pattern: Option<String>,
    pub evaluated_constant: Option<String>,
    pub components: Option<Vec<String>>,
    pub toolchain: Option<String>,
    pub fallback_coverage: Option<String>,
    pub check: Option<String>,
    pub sound: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Set {
    pub name: String,
    #[serde(default)]
    pub doc: String,
    pub all: bool,
    pub members: Vec<Member>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Member {
    /// `procedure` | `set`.
    pub kind: String,
    pub name: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    /// `root` | `region` | `module-prefix`.
    pub scope: String,
    pub name: String,
    /// The `default` set (the export calls it `allow`).
    pub allow: Option<Vec<String>>,
    pub max: Option<Vec<String>>,
    pub deps: Option<Vec<String>>,
    pub axioms: Option<Vec<String>>,
    pub origin: Origin,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Origin {
    pub file: String,
    pub pin: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Module {
    pub name: String,
    pub region: Option<String>,
    pub source: String,
    pub source_sha256: Option<String>,
    pub imports: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Use {
    pub module: String,
    pub decl: String,
    pub procedure: String,
    /// `native` | `kernel`.
    pub backend: String,
    pub profile: String,
    pub axiom: Option<String>,
    /// The core's provenance check for a native use (`verifiedNative`); null for a kernel use.
    pub verified: Option<bool>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Declaration {
    pub decl: String,
    pub module: String,
    pub axioms: Vec<String>,
    pub native_axioms: Vec<String>,
    pub own_native: Vec<String>,
    pub dep_native: Vec<String>,
    pub unverified_native: Vec<CoreUnverified>,
    pub violations: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Unresolved {
    pub set: String,
    pub name: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Excluded {
    pub module: String,
    pub coverage: String,
    pub profile: String,
    pub reason: String,
}

/// One set list of the export (`["name"]` or null) as the scope's set name.
fn one(field: &str, scope: &str, v: &Option<Vec<String>>) -> Result<Option<String>, String> {
    match v.as_deref() {
        None => Ok(None),
        Some([n]) => Ok(Some(n.clone())),
        Some(other) => Err(format!(
            "policy {scope}: {field} names {} sets {other:?}; a scope names at most one",
            other.len()
        )),
    }
}

/// The top-level `standard = [...]` list of `policy.toml` (the core's `parsePolicy` reads that key
/// only), if the file's digest is `want`.
fn policy_sets(dir: &Path, want: &Option<String>) -> Result<Vec<LineSet>, String> {
    let Some(want) = want else {
        return Err(
            "inputs.policy_toml_sha256 is null: the policy file's own sets (`standard`) \
                    cannot be read"
                .into(),
        );
    };
    match sha256_of(dir, "policy.toml") {
        None => {
            return Err(
                "policy.toml is missing here, so its own sets (`standard`) cannot be \
                        read; the export does not carry them"
                    .into(),
            );
        }
        Some(h) if h != *want => {
            return Err(format!(
                "policy.toml here has SHA-256 {h}, not the export's {want}: its own sets \
                 (`standard`) are not the exported policy's"
            ));
        }
        Some(_) => {}
    }
    let text = std::fs::read_to_string(dir.join("policy.toml")).map_err(|e| e.to_string())?;
    let table: toml::Table = text.parse().map_err(|e| format!("policy.toml: {e}"))?;
    let mut out = Vec::new();
    if let Some(v) = table.get("standard") {
        let members = v
            .as_array()
            .and_then(|xs| {
                xs.iter()
                    .map(|x| x.as_str().map(String::from))
                    .collect::<Option<Vec<_>>>()
            })
            .ok_or("policy.toml: `standard` is not a list of names")?;
        out.push(LineSet {
            name: "standard".into(),
            all: false,
            origin: Some("policy".into()),
            members,
            includes: vec![],
            resolved: None,
            doc: Some("the policy file's own set, read from policy.toml (digest checked)".into()),
        });
    }
    Ok(out)
}

/// Convert an export into internal lines. `dir` is where `policy.toml` is read (see the module
/// docs). Errors name the field.
pub fn convert(doc: Doc, dir: &Path) -> Result<Vec<TrustLine>, String> {
    if doc.schema != CORE_DOC_SCHEMA {
        return Err(format!("schema {:?} is not {CORE_DOC_SCHEMA}", doc.schema));
    }
    let mut out = Vec::new();
    let origin = if doc.producer.tool == CORE_EXPORTER {
        "lean"
    } else {
        "fixture"
    };
    out.push(TrustLine::Header(LineHeader {
        core_api: CORE_DOC_SCHEMA.into(),
        toolchain: doc.toolchain.clone(),
        profile: Some(doc.producer.profile.clone()),
        ceiling: Some(doc.producer.ceiling.clone()),
        producer: Some(format!(
            "{} (main module {})",
            doc.producer.tool, doc.producer.main_module
        )),
        origin: Some(origin.into()),
        roots: vec!["Silmaril".into()],
    }));
    for (path, sha) in [
        ("policy.toml", &doc.inputs.policy_toml_sha256),
        ("regions.toml", &doc.inputs.regions_toml_sha256),
        ("lean-toolchain", &doc.inputs.lean_toolchain_sha256),
        (
            "scripts/trust-profile-exclude.txt",
            &doc.inputs.exclusions_sha256,
        ),
    ] {
        if let Some(h) = sha {
            out.push(TrustLine::Input(LineInput {
                path: path.into(),
                sha256: h.clone(),
            }));
        }
    }
    out.extend(
        policy_sets(dir, &doc.inputs.policy_toml_sha256)?
            .into_iter()
            .map(TrustLine::Set),
    );

    // Procedures.
    let mut named = BTreeSet::new();
    for p in doc.procedures {
        let what = format!("procedure {} ({})", p.name, p.kind);
        let role = |r: &str| p.backends.iter().find(|b| b.role == r);
        if p.backends
            .iter()
            .any(|b| !matches!(b.role.as_str(), "native" | "kernel"))
        {
            return Err(format!("{what}: a backend role is not native or kernel"));
        }
        match (p.kind.as_str(), p.implemented) {
            ("named", false) => {
                if !p.backends.is_empty() {
                    return Err(format!("{what}: a named procedure has no backends"));
                }
                named.insert(p.name.clone());
                out.push(TrustLine::Named(LineNamed {
                    name: p.name,
                    doc: p.doc,
                }));
            }
            ("decider", true) => {
                let native = role("native").ok_or(format!("{what}: no native backend"))?;
                let kernel = role("kernel");
                // The statement's function: the kernel backend's, else (no separate native
                // implementation) the native backend's. A paired decider without a kernel
                // fallback does not export it.
                let function = match (kernel, &native.equation) {
                    (Some(k), _) => k.function.clone(),
                    (None, None) => native.function.clone(),
                    (None, Some(_)) => None,
                }
                .unwrap_or_else(|| "(not exported)".into());
                let paired = native.equation.is_some();
                out.push(TrustLine::Procedure(LineProcedure {
                    name: p.name,
                    function,
                    kernel_fallback: kernel.is_some(),
                    module: p.module.unwrap_or_default(),
                    format: p.format,
                    sound: p.sound,
                    native_function: if paired {
                        native.function.clone()
                    } else {
                        None
                    },
                    native_eq: native.equation.clone(),
                    axiom_pattern: None,
                    components: vec![],
                    toolchain: None,
                    fallback_coverage: None,
                    doc: p.doc,
                }));
            }
            ("tactic", true) => {
                let native = role("native").ok_or(format!("{what}: no native backend"))?;
                out.push(TrustLine::Procedure(LineProcedure {
                    name: p.name,
                    function: native
                        .evaluated_constant
                        .clone()
                        .ok_or(format!("{what}: no evaluated_constant"))?,
                    kernel_fallback: false,
                    module: p.module.unwrap_or_default(),
                    format: p.format,
                    sound: p.sound,
                    native_function: None,
                    native_eq: None,
                    axiom_pattern: Some(
                        native
                            .axiom_pattern
                            .clone()
                            .ok_or(format!("{what}: no axiom_pattern"))?,
                    ),
                    components: native.components.clone().unwrap_or_default(),
                    toolchain: native.toolchain.clone(),
                    fallback_coverage: native.fallback_coverage.clone(),
                    doc: p.doc,
                }));
            }
            ("declared", true) => {
                let pair = |b: Option<&Backend>| -> Result<Option<LinePair>, String> {
                    match b {
                        None => Ok(None),
                        Some(b) => Ok(Some(LinePair {
                            check: b
                                .check
                                .clone()
                                .ok_or(format!("{what}: {} backend without check", b.role))?,
                            sound: b
                                .sound
                                .clone()
                                .ok_or(format!("{what}: {} backend without sound", b.role))?,
                        })),
                    }
                };
                out.push(TrustLine::DeclaredProcedure(LineDeclaredProcedure {
                    name: p.name.clone(),
                    constant: p.constant.clone().ok_or(format!("{what}: no constant"))?,
                    native: pair(role("native"))?,
                    kernel: pair(role("kernel"))?,
                    format: p.format,
                    bound: None,
                    doc: p.doc,
                }));
            }
            (k, i) => return Err(format!("{what}: kind {k:?} with implemented = {i}")),
        }
    }

    // Sets.
    for s in doc.sets {
        let mut members = Vec::new();
        let mut includes = Vec::new();
        for m in s.members {
            match m.kind.as_str() {
                "procedure" => members.push(m.name),
                "set" => includes.push(m.name),
                k => return Err(format!("set {}: member kind {k:?}", s.name)),
            }
        }
        out.push(TrustLine::Set(LineSet {
            doc: Some(s.doc),
            name: s.name,
            all: s.all,
            origin: Some("trust_set".into()),
            members,
            includes,
            resolved: None,
        }));
    }
    // `unresolved` must list exactly the (set, member) pairs whose member is a `named`
    // (unimplemented) procedure: never silently granted, never silently dropped.
    let unresolved: BTreeSet<(String, String)> = doc
        .unresolved
        .iter()
        .map(|u| (u.set.clone(), u.name.clone()))
        .collect();
    let expected: BTreeSet<(String, String)> = out
        .iter()
        .filter_map(|l| match l {
            TrustLine::Set(s) if s.origin.as_deref() == Some("trust_set") => Some(s),
            _ => None,
        })
        .flat_map(|s| {
            s.members
                .iter()
                .filter(|m| named.contains(*m))
                .map(|m| (s.name.clone(), m.clone()))
        })
        .collect();
    if unresolved != expected {
        return Err(format!(
            "unresolved {unresolved:?} differs from the set members that name unimplemented procedures {expected:?}"
        ));
    }

    // Policies (each names the pinned file; the pin must be the export's).
    for p in doc.policies {
        if doc.inputs.policy_pin.as_deref() != Some(p.origin.pin.as_str()) {
            return Err(format!(
                "policy {}: pin {} is not inputs.policy_pin {:?}",
                p.name, p.origin.pin, doc.inputs.policy_pin
            ));
        }
        if !matches!(p.scope.as_str(), "root" | "region" | "module-prefix") {
            return Err(format!("policy {}: scope {:?}", p.name, p.scope));
        }
        out.push(TrustLine::Scope(LineScope {
            scope_kind: Some(p.scope.clone()),
            module: p.name.clone(),
            max: one("max", &p.name, &p.max)?,
            default: one("allow", &p.name, &p.allow)?,
            deps: one("deps", &p.name, &p.deps)?,
            axioms: one("axioms", &p.name, &p.axioms)?,
            policy_file: Some(p.origin.file),
            policy_pin: Some(p.origin.pin),
        }));
    }

    // Modules and their sources.
    for m in doc.modules {
        if let Some(h) = &m.source_sha256 {
            out.push(TrustLine::Source(LineSource {
                module: m.name.clone(),
                path: m.source.clone(),
                sha256: h.clone(),
            }));
        }
        out.push(TrustLine::Module(LineModule {
            name: m.name,
            imports: m.imports,
            region: m.region,
        }));
    }

    // Uses.
    for u in doc.uses {
        out.push(TrustLine::Use(LineUse {
            decl: u.decl,
            module: u.module,
            procedure: u.procedure,
            mode: u.backend,
            profile: u.profile,
            axiom: u.axiom,
            verified: u.verified,
        }));
    }

    // Declarations (the listed modules only).
    for d in doc.declarations {
        out.push(TrustLine::Decl(LineDecl {
            decl: d.decl,
            module: d.module,
            own_native: d.own_native,
            dep_native: d.dep_native,
            unverified: d
                .unverified_native
                .into_iter()
                .map(|u| (u.procedure, u.axiom))
                .collect(),
            axioms: d.axioms,
            native_axioms: d.native_axioms,
            profile: Some(doc.producer.profile.clone()),
            elaborated_profiles: vec![],
            violations: d.violations,
        }));
    }

    // Exclusions of the core (`scripts/trust-profile-exclude.txt` for the export's ceiling).
    for e in doc.excluded {
        if e.coverage != "excluded" {
            return Err(format!("excluded {}: coverage {:?}", e.module, e.coverage));
        }
        out.push(TrustLine::Excluded(LineExcluded {
            module: e.module,
            coverage: "excluded".into(),
            reason: format!(
                "{} (core exclusion for the {} profile)",
                e.reason, e.profile
            ),
        }));
    }
    Ok(out)
}
