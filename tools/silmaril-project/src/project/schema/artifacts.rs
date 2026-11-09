//! Layer 2, artifacts: the registry file `silmaril/artifacts.toml` (with build provenance,
//! [`Derivation`], since `silmaril.artifacts.v0.2`), the `artifact` and `artifact_type` records
//! and the blob tables (artifacts, paths, tool-checked facts).
use super::*;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

// ---------------------------------------------------------------- silmaril/artifacts.toml

/// `silmaril/artifacts.toml`. `lock` writes `cid`, `size`, `sha256` and `git_sha1`; a person
/// writes `paths` and optionally `name`, `package`, `type`, `doc` and `derivation`, and the
/// `[[derivation]]` tables (v0.2).
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Artifacts {
    pub schema: String,
    #[serde(default, rename = "artifact")]
    pub artifacts: Vec<ArtifactEntry>,
    /// How artifacts are built (v0.2).
    #[serde(default, rename = "derivation")]
    pub derivations: Vec<Derivation>,
}

/// The registry schemas `sil project` reads; v0.1 has no derivations.
pub const ARTIFACTS_SCHEMAS: [&str; 2] = ["silmaril.artifacts.v0.1", ARTIFACTS_SCHEMA];

/// One build: a recipe run on inputs in an environment, producing the artifacts whose
/// `derivation` names it. Checked by `sil project check` (rules P1–P6) without the network.
#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Derivation {
    /// A dotted name, unique in the registry.
    pub name: String,
    /// What the build does: one of [`DERIVATION_OPS`].
    pub op: String,
    /// One of [`DERIVATION_STATUSES`]: `pinned` (the output digests are recorded),
    /// `reproduced` (rebuilt bit for bit; needs a `receipt`), `generated` (the output need not be
    /// committed).
    pub status: String,
    /// The script that builds the outputs.
    pub recipe: Option<Recipe>,
    /// Tools and their exact versions.
    #[serde(default)]
    pub toolchain: Vec<Tool>,
    /// Flags, exactly as the recipe passes them.
    #[serde(default)]
    pub flags: Vec<String>,
    pub environment: Option<Environment>,
    /// A file listing the outputs' sha256 (`sha256sum` format), from a rebuild.
    pub receipt: Option<FileRef>,
    pub doc: Option<String>,
    /// Tool-only data (any table), kept as written; `sil project check` does not read it.
    pub meta: Option<toml::Table>,
    #[serde(default, rename = "input")]
    pub inputs: Vec<DerivationInput>,
}

/// What a derivation can do.
pub const DERIVATION_OPS: [&str; 9] = [
    "compile",
    "link",
    "patch",
    "instrument",
    "lift",
    "segment",
    "generate",
    "fetch",
    "revision-of",
];
/// A derivation's status.
pub const DERIVATION_STATUSES: [&str; 3] = ["pinned", "reproduced", "generated"];
/// An input's role.
pub const INPUT_ROLES: [&str; 6] = ["source", "driver", "libc", "patch", "recipe-input", "tool"];

/// A recipe: a script in the package, its arguments, and its CID (`lock` fills it).
#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Recipe {
    pub path: String,
    #[serde(default)]
    pub args: Vec<String>,
    pub cid: Option<String>,
}

/// A file in the package, with its CID (`lock` fills it).
#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FileRef {
    pub path: String,
    pub cid: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Tool {
    pub name: String,
    pub version: String,
}

#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Environment {
    pub os: Option<String>,
    pub arch: Option<String>,
    #[serde(default)]
    pub vars: BTreeMap<String, String>,
}

/// One input of a derivation. It has exactly one locator: `artifact` (a registered artifact,
/// by name or CID), `path` (a file in the package, with an optional `cid`), `url` (with its
/// `sha256`) or `git` (a repository and a full 40-hex `rev`).
#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct DerivationInput {
    /// One of [`INPUT_ROLES`].
    pub role: String,
    /// A label (e.g. the tarball's file name).
    pub name: Option<String>,
    pub artifact: Option<String>,
    pub path: Option<String>,
    pub cid: Option<String>,
    pub url: Option<String>,
    pub sha256: Option<String>,
    pub git: Option<GitRev>,
    /// `private:<package>`: recorded but not shipped; needs a digest (`sha256`).
    pub available: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GitRev {
    pub repo: String,
    pub rev: String,
}

/// One registry entry, keyed by `cid`. Field order is the written order.
#[derive(Debug, Clone, Default, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactEntry {
    pub cid: Option<String>,
    /// The interpretation tag; the codec is read from the CID. v0.1: only `blob`.
    #[serde(default = "blob", rename = "type")]
    pub r#type: String,
    /// A dotted name, unique in the import closure.
    pub name: Option<String>,
    /// The package whose root `paths` are relative to. Default: the registry's package.
    pub package: Option<String>,
    #[serde(default)]
    pub paths: Vec<String>,
    pub size: Option<u64>,
    pub sha256: Option<String>,
    pub git_sha1: Option<String>,
    pub doc: Option<String>,
    /// The derivation that builds it (v0.2).
    pub derivation: Option<String>,
    /// Tool-only data (any table), kept as written (v0.2); Lean and `check` do not read it.
    pub meta: Option<toml::Table>,
}

pub fn blob() -> String {
    "blob".into()
}

/// Artifact types (interpretation tags) of v0.1, with their CID codec.
pub const ARTIFACT_TYPES: [(&str, &str); 1] = [("blob", "raw")];

/// An artifact entry as Lean imported it (`silmaril artifacts "…"`); Rust checks it against
/// the registry file.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
    pub cid: String,
    pub module: String,
    #[serde(default = "blob", rename = "type")]
    pub r#type: String,
    pub name: Option<String>,
    pub package: Option<String>,
    #[serde(default)]
    pub paths: Vec<String>,
    pub size: Option<u64>,
    pub doc: Option<String>,
}

table! {
    /// `silmaril artifact_type NAME := decl`.
    ArtifactType = "artifact_types", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// A blob; its sid is its BLAKE3 digest (the one inside its CID). Digests are the
    /// registry's, verified by `check` (see `facts`).
    ArtifactRow = "artifacts", key("sid"), unique("cid") {
        sid: String = "TEXT NOT NULL",
        cid: String = "TEXT NOT NULL",
        r#type: String = "TEXT NOT NULL",
        name: Option<String> = "TEXT",
        size: Option<u64> = "INTEGER",
        sha256: Option<String> = "TEXT",
        git_sha1: Option<String> = "TEXT",
        registry: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
    }
}

table! {
    ArtifactPath = "artifact_paths", key("package", "path") {
        package: String = "TEXT NOT NULL",
        path: String = "TEXT NOT NULL",
        artifact: String = "TEXT NOT NULL",
    }
}

table! {
    /// A tool-checked fact: `subject` is an artifact sid, `at` the `package:path` the
    /// checker read.
    Fact = "facts", key("subject", "at", "property", "checker") {
        subject: String = "TEXT NOT NULL",
        at: String = "TEXT NOT NULL",
        property: String = "TEXT NOT NULL",
        value: String = "TEXT NOT NULL",
        checker: String = "TEXT NOT NULL",
        tier: String = "TEXT NOT NULL CHECK(tier IN ('kernel','compiled','tool','external'))",
    }
}
