//! Layer 2, artifacts: the registries in scope, R3 (every blob in scope hashes to its
//! entry) and W2 (files Lean reads are Lake inputs).

use super::super::hash;
use super::refs::Kept;
use super::{Ctx, Outcome, name_error};
use crate::project::schema::*;
use std::collections::{BTreeMap, BTreeSet};

/// One registry entry in scope, with where it came from.
#[derive(Debug, Clone)]
pub(super) struct Blob {
    pub entry: ArtifactEntry,
    /// The package whose registry declares it.
    pub registry: String,
    /// The package `paths` are relative to.
    pub package: String,
    pub used: bool,
}

/// The registries the project sees.
pub(super) struct Registries {
    /// By CID.
    pub blobs: BTreeMap<String, Blob>,
    /// Name -> CID.
    names: BTreeMap<String, String>,
    /// Package -> registry path.
    pub files: BTreeMap<String, String>,
}

impl Registries {
    /// A CID or a registry name, as a CID.
    pub fn resolve(&self, s: &str) -> Option<String> {
        if self.blobs.contains_key(s) {
            Some(s.to_string())
        } else {
            self.names.get(s).cloned()
        }
    }
    /// A CID or a registry name, as a CID; an unknown one as itself.
    pub fn resolve_or_keep(&self, s: &str) -> String {
        self.resolve(s).unwrap_or_else(|| s.to_string())
    }
    /// The blobs in scope: the local registry's and those in-scope records use.
    pub fn in_scope<'r>(&'r self, kept: &Kept) -> Vec<(&'r String, &'r Blob)> {
        self.blobs
            .iter()
            .filter(|(c, b)| b.used || kept.used_blobs.contains(*c))
            .collect()
    }
}

/// The registries in scope: the local one, and those of the packages whose `artifact` records
/// Lean imported. Lean's view of each registry must be the file's (else the dump is stale).
pub(super) fn registries(cx: &Ctx, o: &mut Outcome) -> Registries {
    let (p, dump) = (cx.p, cx.dump);
    let mut blobs: BTreeMap<String, Blob> = BTreeMap::new();
    let mut files: BTreeMap<String, String> = BTreeMap::new();
    let mut registries: BTreeSet<String> = BTreeSet::new();
    if p.registry_exists(&p.name) {
        registries.insert(p.name.clone());
    }
    for r in &dump.records {
        if let Record::Artifact(a) = r {
            match p.package_of(&a.module) {
                Some(pk) => {
                    registries.insert(pk);
                }
                None => o.error(
                    format!("artifact {}", a.cid),
                    format!("no package owns module {}", a.module),
                ),
            }
        }
    }
    for pk in &registries {
        let (path, reg) = match p.registry(pk) {
            Ok(x) => x,
            Err(e) => {
                o.error(format!("registry {pk}"), e);
                continue;
            }
        };
        let at = format!("registry {pk}:{path}");
        files.insert(pk.clone(), path.clone());
        if !ARTIFACTS_SCHEMAS.contains(&reg.schema.as_str()) {
            o.error(
                &at,
                format!("schema {:?} is not {ARTIFACTS_SCHEMA:?}", reg.schema),
            );
        }
        for (i, e) in reg.artifacts.iter().enumerate() {
            let label = e
                .name
                .clone()
                .or_else(|| e.paths.first().cloned())
                .unwrap_or_else(|| format!("#{i}"));
            let Some(cid) = &e.cid else {
                o.error(&at, format!("{label}: no cid (run `sil project lock`)"));
                continue;
            };
            if hash::blake3_of_cid(cid).is_none() {
                o.error(
                    &at,
                    format!("{label}: {cid:?} is not a CIDv1 raw BLAKE3-256 CID"),
                );
                continue;
            }
            if let Some(why) = e.name.as_deref().and_then(name_error) {
                o.error(&at, format!("{label}: invalid name: {why}"));
            }
            if !ARTIFACT_TYPES.iter().any(|(t, _)| *t == e.r#type) {
                o.error(&at, format!("{label}: type {:?} is not blob", e.r#type));
            }
            let blob = Blob {
                entry: e.clone(),
                registry: pk.clone(),
                package: e.package.clone().unwrap_or_else(|| pk.clone()),
                used: pk == &p.name,
            };
            match blobs.get_mut(cid) {
                Some(prev) if prev.registry == *pk => {
                    o.error(&at, format!("{cid} appears twice (merge its paths)"))
                }
                Some(prev) => {
                    // The same blob in two registries: one artifact, more paths.
                    if prev.entry.name.is_some() && e.name.is_some() && prev.entry.name != e.name {
                        o.error(
                            &at,
                            format!(
                                "{cid} is named {:?} in {} and {:?} here",
                                prev.entry.name, prev.registry, e.name
                            ),
                        );
                    }
                }
                None => {
                    blobs.insert(cid.clone(), blob);
                }
            }
        }
    }
    let mut names: BTreeMap<String, String> = BTreeMap::new();
    for (cid, b) in &blobs {
        if let Some(n) = &b.entry.name
            && let Some(other) = names.insert(n.clone(), cid.clone())
        {
            o.error(
                format!("artifact {n}"),
                format!("names both {other} and {cid}"),
            );
        }
    }
    for r in &dump.records {
        if let Record::Artifact(a) = r {
            let at = format!("artifact {}", a.cid);
            match blobs.get(&a.cid) {
                None => o.error(
                    &at,
                    "imported by Lean but not in the registry (stale dump?)",
                ),
                Some(b) => {
                    let e = &b.entry;
                    if e.name != a.name
                        || e.paths != a.paths
                        || e.size != a.size
                        || e.package != a.package
                        || e.r#type != a.r#type
                        || e.doc != a.doc
                    {
                        o.error(&at, "Lean's copy differs from the registry (stale dump? rebuild and dump again)");
                    }
                }
            }
        }
    }
    Registries {
        blobs,
        names,
        files,
    }
}

/// What R3 read: the tool-checked facts and the `(package, path) -> cid` map.
pub(super) struct Files {
    pub facts: Vec<Fact>,
    pub paths: BTreeMap<(String, String), String>,
}

/// R3: every blob in scope hashes to its registry entry; record the facts.
pub(super) fn hash(cx: &Ctx, reg: &Registries, kept: &Kept, o: &mut Outcome) -> Files {
    let p = cx.p;
    let mut facts = Vec::new();
    let mut paths_rows: BTreeMap<(String, String), String> = BTreeMap::new();
    for (cid, b) in reg.in_scope(kept) {
        let at = format!("artifact {}", b.entry.name.as_deref().unwrap_or(cid));
        if b.entry.paths.is_empty() {
            o.warn(&at, "no paths: the blob is not checked");
        }
        for path in &b.entry.paths {
            match p.read_package_file(&b.package, path) {
                Err(e) => o.error(&at, e),
                Ok(bytes) => {
                    let d = hash::Digests::of(&bytes);
                    let mut ok = true;
                    for (name, got, want) in [
                        ("cid", Some(cid.clone()), d.cid.clone()),
                        (
                            "size",
                            b.entry.size.map(|s| s.to_string()),
                            d.size.to_string(),
                        ),
                        ("sha256", b.entry.sha256.clone(), d.sha256.clone()),
                        ("git_sha1", b.entry.git_sha1.clone(), d.git_sha1.clone()),
                    ] {
                        match got {
                            None => {
                                ok = false;
                                o.error(&at, format!("no {name} (run `sil project lock`)"));
                            }
                            Some(g) if g != want => {
                                ok = false;
                                o.error(
                                    &at,
                                    format!(
                                        "{}:{path}: {name} mismatch: registry {g}, file {want}",
                                        b.package
                                    ),
                                );
                            }
                            _ => {}
                        }
                    }
                    let place = format!("{}:{path}", b.package);
                    if let Some(prev) =
                        paths_rows.insert((b.package.clone(), path.clone()), cid.clone())
                        && prev != *cid
                    {
                        o.error(&at, format!("{place} is also registered as {prev}"));
                    }
                    if ok {
                        let subject = hash::blake3_of_cid(cid).unwrap_or_default();
                        for (property, value) in [
                            ("cid", d.cid),
                            ("codec", "raw".into()),
                            ("git_sha1", d.git_sha1),
                            ("sha256", d.sha256),
                            ("size", d.size.to_string()),
                            ("type", b.entry.r#type.clone()),
                        ] {
                            facts.push(Fact {
                                subject: subject.clone(),
                                at: place.clone(),
                                property: property.into(),
                                value,
                                checker: CHECKER.into(),
                                tier: "tool".into(),
                            });
                        }
                    }
                }
            }
        }
    }
    Files {
        facts,
        paths: paths_rows,
    }
}

/// W2: files Lean reads at elaboration time should be Lake inputs.
pub(super) fn inputs(cx: &Ctx, reg: &Registries, kept: &Kept, o: &mut Outcome) {
    let (p, dump) = (cx.p, cx.dump);
    let Some(inputs) = p.input_files() else {
        return;
    };
    let mut read: BTreeSet<String> = BTreeSet::new();
    if let Some(f) = reg.files.get(&p.name)
        && dump
            .records
            .iter()
            .any(|r| matches!(r, Record::Artifact(a) if cx.local(&a.module)))
    {
        read.insert(f.clone());
    }
    for r in dump
        .records
        .iter()
        .filter(|r| kept.kept(cx, r) && cx.local(r.module()))
    {
        if let Record::Value(v) = r {
            for s in &v.sources {
                if s.package.as_ref().is_none_or(|pk| *pk == p.name)
                    && let Some(path) = &s.path
                {
                    read.insert(path.clone());
                }
            }
        }
    }
    let dirs = p.input_dirs().unwrap_or_default();
    let in_dir = |f: &str| dirs.iter().any(|d| f.starts_with(&format!("{d}/")));
    for f in read.difference(&inputs).filter(|f| !in_dir(f)) {
        o.warn(
            format!("lakefile.toml {f}"),
            format!("Lean reads it but it is not an [[input_file]] or below an [[input_dir]] (add `[[input_file]] path = \"{f}\"` and list it in the library's `needs`)"),
        );
    }
}
