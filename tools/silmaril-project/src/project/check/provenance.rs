//! Layer 2, build provenance (`silmaril.artifacts.v0.2`): the local registry's derivations,
//! checked without the network or a rebuild.
//!
//! - P1: every file a derivation names (`recipe`, `receipt`, an input `path`) exists in the
//!   package, and hashes to its `cid` when one is given (`sil project lock` fills them).
//! - P2: names resolve: an input `artifact` is a registered artifact (name or CID), an
//!   artifact's `derivation` is a derivation of the registry; derivation names are unique and
//!   valid; `op`, `status` and `role` are known.
//! - P3: every input has exactly one locator; a `url` has a `sha256`, a `git` input a full
//!   40-hex `rev`; `available = "private:<package>"` needs a digest.
//! - P4: a `reproduced` derivation has a `receipt` listing every output's sha256, matching the
//!   registry; a `pinned` or `reproduced` derivation has outputs.
//! - P5: no derivation is its own (transitive) input.
//! - P6 (a summary line): how many local artifacts have a derivation.

use super::super::hash;
use super::blobs::Registries;
use super::{Ctx, Outcome, name_error, reach};
use crate::project::schema::*;
use std::collections::{BTreeMap, BTreeSet};

fn is_hex(s: &str, n: usize) -> bool {
    s.len() == n
        && s.bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

/// The checks; returns the P6 summary line when the registry has derivations.
pub(super) fn check(cx: &Ctx, reg: &Registries, o: &mut Outcome) -> Option<String> {
    let p = cx.p;
    if !p.registry_exists(&p.name) {
        return None;
    }
    let Ok((path, file)) = p.registry(&p.name) else {
        return None; // reported by `blobs::registries`
    };
    if file.derivations.is_empty() {
        return None;
    }
    if file.schema != ARTIFACTS_SCHEMA {
        o.error(
            format!("registry {}:{path}", p.name),
            format!("`[[derivation]]` needs schema = {ARTIFACTS_SCHEMA:?}"),
        );
    }
    let mut names: BTreeMap<&str, &Derivation> = BTreeMap::new();
    for d in &file.derivations {
        let at = format!("derivation {}", d.name);
        if let Some(why) = name_error(&d.name) {
            o.error(&at, format!("invalid name: {why}"));
        }
        if names.insert(&d.name, d).is_some() {
            o.error(&at, "declared twice (P2)");
        }
        if !DERIVATION_OPS.contains(&d.op.as_str()) {
            o.error(
                &at,
                format!("op {:?} is not one of {}", d.op, DERIVATION_OPS.join(", ")),
            );
        }
        if !DERIVATION_STATUSES.contains(&d.status.as_str()) {
            o.error(
                &at,
                format!(
                    "status {:?} is not one of {}",
                    d.status,
                    DERIVATION_STATUSES.join(", ")
                ),
            );
        }
    }
    // the outputs of each derivation: (cid, entry)
    let mut outputs: BTreeMap<&str, Vec<(&str, &ArtifactEntry)>> = BTreeMap::new();
    let mut with = 0;
    for e in &file.artifacts {
        let (Some(cid), Some(d)) = (&e.cid, &e.derivation) else {
            continue;
        };
        with += 1;
        if names.contains_key(d.as_str()) {
            outputs.entry(d).or_default().push((cid, e));
        } else {
            let label = e.name.clone().unwrap_or_else(|| cid.clone());
            o.error(
                format!("artifact {label}"),
                format!("derivation {d:?} is not declared (P2)"),
            );
        }
    }
    // P1: files
    let file_ok = |o: &mut Outcome, at: &str, what: &str, f: &str, cid: &Option<String>| match p
        .read_package_file(&p.name, f)
    {
        Err(e) => o.error(at, format!("{what}: {e} (P1)")),
        Ok(bytes) => {
            if let Some(c) = cid
                && *c != hash::Digests::of(&bytes).cid
            {
                o.error(
                    at,
                    format!("{what} {f}: does not hash to {c} (P1; run `sil project lock`)"),
                );
            }
        }
    };
    // derivation -> derivations it reads (through input artifacts)
    let mut deps: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let by_cid: BTreeMap<&str, &ArtifactEntry> = file
        .artifacts
        .iter()
        .filter_map(|e| e.cid.as_deref().map(|c| (c, e)))
        .collect();
    for d in &file.derivations {
        let at = format!("derivation {}", d.name);
        if let Some(r) = &d.recipe {
            file_ok(o, &at, "recipe", &r.path, &r.cid);
        }
        if let Some(r) = &d.receipt {
            file_ok(o, &at, "receipt", &r.path, &r.cid);
        }
        for (i, inp) in d.inputs.iter().enumerate() {
            let label = inp
                .name
                .clone()
                .unwrap_or_else(|| format!("input {}", i + 1));
            if !INPUT_ROLES.contains(&inp.role.as_str()) {
                o.error(
                    &at,
                    format!(
                        "{label}: role {:?} is not one of {}",
                        inp.role,
                        INPUT_ROLES.join(", ")
                    ),
                );
            }
            let locators = [
                inp.artifact.is_some(),
                inp.path.is_some(),
                inp.url.is_some(),
                inp.git.is_some(),
            ];
            let n = locators.iter().filter(|b| **b).count();
            let private = inp
                .available
                .as_deref()
                .is_some_and(|a| a.starts_with("private:"));
            if n > 1 || (n == 0 && !private) {
                o.error(
                    &at,
                    format!("{label}: give exactly one of `artifact`, `path`, `url`, `git` (P3)"),
                );
            }
            if let Some(a) = &inp.available
                && (!private || a.len() == "private:".len())
            {
                o.error(
                    &at,
                    format!("{label}: available {a:?} is not `private:<package>` (P3)"),
                );
            }
            if (inp.url.is_some() || private)
                && !inp.sha256.as_deref().is_some_and(|s| is_hex(s, 64))
            {
                o.error(&at, format!("{label}: needs `sha256` (64 hex digits) (P3)"));
            }
            if let Some(g) = &inp.git
                && !is_hex(&g.rev, 40)
            {
                o.error(
                    &at,
                    format!(
                        "{label}: git rev {:?} is not a full 40-hex commit (P3)",
                        g.rev
                    ),
                );
            }
            if let Some(f) = &inp.path {
                file_ok(o, &at, &label, f, &inp.cid);
            }
            if let Some(a) = &inp.artifact {
                match reg.resolve(a) {
                    None => o.error(
                        &at,
                        format!("{label}: artifact {a:?} is not registered (P2)"),
                    ),
                    Some(cid) => {
                        if let Some(dd) = by_cid
                            .get(cid.as_str())
                            .and_then(|e| e.derivation.as_deref())
                            && let Some((k, _)) = names.get_key_value(dd)
                        {
                            deps.entry(&d.name).or_default().insert(k);
                        }
                    }
                }
            }
        }
        // P4
        let outs = outputs
            .get(d.name.as_str())
            .map(Vec::as_slice)
            .unwrap_or_default();
        if outs.is_empty() && d.status != "generated" {
            o.error(&at, "no artifact names it as its `derivation` (P4)");
        }
        if d.status == "reproduced" {
            match &d.receipt {
                None => o.error(&at, "a `reproduced` derivation needs a `receipt` (P4)"),
                Some(r) => {
                    let listed: BTreeSet<String> = p
                        .read_package_file(&p.name, &r.path)
                        .ok()
                        .and_then(|b| String::from_utf8(b).ok())
                        .unwrap_or_default()
                        .lines()
                        .filter_map(|l| l.split_whitespace().next().map(String::from))
                        .collect();
                    for (cid, e) in outs {
                        match &e.sha256 {
                            Some(s) if listed.contains(s) => {}
                            Some(s) => o.error(
                                &at,
                                format!(
                                    "receipt {} does not list output {cid} (sha256 {s}) (P4)",
                                    r.path
                                ),
                            ),
                            None => o.error(
                                &at,
                                format!("output {cid} has no sha256 (run `sil project lock`)"),
                            ),
                        }
                    }
                }
            }
        }
    }
    // P5
    for d in names.keys() {
        let start: Vec<&str> = deps.get(d).into_iter().flatten().copied().collect();
        if reach(start, &deps).contains(d) {
            o.error(
                format!("derivation {d}"),
                "is its own (transitive) input (P5)",
            );
        }
    }
    // P6
    Some(format!(
        "provenance: {} derivations; {with} of {} local artifacts have one",
        file.derivations.len(),
        file.artifacts.len()
    ))
}
