//! `--trust PATH`: check a trust dump ([`schema::trust`]) and add its tables to the database.
//!
//! The check fails closed: an unsupported schema, a duplicate, an unknown procedure, set,
//! implementation or module, a set cycle, an overlapping or contradictory policy, or a child
//! policy beyond its parent's `max` is an error, and no database is written. Uses outside a
//! module's effective `allow` set, uses of an unimplemented implementation and axioms no use
//! accounts for are **violations**: warnings, rows of the `trust_violations` view, and lines of
//! the report. Without `--trust`, the tables are empty and `meta` says `trust.status = absent`:
//! nothing is known about decision-procedure use, which is not the same as a clean result.
//!
//! Policy resolution, for a module `m`: the root policy (built in as `allow = max =
//! [standard]` when the dump has none), then the policy of `m`'s region, then every `prefix`
//! policy `A.B.*` with `m` under `A.B`, shortest first, then the `module` policy of `m`. Each
//! step may restate `allow` and `max`; what it omits is inherited. Every step's `allow` and
//! `max` must lie within the previous effective `max`, and an inherited `allow` must lie
//! within a restated `max`. The effective `allow` applies to the module's own uses and to the
//! uses of every module it imports, transitively (there is no separate dependency role yet).

use super::check::Outcome;
use super::hash::Digests;
use super::schema::*;
use miette::{IntoDiagnostic, Result, WrapErr};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

/// A grant: `(procedure, backend, profile)`; profile `""` is every profile of the backend.
type Grant = (String, String, String);

/// What a set of grants covers: `g` is in it, or its backend's wildcard is.
fn covers(have: &BTreeSet<Grant>, g: &Grant) -> bool {
    have.contains(g) || have.contains(&(g.0.clone(), g.1.clone(), String::new()))
}

fn meta(o: &mut Outcome, rows: &[(&str, String)]) {
    if let Some((_, table)) = o.db.tables.iter_mut().find(|(t, _)| t.name == "meta") {
        for (k, v) in rows {
            table.push(vec![Sql::Text(format!("trust.{k}")), Sql::Text(v.clone())]);
        }
    }
}

fn sha256_of(dir: &Path, rel: &str) -> Option<String> {
    fs::read(dir.join(rel)).ok().map(|b| Digests::of(&b).sha256)
}

fn status(recorded: &str, disk: &Option<String>) -> &'static str {
    match disk {
        None => "missing",
        Some(d) if d == recorded => "match",
        Some(_) => "changed",
    }
}

#[derive(Default)]
struct Tables {
    inputs: Vec<TrustInput>,
    procedures: Vec<TrustProcedure>,
    impls: Vec<TrustImplementation>,
    sets: Vec<TrustSet>,
    members: Vec<TrustSetMember>,
    policies: Vec<TrustPolicy>,
    policy_sets: Vec<TrustPolicySet>,
    modules: Vec<TrustModule>,
    imports: Vec<TrustImport>,
    uses: Vec<TrustUse>,
    use_axioms: Vec<TrustUseAxiom>,
    decl_axioms: Vec<TrustDeclAxiom>,
    module_policy: Vec<TrustModulePolicy>,
}

impl Tables {
    fn push(self, db: &mut Database) {
        db.push(&self.inputs);
        db.push(&self.procedures);
        db.push(&self.impls);
        db.push(&self.sets);
        db.push(&self.members);
        db.push(&self.policies);
        db.push(&self.policy_sets);
        db.push(&self.modules);
        db.push(&self.imports);
        db.push(&self.uses);
        db.push(&self.use_axioms);
        db.push(&self.decl_axioms);
        db.push(&self.module_policy);
    }
}

/// Check the trust dump at `path` (relative to `dir`), if any, and append the trust tables to
/// `o.db` (which `check` has filled up to the summary table).
pub fn run(dir: &Path, path: Option<&Path>, o: &mut Outcome) -> Result<()> {
    let Some(path) = path else {
        meta(o, &[("status", "absent".into())]);
        o.lines.push(
            "trust: no trust dump (--trust): decision-procedure and axiom use is unaudited \
             (unknown, not clean)"
                .into(),
        );
        Tables::default().push(&mut o.db);
        return Ok(());
    };
    let bytes = fs::read(dir.join(path))
        .into_diagnostic()
        .wrap_err_with(|| format!("could not read the trust dump {}", path.display()))?;
    let dump: TrustDump = serde_json::from_slice(&bytes)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not parse the trust dump {}", path.display()))?;
    let at = path.display().to_string();
    let mut t = Tables::default();
    if dump.schema != TRUST_SCHEMA {
        o.error(
            &at,
            format!("schema {:?} is not {TRUST_SCHEMA:?}", dump.schema),
        );
        Tables::default().push(&mut o.db);
        return Ok(());
    }
    Ingest {
        dir,
        at: &at,
        dump: &dump,
        o,
    }
    .run(&mut t, Digests::of(&bytes).sha256);
    t.push(&mut o.db);
    Ok(())
}

struct Ingest<'a> {
    dir: &'a Path,
    at: &'a str,
    dump: &'a TrustDump,
    o: &'a mut Outcome,
}

impl Ingest<'_> {
    fn err(&mut self, msg: impl AsRef<str>) {
        self.o.error(self.at, msg);
    }

    fn run(mut self, t: &mut Tables, sha256: String) {
        let d = self.dump;
        // ---- provenance: the dump, the toolchain, the inputs
        let toolchain = fs::read_to_string(self.dir.join("lean-toolchain"))
            .ok()
            .map(|s| s.trim().to_string());
        let toolchain_status = match &toolchain {
            None => "missing",
            Some(tc) if *tc == d.toolchain => "match",
            Some(_) => "changed",
        };
        let mut seen = BTreeSet::new();
        for i in &d.inputs {
            if !seen.insert(i.path.clone()) {
                self.err(format!("input {}: listed twice", i.path));
            }
            let disk = sha256_of(self.dir, &i.path);
            t.inputs.push(TrustInput {
                path: i.path.clone(),
                sha256: i.sha256.clone(),
                status: status(&i.sha256, &disk).into(),
                disk_sha256: disk,
            });
        }
        let inputs_ok = t.inputs.iter().all(|i| i.status == "match");

        // ---- procedures and implementations
        let mut kinds: BTreeMap<String, String> = BTreeMap::new();
        for p in &d.procedures {
            if !matches!(p.kind.as_str(), "axiom" | "decision") {
                self.err(format!(
                    "procedure {}: kind {:?} is not axiom or decision",
                    p.name, p.kind
                ));
                continue;
            }
            if kinds.insert(p.name.clone(), p.kind.clone()).is_some() {
                self.err(format!("procedure {}: declared twice", p.name));
                continue;
            }
            t.procedures.push(TrustProcedure {
                name: p.name.clone(),
                kind: p.kind.clone(),
                proposition: p.proposition.clone(),
                builtin: false,
                doc: p.doc.clone(),
            });
        }
        for a in STANDARD_AXIOMS {
            match kinds.get(a).map(String::as_str) {
                Some("axiom") => {}
                Some(_) => self.err(format!(
                    "procedure {a}: a standard axiom must have kind axiom"
                )),
                None => {
                    kinds.insert(a.into(), "axiom".into());
                    t.procedures.push(TrustProcedure {
                        name: a.into(),
                        kind: "axiom".into(),
                        proposition: None,
                        builtin: true,
                        doc: Some("standard axiom".into()),
                    });
                }
            }
        }
        // (procedure, backend) -> profiles, and each implementation's `implemented`.
        let mut impls: BTreeMap<Grant, bool> = BTreeMap::new();
        for i in &d.implementations {
            let profile = i.profile.clone().unwrap_or_default();
            let what = format!("implementation {} {} {:?}", i.procedure, i.backend, profile);
            match kinds.get(&i.procedure).map(String::as_str) {
                None => {
                    self.err(format!("{what}: unknown procedure"));
                    continue;
                }
                Some("axiom") => {
                    self.err(format!("{what}: an axiom has no implementations"));
                    continue;
                }
                _ => {}
            }
            if !matches!(i.backend.as_str(), "kernel" | "native") {
                self.err(format!("{what}: backend is not kernel or native"));
                continue;
            }
            let key = (i.procedure.clone(), i.backend.clone(), profile.clone());
            if impls.insert(key, i.implemented).is_some() {
                self.err(format!("{what}: declared twice"));
                continue;
            }
            t.impls.push(TrustImplementation {
                procedure: i.procedure.clone(),
                backend: i.backend.clone(),
                profile,
                decl: i.decl.clone(),
                implemented: i.implemented,
                surface: i.surface.clone(),
                doc: i.doc.clone(),
            });
        }

        // ---- sets
        let mut sets: BTreeMap<String, Vec<(String, Option<Grant>)>> = BTreeMap::new();
        for s in &d.sets {
            if sets.contains_key(&s.name) {
                self.err(format!("set {}: declared twice", s.name));
                continue;
            }
            let mut ms = Vec::new();
            for m in &s.members {
                match (&m.procedure, &m.set) {
                    (Some(p), None) => {
                        let Some(kind) = kinds.get(p) else {
                            self.err(format!("set {}: unknown procedure {p}", s.name));
                            continue;
                        };
                        let backend = m.backend.clone().unwrap_or_else(|| {
                            (if kind == "axiom" { "axiom" } else { "kernel" }).into()
                        });
                        let profile = m.profile.clone().unwrap_or_default();
                        let ok = if kind == "axiom" {
                            backend == "axiom" && profile.is_empty()
                        } else {
                            impls.keys().any(|(ip, ib, iprof)| {
                                ip == p
                                    && *ib == backend
                                    && (profile.is_empty() || *iprof == profile)
                            })
                        };
                        if !ok {
                            self.err(format!(
                                "set {}: no implementation of {p} with backend {backend:?} and profile {profile:?}",
                                s.name
                            ));
                            continue;
                        }
                        ms.push((p.clone(), Some((p.clone(), backend, profile))));
                    }
                    (None, Some(n)) if m.backend.is_none() && m.profile.is_none() => {
                        ms.push((n.clone(), None))
                    }
                    _ => self.err(format!(
                        "set {}: a member is {{procedure, backend?, profile?}} or {{set}}",
                        s.name
                    )),
                }
            }
            sets.insert(s.name.clone(), ms);
        }
        let std_grants: Vec<(String, Option<Grant>)> = STANDARD_AXIOMS
            .iter()
            .map(|a| {
                (
                    a.to_string(),
                    Some((a.to_string(), "axiom".into(), String::new())),
                )
            })
            .collect();
        match sets.get(STANDARD_SET) {
            Some(ms) => {
                let mut a: Vec<_> = ms.clone();
                a.sort();
                let mut b = std_grants.clone();
                b.sort();
                if a != b {
                    self.err(format!("set {STANDARD_SET}: must be exactly the standard axioms {STANDARD_AXIOMS:?}"));
                }
            }
            None => {
                sets.insert(STANDARD_SET.into(), std_grants);
            }
        }
        let builtin_standard = !d.sets.iter().any(|s| s.name == STANDARD_SET);
        for (name, ms) in &sets {
            for (m, g) in ms {
                if g.is_none() && !sets.contains_key(m) {
                    self.err(format!("set {name}: unknown set {m}"));
                }
            }
        }
        // Closures, rejecting cycles.
        let mut closure: BTreeMap<String, BTreeSet<Grant>> = BTreeMap::new();
        fn close(
            n: &str,
            sets: &BTreeMap<String, Vec<(String, Option<Grant>)>>,
            closure: &mut BTreeMap<String, BTreeSet<Grant>>,
            stack: &mut Vec<String>,
            cycles: &mut BTreeSet<String>,
        ) -> BTreeSet<Grant> {
            if let Some(c) = closure.get(n) {
                return c.clone();
            }
            if stack.iter().any(|s| s == n) {
                let from = stack.iter().position(|s| s == n).unwrap();
                let mut cyc = stack[from..].to_vec();
                cyc.push(n.into());
                cycles.insert(cyc.join(" -> "));
                return BTreeSet::new();
            }
            stack.push(n.into());
            let mut out = BTreeSet::new();
            for (m, g) in sets.get(n).into_iter().flatten() {
                match g {
                    Some(g) => {
                        out.insert(g.clone());
                    }
                    None => out.extend(close(m, sets, closure, stack, cycles)),
                }
            }
            stack.pop();
            closure.insert(n.into(), out.clone());
            out
        }
        let mut cycles = BTreeSet::new();
        for n in sets.keys() {
            close(n, &sets, &mut closure, &mut Vec::new(), &mut cycles);
        }
        for c in cycles {
            self.err(format!("set cycle {c}"));
        }
        for (name, ms) in &sets {
            let doc = d
                .sets
                .iter()
                .find(|s| &s.name == name)
                .and_then(|s| s.doc.clone());
            let builtin = name == STANDARD_SET && builtin_standard;
            t.sets.push(TrustSet {
                name: name.clone(),
                builtin,
                doc: if builtin {
                    Some("the standard axioms".into())
                } else {
                    doc
                },
            });
            for (m, g) in ms {
                let (kind, backend, profile) = match g {
                    Some((_, b, p)) => ("procedure", b.clone(), p.clone()),
                    None => ("set", String::new(), String::new()),
                };
                t.members.push(TrustSetMember {
                    set_name: name.clone(),
                    member_kind: kind.into(),
                    member: m.clone(),
                    backend,
                    profile,
                });
            }
        }
        let grants = |names: &[String]| -> BTreeSet<Grant> {
            names
                .iter()
                .flat_map(|n| closure.get(n).cloned().unwrap_or_default())
                .collect()
        };

        // ---- policies
        let mut policies: BTreeMap<(String, String), &PolicyDecl> = BTreeMap::new();
        for p in &d.policies {
            let what = format!("policy {} {:?}", p.scope, p.name);
            let shape_ok = match p.scope.as_str() {
                "root" => p.name.is_empty(),
                "region" | "module" => !p.name.is_empty() && !p.name.contains('*'),
                "prefix" => p
                    .name
                    .strip_suffix(".*")
                    .is_some_and(|s| !s.is_empty() && !s.contains('*')),
                _ => false,
            };
            if !shape_ok {
                self.err(format!(
                    "{what}: a scope is root (name \"\"), region NAME, prefix A.B.* or module NAME"
                ));
                continue;
            }
            for n in p.allow.iter().chain(&p.max).flatten() {
                if !sets.contains_key(n) {
                    self.err(format!("{what}: unknown set {n}"));
                }
            }
            if let (Some(a), Some(m)) = (&p.allow, &p.max) {
                let (a, m) = (grants(a), grants(m));
                if let Some(g) = a.iter().find(|g| !covers(&m, g)) {
                    self.err(format!("{what}: allow grants {g:?} beyond its own max"));
                }
            }
            if policies
                .insert((p.scope.clone(), p.name.clone()), p)
                .is_some()
            {
                self.err(format!(
                    "{what}: declared twice (overlapping policies are rejected)"
                ));
            }
        }
        let std_names = vec![STANDARD_SET.to_string()];
        let root_builtin = PolicyDecl {
            scope: "root".into(),
            name: String::new(),
            allow: Some(std_names.clone()),
            max: Some(std_names.clone()),
            origin: Some("built-in default".into()),
        };
        let has_root = policies.contains_key(&("root".into(), String::new()));
        if !has_root {
            policies.insert(("root".into(), String::new()), &root_builtin);
        }
        for ((kind, name), p) in &policies {
            let builtin = kind == "root" && !has_root;
            t.policies.push(TrustPolicy {
                scope_kind: kind.clone(),
                scope: name.clone(),
                builtin,
                origin: p.origin.clone(),
            });
            for (role, sets) in [("allow", &p.allow), ("max", &p.max)] {
                for s in sets.iter().flatten().collect::<BTreeSet<_>>() {
                    t.policy_sets.push(TrustPolicySet {
                        scope_kind: kind.clone(),
                        scope: name.clone(),
                        role: role.into(),
                        set_name: s.clone(),
                    });
                }
            }
        }

        // ---- modules, coverage, freshness
        let mut described: BTreeMap<String, &ModuleDecl> = BTreeMap::new();
        for m in &d.modules {
            if described.insert(m.name.clone(), m).is_some() {
                self.err(format!("module {}: described twice", m.name));
            }
        }
        let mut excluded: BTreeMap<String, &ExcludedDecl> = BTreeMap::new();
        for e in &d.excluded {
            if !matches!(e.coverage.as_str(), "excluded" | "unsupported") {
                self.err(format!(
                    "excluded {}: coverage {:?} is not excluded or unsupported",
                    e.module, e.coverage
                ));
            }
            if excluded.insert(e.module.clone(), e).is_some() {
                self.err(format!("excluded {}: listed twice", e.module));
            }
        }
        let mut imports: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for m in described.values() {
            let set = imports.entry(m.name.clone()).or_default();
            for i in &m.imports {
                if !set.insert(i.clone()) {
                    self.err(format!("module {}: imports {i} twice", m.name));
                }
            }
        }
        let mut src_status: BTreeMap<String, &'static str> = BTreeMap::new();
        for m in described.values() {
            let st = match (&m.source, &m.source_sha256) {
                (Some(s), Some(h)) => status(h, &sha256_of(self.dir, s)),
                _ => "unrecorded",
            };
            src_status.insert(m.name.clone(), st);
        }
        // A module is stale when its own source or a described import's (transitively) is.
        let mut deps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for n in described.keys() {
            let mut seen = BTreeSet::new();
            let mut todo: Vec<String> = imports[n].iter().cloned().collect();
            while let Some(x) = todo.pop() {
                if seen.insert(x.clone()) {
                    todo.extend(imports.get(&x).into_iter().flatten().cloned());
                }
            }
            seen.remove(n);
            deps.insert(n.clone(), seen);
        }
        let global_ok = toolchain_status == "match" && inputs_ok;
        let global_known = toolchain_status != "missing";
        let mut all: BTreeSet<String> = described.keys().cloned().collect();
        all.extend(excluded.keys().cloned());
        all.extend(imports.values().flatten().cloned());
        for n in &all {
            let m = described.get(n);
            let ss = src_status.get(n).copied().unwrap_or("unrecorded");
            let freshness = if m.is_none() {
                "unknown"
            } else {
                let mine = std::iter::once(n)
                    .chain(&deps[n])
                    .filter_map(|x| src_status.get(x));
                let bad = mine.clone().any(|s| matches!(*s, "changed" | "missing"));
                if bad || (global_known && !global_ok) {
                    "stale"
                } else if !global_known || mine.into_iter().any(|s| *s == "unrecorded") {
                    "unknown"
                } else {
                    "consistent"
                }
            };
            let (coverage, reason) = match (excluded.get(n), m) {
                (Some(e), _) => (e.coverage.clone(), Some(e.reason.clone())),
                (None, Some(_)) => ("covered".into(), None),
                (None, None) => (
                    "undescribed".into(),
                    Some("imported by a described module; not in the trust dump".into()),
                ),
            };
            t.modules.push(TrustModule {
                name: n.clone(),
                region: m.and_then(|m| m.region.clone()),
                source: m.and_then(|m| m.source.clone()),
                source_sha256: m.and_then(|m| m.source_sha256.clone()),
                source_status: ss.into(),
                freshness: freshness.into(),
                coverage,
                reason,
            });
        }
        for (m, is) in &imports {
            for i in is {
                t.imports.push(TrustImport {
                    module: m.clone(),
                    import: i.clone(),
                });
            }
        }

        // ---- effective policy per described module
        let mut allowed: BTreeMap<String, BTreeSet<Grant>> = BTreeMap::new();
        for n in described
            .keys()
            .chain(excluded.keys())
            .collect::<BTreeSet<_>>()
        {
            let region = described.get(n).and_then(|m| m.region.clone());
            let mut chain: Vec<(String, String)> = vec![("root".into(), String::new())];
            if let Some(r) = region {
                chain.push(("region".into(), r));
            }
            let mut prefixes: Vec<&String> = policies
                .keys()
                .filter(|(k, name)| {
                    k == "prefix" && n.starts_with(&format!("{}.", &name[..name.len() - 2]))
                })
                .map(|(_, name)| name)
                .collect();
            prefixes.sort_by_key(|p| p.len());
            chain.extend(prefixes.into_iter().map(|p| ("prefix".into(), p.clone())));
            chain.push(("module".into(), n.clone()));
            let mut allow: (Vec<String>, (String, String)) = (vec![], chain[0].clone());
            let mut max: (Vec<String>, (String, String)) = (vec![], chain[0].clone());
            let mut first = true;
            for scope in chain {
                let Some(p) = policies.get(&scope) else {
                    continue;
                };
                let what = format!("policy {} {:?}", scope.0, scope.1);
                if first {
                    let a = p.allow.clone().unwrap_or_else(|| std_names.clone());
                    let m = p.max.clone().unwrap_or_else(|| a.clone());
                    if let Some(g) = grants(&a).iter().find(|g| !covers(&grants(&m), g)) {
                        self.err(format!("{what}: allow grants {g:?} beyond its own max"));
                    }
                    allow = (a, scope.clone());
                    max = (m, scope.clone());
                    first = false;
                    continue;
                }
                let bound = grants(&max.0);
                for (role, sets) in [("max", &p.max), ("allow", &p.allow)] {
                    if let Some(s) = sets
                        && let Some(g) = grants(s).iter().find(|g| !covers(&bound, g))
                    {
                        self.err(format!(
                            "{what}: {role} grants {g:?}, beyond the max of policy {} {:?} (module {n})",
                            max.1 .0, max.1 .1
                        ));
                    }
                }
                if let Some(m) = &p.max {
                    max = (m.clone(), scope.clone());
                }
                if let Some(a) = &p.allow {
                    allow = (a.clone(), scope.clone());
                } else if p.max.is_some() {
                    let bound = grants(&max.0);
                    if let Some(g) = grants(&allow.0).iter().find(|g| !covers(&bound, g)) {
                        self.err(format!(
                            "{what}: the inherited allow (policy {} {:?}) grants {g:?}, beyond this max; restate allow (module {n})",
                            allow.1 .0, allow.1 .1
                        ));
                    }
                }
            }
            for (role, (names, scope)) in [("allow", &allow), ("max", &max)] {
                for s in names.iter().collect::<BTreeSet<_>>() {
                    t.module_policy.push(TrustModulePolicy {
                        module: n.clone(),
                        role: role.into(),
                        set_name: s.clone(),
                        scope_kind: scope.0.clone(),
                        scope: scope.1.clone(),
                    });
                }
            }
            allowed.insert(n.clone(), grants(&allow.0));
        }

        // ---- uses
        let mut uses: BTreeMap<String, BTreeSet<(String, Grant)>> = BTreeMap::new();
        for u in &d.uses {
            let profile = u.profile.clone().unwrap_or_default();
            let what = format!(
                "use {} {} {} {:?} in {}",
                u.decl, u.procedure, u.backend, profile, u.module
            );
            if !described.contains_key(&u.module) {
                self.err(format!("{what}: the module is not described"));
                continue;
            }
            if excluded.contains_key(&u.module) {
                self.err(format!(
                    "{what}: the module is listed as {}",
                    excluded[&u.module].coverage
                ));
                continue;
            }
            let ok = match kinds.get(&u.procedure).map(String::as_str) {
                None => {
                    self.err(format!("{what}: unknown procedure"));
                    continue;
                }
                Some("axiom") => u.backend == "axiom" && profile.is_empty(),
                Some(_) => {
                    impls.contains_key(&(u.procedure.clone(), u.backend.clone(), profile.clone()))
                }
            };
            if !ok {
                self.err(format!("{what}: no such implementation"));
                continue;
            }
            let g = (u.procedure.clone(), u.backend.clone(), profile.clone());
            if !uses
                .entry(u.module.clone())
                .or_default()
                .insert((u.decl.clone(), g))
            {
                self.err(format!("{what}: listed twice"));
                continue;
            }
            t.uses.push(TrustUse {
                module: u.module.clone(),
                decl: u.decl.clone(),
                procedure: u.procedure.clone(),
                backend: u.backend.clone(),
                profile: profile.clone(),
            });
            for a in u.axioms.iter().collect::<BTreeSet<_>>() {
                t.use_axioms.push(TrustUseAxiom {
                    module: u.module.clone(),
                    decl: u.decl.clone(),
                    procedure: u.procedure.clone(),
                    backend: u.backend.clone(),
                    profile: profile.clone(),
                    axiom: a.clone(),
                });
            }
        }
        for x in d.decls.iter().flatten() {
            if !described.contains_key(&x.module) || excluded.contains_key(&x.module) {
                self.err(format!(
                    "decl {} in {}: the module is not described and covered",
                    x.decl, x.module
                ));
                continue;
            }
            for a in x.axioms.iter().collect::<BTreeSet<_>>() {
                t.decl_axioms.push(TrustDeclAxiom {
                    module: x.module.clone(),
                    decl: x.decl.clone(),
                    axiom: a.clone(),
                });
            }
        }

        // ---- violations (the `trust_violations` view computes the same rows)
        let mut violations: BTreeSet<(String, String, String, String, &'static str)> =
            BTreeSet::new();
        for n in described.keys().filter(|n| !excluded.contains_key(*n)) {
            let allow = &allowed[n];
            for via in std::iter::once(n).chain(&deps[n]) {
                for (decl, g) in uses.get(via).into_iter().flatten() {
                    let shown = format!("{} {} {:?}", g.0, g.1, g.2);
                    if !covers(allow, g) {
                        violations.insert((
                            n.clone(),
                            via.clone(),
                            decl.clone(),
                            shown.clone(),
                            "not-allowed",
                        ));
                    }
                    if impls.get(g) == Some(&false) {
                        violations.insert((
                            n.clone(),
                            via.clone(),
                            decl.clone(),
                            shown,
                            "unimplemented",
                        ));
                    }
                }
            }
        }
        for x in &t.decl_axioms {
            let accounted = t.uses.iter().any(|u| {
                u.module == x.module
                    && u.decl == x.decl
                    && u.procedure == x.axiom
                    && u.backend == "axiom"
            }) || t
                .use_axioms
                .iter()
                .any(|a| a.module == x.module && a.decl == x.decl && a.axiom == x.axiom);
            if !accounted {
                violations.insert((
                    x.module.clone(),
                    x.module.clone(),
                    x.decl.clone(),
                    x.axiom.clone(),
                    "unattributed-axiom",
                ));
            }
        }
        for (m, via, decl, g, why) in &violations {
            let route = if m == via {
                String::new()
            } else {
                format!(" (through {via})")
            };
            self.o.warn(
                format!("trust {m}"),
                format!("{why}: {decl} uses {g}{route}"),
            );
        }

        // ---- report
        let count = |c: &str| t.modules.iter().filter(|m| m.coverage == c).count();
        let fresh = |c: &str| {
            t.modules
                .iter()
                .filter(|m| m.coverage != "undescribed" && m.freshness == c)
                .count()
        };
        let native = t.impls.iter().filter(|i| i.backend == "native").count();
        let unimpl = t.impls.iter().filter(|i| !i.implemented).count();
        let direct = violations.iter().filter(|v| v.0 == v.1).count();
        self.o.lines.push(format!(
            "trust: {} procedures ({} implementations, {native} native, {unimpl} not implemented), {} sets, {} policies",
            t.procedures.len(),
            t.impls.len(),
            t.sets.len(),
            t.policies.len()
        ));
        self.o.lines.push(format!(
            "trust modules: {} covered, {} excluded, {} unsupported, {} undescribed; {} direct uses",
            count("covered"),
            count("excluded"),
            count("unsupported"),
            count("undescribed"),
            t.uses.len()
        ));
        self.o.lines.push(format!(
            "trust violations: {} ({direct} direct, {} transitive){}",
            violations.len(),
            violations.len() - direct,
            if d.decls.is_none() {
                "; axioms per declaration not collected"
            } else {
                ""
            }
        ));
        self.o.lines.push(format!(
            "trust digests: toolchain {toolchain_status}, inputs {}, modules {} consistent, {} stale, {} unknown (consistent digests are not proof of freshness)",
            if inputs_ok { "match" } else { "changed" },
            fresh("consistent"),
            fresh("stale"),
            fresh("unknown")
        ));
        meta(
            self.o,
            &[
                ("status", "present".into()),
                ("schema", d.schema.clone()),
                ("sha256", sha256),
                ("producer", d.producer.clone()),
                ("toolchain", d.toolchain.clone()),
                ("toolchain_status", toolchain_status.into()),
                (
                    "decl_axioms",
                    (if d.decls.is_some() {
                        "collected"
                    } else {
                        "not-collected"
                    })
                    .into(),
                ),
            ],
        );
    }
}
