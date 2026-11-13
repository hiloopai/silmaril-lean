//! `--trust PATH`: check trust lines ([`schema::trust`]) and add their tables to the database.
//!
//! The model is the core trust framework's (`Silmaril.Prelude.Trust`): registered native
//! procedures, trust sets, `[[native.scope]]` scopes with `max`, `default`, `deps` and
//! `axioms`, recorded `edge_decide` uses, and per theorem its axioms, split as `trust_audit`
//! splits them. This module does not decide policy on its own: it **recomputes** each module's
//! effective sets with the core's rules and fails when the producer's differ, then applies the
//! core's audit to every theorem:
//!
//! - an own native run (`<decl>._native.edge.<p>.ax_i_j`) must be `allowed` (the module's sets
//!   for the dump's profile and ceiling);
//! - an inherited native run must be in `deps`;
//! - a native run outside `edge_decide` (`decide +native`, `bv_decide`) is never allowed;
//! - every other axiom must be in `axioms`.
//!
//! Errors (no database): an unsupported schema, a malformed or duplicate line, an unknown
//! procedure, set or module, a set cycle, a scope beyond its parent's `max`, an effective set
//! that differs from the recomputed one, or a split of axioms that differs from the axiom names.
//! Violations of the audit are warnings and rows of `trust_violations`; with `--strict-trust`
//! they are errors, as are inconsistent digests, undescribed imports and a missing dump. Without
//! `--trust`, `meta` says `trust.status = absent`: unaudited, not clean.

use super::check::Outcome;
use super::hash::Digests;
use super::schema::*;
use miette::{IntoDiagnostic, Result, WrapErr};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

/// A resolved set, as the core's `Members`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Members {
    All,
    Some(BTreeSet<String>),
}

impl Members {
    fn none() -> Self {
        Members::Some(BTreeSet::new())
    }
    fn contains(&self, n: &str) -> bool {
        match self {
            Members::All => true,
            Members::Some(s) => s.contains(n),
        }
    }
    fn inter(&self, o: &Members) -> Members {
        match (self, o) {
            (Members::All, m) | (m, Members::All) => m.clone(),
            (Members::Some(a), Members::Some(b)) => {
                Members::Some(a.intersection(b).cloned().collect())
            }
        }
    }
    fn subset(&self, o: &Members) -> bool {
        match (self, o) {
            (_, Members::All) => true,
            (Members::All, Members::Some(_)) => false,
            (Members::Some(a), Members::Some(b)) => a.is_subset(b),
        }
    }
    fn of(l: &LineMembers) -> Members {
        if l.all {
            Members::All
        } else {
            Members::Some(l.names.iter().cloned().collect())
        }
    }
    /// Rows of `trust_module_policy` (`*` is `all`).
    fn names(&self) -> Vec<String> {
        match self {
            Members::All => vec!["*".into()],
            Members::Some(s) => s.iter().cloned().collect(),
        }
    }
    fn show(&self) -> String {
        match self {
            Members::All => "all".into(),
            Members::Some(s) => format!("{{{}}}", s.iter().cloned().collect::<Vec<_>>().join(", ")),
        }
    }
}

/// `p` is a prefix of the module name `m` (as `Name.isPrefixOf`: equal, or `p.` starts `m`).
fn name_prefix(p: &str, m: &str) -> bool {
    m == p || m.starts_with(&format!("{p}."))
}

/// `_private.M.0.x.y` → `x.y` (as `privateToUserName?`).
fn user_name(n: &str) -> &str {
    match n.strip_prefix("_private.") {
        Some(rest) => rest.find(".0.").map_or(n, |i| &rest[i + 3..]),
        None => n,
    }
}

/// The core's `nativeAxiom?`: for `d._native.edge.p.ax_i_j`, `(d, p, true)`; for
/// `d._native.tac.ax_i_j`, `(d, tac, false)`.
pub fn native_axiom(n: &str) -> Option<(String, String, bool)> {
    let i = n.find("._native.")?;
    let owner = user_name(&n[..i]).to_string();
    let rest = &n[i + "._native.".len()..];
    let mid = rest.rsplit_once('.').map_or("", |(a, _)| a);
    Some(match mid.strip_prefix("edge.") {
        Some(p) => (owner, p.to_string(), true),
        None => (owner, mid.to_string(), false),
    })
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

fn enforcement(strict: bool) -> &'static str {
    if strict { "strict" } else { "report-only" }
}

/// Said on every run, so that a report is never mistaken for enforcement.
fn enforcement_line(strict: bool) -> String {
    if strict {
        "trust policy: enforced (--strict-trust): violations and incomplete evidence are errors"
            .into()
    } else {
        "trust policy: NOT enforced (report only): violations are warnings and rows of \
         trust_violations; validate with --strict-trust"
            .into()
    }
}

#[derive(Default)]
struct Tables {
    inputs: Vec<TrustInput>,
    procedures: Vec<TrustProcedure>,
    sets: Vec<TrustSet>,
    members: Vec<TrustSetMember>,
    scopes: Vec<TrustScope>,
    modules: Vec<TrustModule>,
    imports: Vec<TrustImport>,
    module_policy: Vec<TrustModulePolicy>,
    uses: Vec<TrustUse>,
    decls: Vec<TrustDecl>,
    decl_axioms: Vec<TrustDeclAxiom>,
    audit_messages: Vec<TrustAuditMessage>,
}

impl Tables {
    fn push(self, db: &mut Database) {
        db.push(&self.inputs);
        db.push(&self.procedures);
        db.push(&self.sets);
        db.push(&self.members);
        db.push(&self.scopes);
        db.push(&self.modules);
        db.push(&self.imports);
        db.push(&self.module_policy);
        db.push(&self.uses);
        db.push(&self.decls);
        db.push(&self.decl_axioms);
        db.push(&self.audit_messages);
    }
}

/// Read trust lines: one JSON object per non-empty line, each with a `schema` of
/// [`LINE_KINDS`] and a `kind` that schema carries. The conversion is explicit: a core line and
/// an adapter line of the same kind map to the same [`TrustLine`] variant. Adapter fields must
/// all be known; core fields outside [`CORE_FIELDS`] (the core may add fields within v1) are
/// dropped and returned as `kind.field`.
pub fn read_lines(text: &str) -> std::result::Result<(Vec<TrustLine>, BTreeSet<String>), String> {
    let mut out = Vec::new();
    let mut ignored = BTreeSet::new();
    for (i, l) in text
        .lines()
        .enumerate()
        .filter(|(_, l)| !l.trim().is_empty())
    {
        let at = |e: String| format!("line {}: {e}", i + 1);
        let mut v: serde_json::Value = serde_json::from_str(l).map_err(|e| at(e.to_string()))?;
        let obj = v
            .as_object_mut()
            .ok_or_else(|| at("not a JSON object".into()))?;
        let schema = match obj.remove("schema") {
            Some(serde_json::Value::String(s)) => s,
            _ => return Err(at("no `schema`".into())),
        };
        let kind = obj
            .get("kind")
            .and_then(|k| k.as_str())
            .unwrap_or_default()
            .to_string();
        let Some((_, kinds)) = LINE_KINDS.iter().find(|(s, _)| *s == schema) else {
            return Err(at(format!("unsupported schema {schema:?}")));
        };
        if !kinds.contains(&kind.as_str()) {
            return Err(at(format!("kind {kind:?} is not a {schema} kind")));
        }
        if schema == CORE_SCHEMA
            && let Some((_, known)) = CORE_FIELDS.iter().find(|(k, _)| *k == kind)
        {
            let extra: Vec<String> = obj
                .keys()
                .filter(|f| *f != "kind" && !known.contains(&f.as_str()))
                .cloned()
                .collect();
            for f in extra {
                obj.remove(&f);
                ignored.insert(format!("{kind}.{f}"));
            }
        }
        let bad = |e: serde_json::Error| at(format!("{schema} {kind}: {e}"));
        match (schema.as_str(), kind.as_str()) {
            (CORE_SCHEMA, "module") => {
                obj.remove("kind");
                let m: CoreModule = serde_json::from_value(v).map_err(bad)?;
                out.extend(core_module(m).map_err(at)?);
            }
            (CORE_SCHEMA, "audit") => {
                obj.remove("kind");
                let a: CoreAudit = serde_json::from_value(v).map_err(bad)?;
                out.push(TrustLine::Decl(LineDecl {
                    decl: a.decl,
                    module: a.module,
                    own_native: a.own_native,
                    dep_native: a.dep_native,
                    unverified: a
                        .unverified_native
                        .into_iter()
                        .map(|u| (u.procedure, u.axiom))
                        .collect(),
                    axioms: a.axioms,
                    native_axioms: a.native_axioms,
                    profile: Some(a.profile),
                    elaborated_profiles: a.elaborated_profiles,
                    violations: a.violations,
                }));
            }
            _ => out.push(serde_json::from_value(v).map_err(bad)?),
        }
    }
    Ok((out, ignored))
}

/// A core set value: `"all"` or a list of names.
fn core_members(v: &Option<serde_json::Value>) -> std::result::Result<Option<LineMembers>, String> {
    match v {
        None | Some(serde_json::Value::Null) => Ok(None),
        Some(serde_json::Value::String(a)) if a == "all" => Ok(Some(LineMembers {
            all: true,
            names: vec![],
        })),
        Some(serde_json::Value::Array(xs)) => xs
            .iter()
            .map(|x| x.as_str().map(String::from))
            .collect::<Option<Vec<_>>>()
            .map(|names| Some(LineMembers { all: false, names }))
            .ok_or_else(|| "a set is \"all\" or a list of names".into()),
        Some(other) => Err(format!("a set is \"all\" or a list of names, not {other}")),
    }
}

/// The core's `module` line is a module (imports) and its effective sets.
fn core_module(m: CoreModule) -> std::result::Result<Vec<TrustLine>, String> {
    let module = TrustLine::Module(LineModule {
        name: m.module.clone(),
        imports: m.imports,
    });
    let eff = LineEffective {
        module: m.module,
        max: core_members(&m.max)?,
        default: core_members(&m.default)?,
        deps: core_members(&m.deps)?,
        axioms: core_members(&m.axioms)?,
        allowed: core_members(&m.allowed)?,
        trace: m.scopes,
        error: m.policy_error,
        profile: Some(m.profile),
        ceiling: Some(m.ceiling),
    };
    Ok(vec![module, TrustLine::Effective(eff)])
}

/// Check the trust lines at `path` (relative to `dir`), if any, and append the trust tables to
/// `o.db` (which `check` has filled up to the summary table).
pub fn run(dir: &Path, path: Option<&Path>, strict: bool, o: &mut Outcome) -> Result<()> {
    let Some(path) = path else {
        meta(o, &[("status", "absent".into())]);
        if strict {
            o.error(
                "--strict-trust",
                "no trust dump (--trust): use is unaudited",
            );
        }
        o.lines.push(
            "trust: no trust dump (--trust): native-procedure and axiom use is unaudited \
             (unknown, not clean)"
                .into(),
        );
        o.lines.push(enforcement_line(strict));
        meta(o, &[("enforcement", enforcement(strict).into())]);
        Tables::default().push(&mut o.db);
        return Ok(());
    };
    let bytes = fs::read(dir.join(path))
        .into_diagnostic()
        .wrap_err_with(|| format!("could not read the trust dump {}", path.display()))?;
    let at = path.display().to_string();
    let text = String::from_utf8_lossy(&bytes);
    let (lines, ignored) = match read_lines(&text) {
        Ok(l) => l,
        Err(e) => {
            o.error(&at, e);
            Tables::default().push(&mut o.db);
            return Ok(());
        }
    };
    for f in &ignored {
        let msg =
            format!("core field {f} is not read by this tool (added within silmaril.trust.v1?)");
        if strict {
            o.error(
                &at,
                format!("{msg}; --strict-trust refuses fields it cannot interpret"),
            );
        } else {
            o.warn(&at, msg);
        }
    }
    if !ignored.is_empty() {
        meta(
            o,
            &[(
                "ignored_core_fields",
                ignored.iter().cloned().collect::<Vec<_>>().join(","),
            )],
        );
    }
    let mut t = Tables::default();
    let mut ingest = Ingest {
        dir,
        at: &at,
        strict,
        coverage: "partial",
        o,
    };
    ingest.run(&lines, &mut t, Digests::of(&bytes).sha256);
    let coverage = ingest.coverage;
    t.push(&mut o.db);
    if strict && o.errors.is_empty() {
        // What a passing strict run establishes, and no more.
        o.lines.push(format!(
            "trust result: policy valid on {coverage} coverage{}",
            if coverage == "complete" {
                " of the modules under the dump's roots (the theorems it audits; not a proof \
                 the dump is complete)"
            } else {
                " (not a full audit: excluded, unsupported or undescribed modules are unaudited)"
            }
        ));
    }
    Ok(())
}

struct Ingest<'a> {
    dir: &'a Path,
    at: &'a str,
    strict: bool,
    /// `complete` or `partial`, set by [`Ingest::run`].
    coverage: &'static str,
    o: &'a mut Outcome,
}

/// Every line, by kind.
#[derive(Default)]
struct Lines<'a> {
    header: Vec<&'a LineHeader>,
    inputs: Vec<&'a LineInput>,
    policy: Vec<&'a LinePolicy>,
    scopes: Vec<&'a LineScope>,
    sets: Vec<&'a LineSet>,
    procedures: Vec<&'a LineProcedure>,
    uses: Vec<&'a LineUse>,
    modules: Vec<&'a LineModule>,
    effective: Vec<&'a LineEffective>,
    decls: Vec<&'a LineDecl>,
    excluded: Vec<&'a LineExcluded>,
    declared: Vec<&'a LineDeclaredProcedure>,
    sources: Vec<&'a LineSource>,
}

impl Ingest<'_> {
    fn err(&mut self, msg: impl AsRef<str>) {
        self.o.error(self.at, msg);
    }

    /// Resolve a set name as the core's `resolve` (cycles are reported separately).
    fn resolve(
        sets: &BTreeMap<String, &LineSet>,
        n: &str,
        fuel: usize,
    ) -> std::result::Result<Members, String> {
        match n {
            "all" => return Ok(Members::All),
            "none" => return Ok(Members::none()),
            _ => {}
        }
        if fuel == 0 {
            return Err(format!(
                "trust set {n}: includes nest too deeply (a cycle?)"
            ));
        }
        let s = sets
            .get(n)
            .ok_or_else(|| format!("unknown trust set {n}"))?;
        if s.all {
            return Ok(Members::All);
        }
        let mut acc: BTreeSet<String> = s.members.iter().cloned().collect();
        for i in &s.includes {
            match Self::resolve(sets, i, fuel - 1)? {
                Members::All => return Ok(Members::All),
                Members::Some(m) => acc.extend(m),
            }
        }
        Ok(Members::Some(acc))
    }

    fn run(&mut self, all: &[TrustLine], t: &mut Tables, sha256: String) {
        let mut l = Lines::default();
        for x in all {
            match x {
                TrustLine::Header(h) => l.header.push(h),
                TrustLine::Input(i) => l.inputs.push(i),
                TrustLine::Policy(p) => l.policy.push(p),
                TrustLine::Scope(s) => l.scopes.push(s),
                TrustLine::Set(s) => l.sets.push(s),
                TrustLine::Procedure(p) => l.procedures.push(p),
                TrustLine::Use(u) => l.uses.push(u),
                TrustLine::Module(m) => l.modules.push(m),
                TrustLine::Effective(e) => l.effective.push(e),
                TrustLine::Decl(d) => l.decls.push(d),
                TrustLine::Excluded(e) => l.excluded.push(e),
                TrustLine::DeclaredProcedure(d) => l.declared.push(d),
                TrustLine::Source(x) => l.sources.push(x),
            }
        }
        let [h] = l.header[..] else {
            self.err(format!(
                "expected one header line, found {}",
                l.header.len()
            ));
            return;
        };
        if h.core_api != "v1-hooks" {
            self.err(format!("core_api {:?} is not v1-hooks", h.core_api));
            return;
        }
        // The profile and ceiling of the dumping run: the header's, else the module lines'.
        let runs: BTreeSet<(String, String)> = l
            .effective
            .iter()
            .filter_map(|e| Some((e.profile.clone()?, e.ceiling.clone()?)))
            .collect();
        let (profile, ceiling) = match (&h.profile, &h.ceiling, runs.len()) {
            (Some(p), Some(c), _) if runs.iter().all(|(q, d)| q == p && d == c) => {
                (p.clone(), c.clone())
            }
            (None, None, 1) => runs.iter().next().cloned().expect("one"),
            (None, None, 0) => ("default".into(), "local".into()),
            _ => {
                self.err(format!("the lines disagree on the profile and ceiling: header {:?}/{:?}, modules {runs:?}", h.profile, h.ceiling));
                return;
            }
        };
        if l.policy.len() > 1 {
            self.err("more than one policy line");
        }
        let roots: Vec<String> = if h.roots.is_empty() {
            vec!["Silmaril".into()]
        } else {
            h.roots.clone()
        };
        let under = |m: &str| roots.iter().any(|r| name_prefix(r, m));

        // ---- inputs
        let mut seen = BTreeSet::new();
        for i in &l.inputs {
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

        // ---- sets
        let mut sets: BTreeMap<String, &LineSet> = BTreeMap::new();
        for s in &l.sets {
            if s.name == "all" || s.name == "none" {
                self.err(format!("trust set {}: the name is built in", s.name));
                continue;
            }
            if sets.insert(s.name.clone(), s).is_some() {
                self.err(format!("trust set {}: declared twice", s.name));
            }
        }
        for (n, s) in &sets {
            for i in &s.includes {
                if !sets.contains_key(i) && i != "all" && i != "none" {
                    self.err(format!("trust set {n}: includes unknown set {i}"));
                }
            }
        }
        let mut resolved: BTreeMap<String, Members> = BTreeMap::new();
        for n in sets.keys() {
            match Self::resolve(&sets, n, sets.len() + 1) {
                Ok(m) => {
                    resolved.insert(n.clone(), m);
                }
                Err(e) if e.contains("cycle") => {
                    self.err(format!("trust set {n}: an include cycle"))
                }
                Err(_) => {} // unknown includes are reported above
            }
        }
        for s in &l.sets {
            let Some(r) = &s.resolved else { continue };
            let theirs = match r {
                serde_json::Value::String(a) if a == "all" => Some(Members::All),
                serde_json::Value::Array(xs) => xs
                    .iter()
                    .map(|x| x.as_str().map(String::from))
                    .collect::<Option<BTreeSet<_>>>()
                    .map(Members::Some),
                _ => None,
            };
            if theirs.is_none() || resolved.get(&s.name) != theirs.as_ref() {
                self.err(format!(
                    "trust set {}: the producer resolves it to {r}, the core's rules to {}",
                    s.name,
                    resolved
                        .get(&s.name)
                        .map_or("nothing".into(), Members::show)
                ));
            }
        }
        for (n, origin) in [("all", "builtin"), ("none", "builtin")] {
            t.sets.push(TrustSet {
                name: n.into(),
                origin: origin.into(),
                is_all: n == "all",
            });
        }
        for (n, s) in &sets {
            t.sets.push(TrustSet {
                name: n.clone(),
                origin: s.origin.clone().unwrap_or_else(|| "trust_set".into()),
                is_all: s.all,
            });
            for m in s.members.iter().collect::<BTreeSet<_>>() {
                t.members.push(TrustSetMember {
                    set_name: n.clone(),
                    member_kind: "name".into(),
                    member: m.clone(),
                });
            }
            for i in s.includes.iter().collect::<BTreeSet<_>>() {
                t.members.push(TrustSetMember {
                    set_name: n.clone(),
                    member_kind: "set".into(),
                    member: i.clone(),
                });
            }
        }
        let set = |n: &str| -> Option<Members> {
            match n {
                "all" => Some(Members::All),
                "none" => Some(Members::none()),
                _ => resolved.get(n).cloned(),
            }
        };

        // ---- procedures and uses
        // name -> (native side exists, kernel side: `fallback` | `declared` | none)
        let mut procs: BTreeMap<String, (bool, Option<&'static str>)> = BTreeMap::new();
        for p in &l.procedures {
            if procs
                .insert(
                    p.name.clone(),
                    (true, p.kernel_fallback.then_some("fallback")),
                )
                .is_some()
            {
                self.err(format!("procedure {}: registered twice", p.name));
                continue;
            }
            if p.native_function.is_some() != p.native_eq.is_some() {
                self.err(format!(
                    "procedure {}: native_function and native_eq come together",
                    p.name
                ));
            }
            t.procedures.push(TrustProcedure {
                name: p.name.clone(),
                kind: (if p.axiom_pattern.is_some() {
                    "native_tactic"
                } else {
                    "native_decider"
                })
                .into(),
                axiom_pattern: p.axiom_pattern.clone(),
                components: (!p.components.is_empty()).then(|| p.components.join(", ")),
                toolchain: p.toolchain.clone(),
                fallback_coverage: p.fallback_coverage.clone(),
                function: p.function.clone(),
                module: Some(p.module.clone()),
                kernel_fallback: p.kernel_fallback,
                native_function: p.native_function.clone(),
                native_eq: p.native_eq.clone(),
                format: p.format.clone(),
                sound: p.sound.clone(),
                doc: p.doc.clone(),
                ..Default::default()
            });
        }
        for d in &l.declared {
            if d.native.is_none() && d.kernel.is_none() {
                self.err(format!("declared procedure {}: no backend", d.name));
            }
            if procs
                .insert(
                    d.name.clone(),
                    (d.native.is_some(), d.kernel.as_ref().map(|_| "declared")),
                )
                .is_some()
            {
                self.err(format!(
                    "procedure {}: registered twice (native_decider and declared, or declared twice)",
                    d.name
                ));
                continue;
            }
            t.procedures.push(TrustProcedure {
                name: d.name.clone(),
                kind: "declared".into(),
                function: d.constant.clone(),
                native_check: d.native.as_ref().map(|x| x.check.clone()),
                native_sound: d.native.as_ref().map(|x| x.sound.clone()),
                kernel_check: d.kernel.as_ref().map(|x| x.check.clone()),
                kernel_sound: d.kernel.as_ref().map(|x| x.sound.clone()),
                format: d.format.clone(),
                doc: d.doc.clone(),
                ..Default::default()
            });
        }
        let mut use_keys = BTreeSet::new();
        for u in &l.uses {
            let what = format!("use of {} in {} ({})", u.procedure, u.decl, u.module);
            let Some(&(native_ok, kernel)) = procs.get(&u.procedure) else {
                self.err(format!("{what}: unknown procedure"));
                continue;
            };
            let kernel_side = match (u.mode.as_str(), &u.axiom) {
                ("native", Some(a)) => {
                    if !native_ok {
                        self.err(format!(
                            "{what}: a native run of a procedure without a native side"
                        ));
                    }
                    if native_axiom(a).map(|(_, q, e)| (q, e)) != Some((u.procedure.clone(), true))
                    {
                        self.err(format!(
                            "{what}: axiom {a} is not a native run of {}",
                            u.procedure
                        ));
                    }
                    ""
                }
                // A kernel run adds no axiom. Without a registered kernel side, the checker it
                // ran is not named by the registry (legacy `elf_leaf`): recorded, not an error.
                ("kernel", None) => kernel.unwrap_or("unregistered"),
                _ => {
                    self.err(format!(
                        "{what}: mode {:?} with axiom {:?}",
                        u.mode, u.axiom
                    ));
                    continue;
                }
            };
            let row = TrustUse {
                module: u.module.clone(),
                decl: u.decl.clone(),
                procedure: u.procedure.clone(),
                mode: u.mode.clone(),
                profile: u.profile.clone(),
                axiom: u.axiom.clone().unwrap_or_default(),
                kernel_side: kernel_side.into(),
            };
            // The core records a use per elaboration; identical rows are one use.
            if use_keys.insert(row.row()) {
                t.uses.push(row);
            }
        }

        // ---- scopes and effective sets (recomputed with the core's rules)
        let mut scopes: BTreeMap<String, &LineScope> = BTreeMap::new();
        for s in &l.scopes {
            if scopes.insert(s.module.clone(), s).is_some() {
                self.err(format!("scope {}: declared twice", s.module));
            }
            for n in [&s.max, &s.default, &s.deps, &s.axioms]
                .into_iter()
                .flatten()
            {
                if set(n).is_none() && !sets.contains_key(n) {
                    self.err(format!("scope {}: unknown trust set {n}", s.module));
                }
            }
            t.scopes.push(TrustScope {
                module: s.module.clone(),
                max: s.max.clone(),
                default_set: s.default.clone(),
                deps: s.deps.clone(),
                axioms: s.axioms.clone(),
            });
        }
        let effective = |m: &str| -> std::result::Result<([Members; 4], Vec<String>), String> {
            let mut chain: Vec<&&LineScope> = scopes
                .values()
                .filter(|s| name_prefix(&s.module, m))
                .collect();
            chain.sort_by_key(|s| s.module.split('.').count());
            if chain.is_empty() {
                return Err(format!("no scope applies to {m}"));
            }
            let get = |n: &Option<String>, cur: &Members| -> std::result::Result<Members, String> {
                match n {
                    Some(n) => set(n).ok_or_else(|| format!("unknown trust set {n}")),
                    None => Ok(cur.clone()),
                }
            };
            let (mut max, mut dflt, mut deps, mut axs) = (
                Members::none(),
                Members::none(),
                Members::none(),
                Members::none(),
            );
            let mut trace = Vec::new();
            for (i, s) in chain.iter().enumerate() {
                let nmax = get(&s.max, &max)?;
                if i > 0 && !nmax.subset(&max) {
                    return Err(format!(
                        "policy scope {}: max exceeds its parent's max",
                        s.module
                    ));
                }
                let nd = get(&s.default, &dflt)?;
                deps = get(&s.deps, &deps)?;
                axs = get(&s.axioms, &axs)?;
                max = nmax;
                dflt = nd.inter(&max);
                trace.push(s.module.clone());
            }
            Ok(([max, dflt, deps, axs], trace))
        };
        let allowed_in =
            |eff: &[Members; 4], profile: &str| -> std::result::Result<Members, String> {
                Ok(match profile {
                    "paranoid" => Members::none(),
                    "local" => eff[0].clone(),
                    "default" => eff[1].clone(),
                    other => set(other)
                        .ok_or_else(|| format!("unknown trust set {other}"))?
                        .inter(&eff[0]),
                })
            };

        // ---- modules
        let mut described: BTreeMap<String, &LineModule> = BTreeMap::new();
        for m in &l.modules {
            if described.insert(m.name.clone(), m).is_some() {
                self.err(format!("module {}: described twice", m.name));
            }
        }
        let mut excluded: BTreeMap<String, &LineExcluded> = BTreeMap::new();
        for e in &l.excluded {
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
            imports.insert(
                m.name.clone(),
                m.imports
                    .iter()
                    .filter(|i| **i != m.name)
                    .cloned()
                    .collect(),
            );
        }
        let mut sources: BTreeMap<String, &LineSource> = BTreeMap::new();
        for x in &l.sources {
            if !described.contains_key(&x.module) {
                self.err(format!("source {}: the module is not described", x.module));
            }
            if sources.insert(x.module.clone(), x).is_some() {
                self.err(format!("source {}: listed twice", x.module));
            }
        }
        let mut src_status: BTreeMap<String, &'static str> = BTreeMap::new();
        for m in described.values() {
            let st = match sources.get(&m.name) {
                Some(x) => status(&x.sha256, &sha256_of(self.dir, &x.path)),
                None => "unrecorded",
            };
            src_status.insert(m.name.clone(), st);
        }
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

        // Effective sets: the producer's must equal the recomputed ones.
        let mut eff_lines: BTreeMap<String, &LineEffective> = BTreeMap::new();
        for e in &l.effective {
            if eff_lines.insert(e.module.clone(), e).is_some() {
                self.err(format!("effective {}: listed twice", e.module));
            }
        }
        let mut allowed: BTreeMap<String, [Members; 5]> = BTreeMap::new();
        let mut traces: BTreeMap<String, String> = BTreeMap::new();
        for n in described.keys() {
            let mine = effective(n).and_then(|(e, tr)| {
                let a = allowed_in(&e, &profile)?.inter(&allowed_in(&e, &ceiling)?);
                let [a0, a1, a2, a3] = e;
                Ok(([a0, a1, a2, a3, a], tr))
            });
            let theirs = eff_lines.get(n);
            match (mine, theirs) {
                (_, None) => self.err(format!("module {n}: no effective line")),
                (Err(e), Some(x)) => {
                    let why = x
                        .error
                        .clone()
                        .unwrap_or_else(|| "the producer resolved it".into());
                    self.err(format!(
                        "module {n}: policy does not resolve: {e} (producer: {why})"
                    ));
                }
                (Ok(_), Some(x)) if x.error.is_some() => self.err(format!(
                    "module {n}: the producer could not resolve its policy: {}",
                    x.error.as_deref().unwrap_or_default()
                )),
                (Ok((sets5, tr)), Some(x)) => {
                    let got = [&x.max, &x.default, &x.deps, &x.axioms, &x.allowed];
                    for (role, (want, got)) in ["max", "default", "deps", "axioms", "allowed"]
                        .iter()
                        .zip(sets5.iter().zip(got))
                    {
                        let got = got.as_ref().map(Members::of);
                        if got.as_ref() != Some(want) {
                            self.err(format!(
                                "module {n}: effective {role} is {} by the producer but {} by the core's rules",
                                got.map_or("missing".into(), |g| g.show()),
                                want.show()
                            ));
                        }
                    }
                    if x.trace != tr {
                        self.err(format!(
                            "module {n}: policy trace {:?} differs from {tr:?}",
                            x.trace
                        ));
                    }
                    for (role, m) in ["max", "default", "deps", "axioms", "allowed"]
                        .iter()
                        .zip(sets5.iter())
                    {
                        for member in m.names() {
                            t.module_policy.push(TrustModulePolicy {
                                module: n.clone(),
                                role: role.to_string(),
                                member,
                            });
                        }
                    }
                    traces.insert(n.clone(), tr.join(" > "));
                    allowed.insert(n.clone(), sets5);
                }
            }
        }
        for e in eff_lines.keys() {
            if !described.contains_key(e) {
                self.err(format!("effective {e}: the module is not described"));
            }
        }

        // Coverage and freshness.
        let mut all_mods: BTreeSet<String> = described.keys().cloned().collect();
        all_mods.extend(excluded.keys().cloned());
        all_mods.extend(imports.values().flatten().cloned());
        for n in &all_mods {
            let m = described.get(n);
            let ss = src_status.get(n).copied().unwrap_or("unrecorded");
            let freshness = if m.is_none() {
                "unknown"
            } else {
                let mine: Vec<&str> = std::iter::once(n)
                    .chain(&deps[n])
                    .filter_map(|x| src_status.get(x).copied())
                    .collect();
                if !inputs_ok || mine.iter().any(|s| matches!(*s, "changed" | "missing")) {
                    "stale"
                } else if t.inputs.is_empty() || mine.contains(&"unrecorded") {
                    "unknown"
                } else {
                    "consistent"
                }
            };
            let (coverage, reason): (String, Option<String>) = match (excluded.get(n), m) {
                (Some(e), _) => (e.coverage.clone(), Some(e.reason.clone())),
                (None, Some(_)) => ("covered".into(), None),
                (None, None) if !under(n) => (
                    "external".into(),
                    Some("outside the dump's roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems".into()),
                ),
                (None, None) => (
                    "undescribed".into(),
                    Some("imported by a described module; not in the trust dump".into()),
                ),
            };
            t.modules.push(TrustModule {
                name: n.clone(),
                source: sources.get(n).map(|x| x.path.clone()),
                source_sha256: sources.get(n).map(|x| x.sha256.clone()),
                source_status: ss.into(),
                freshness: freshness.into(),
                coverage,
                policy_trace: traces.get(n).cloned(),
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

        // ---- declarations and their axioms (the core's audit lines)
        // A native tactic's axiom `<decl>._native.<tag>.ax_<n>` names its procedure by tag.
        let tags: BTreeMap<String, String> = l
            .procedures
            .iter()
            .filter_map(|p| {
                let pat = p.axiom_pattern.as_deref()?;
                let tag = pat.split("._native.").nth(1)?.rsplit_once(".ax_")?.0;
                Some((tag.to_string(), p.name.clone()))
            })
            .collect();
        let sorted = |v: &[String]| {
            let mut v = v.to_vec();
            v.sort();
            v
        };
        let native_uses: BTreeSet<(&str, &str)> = l
            .uses
            .iter()
            .filter(|u| u.mode == "native")
            .filter_map(|u| Some((u.procedure.as_str(), u.axiom.as_deref()?)))
            .collect();
        let mut seen_decls: BTreeMap<String, &LineDecl> = BTreeMap::new();
        let mut repeated = 0usize;
        let mut core_counts: BTreeMap<String, usize> = BTreeMap::new();
        for d in &l.decls {
            if !described.contains_key(&d.module) {
                self.err(format!(
                    "decl {} in {}: the module is not described",
                    d.decl, d.module
                ));
                continue;
            }
            if let Some(first) = seen_decls.get(&d.decl) {
                // Realized constants (`eq_def`, …) are listed by every module that realizes
                // them (`declsOf`); identical audits of one declaration are one.
                if *first == *d {
                    repeated += 1;
                } else {
                    self.err(format!(
                        "decl {}: listed twice with different audits",
                        d.decl
                    ));
                }
                continue;
            }
            seen_decls.insert(d.decl.clone(), *d);
            if let Some(p) = &d.profile
                && *p != profile
                && !p.starts_with(&format!("{profile}≤"))
            {
                self.err(format!(
                    "decl {}: audited under {p}, not the dump's {profile}",
                    d.decl
                ));
            }
            t.decls.push(TrustDecl {
                decl: d.decl.clone(),
                module: d.module.clone(),
                profile: d.profile.clone(),
                elaborated_profiles: (!d.elaborated_profiles.is_empty())
                    .then(|| d.elaborated_profiles.join(",")),
            });
            for (i, m) in d.violations.iter().enumerate() {
                t.audit_messages.push(TrustAuditMessage {
                    decl: d.decl.clone(),
                    pos: i as i64,
                    message: m.clone(),
                });
            }
            core_counts.insert(d.decl.clone(), d.violations.len());
            let unverified: BTreeMap<&str, &str> = d
                .unverified
                .iter()
                .map(|(p, a)| (a.as_str(), p.as_str()))
                .collect();
            let (mut own, mut dep) = (Vec::new(), Vec::new());
            let mut rows = BTreeMap::new();
            for a in &d.native_axioms {
                let Some((owner, name, edge)) = native_axiom(a) else {
                    self.err(format!("decl {}: {a} is not a native axiom", d.decl));
                    continue;
                };
                if let Some(p) = unverified.get(a.as_str()) {
                    rows.insert(a.clone(), ("unverified_native", p.to_string()));
                    continue;
                }
                let proc = if edge {
                    Some(name.clone())
                } else {
                    tags.get(&name).cloned()
                };
                let Some(p) = proc else {
                    rows.insert(a.clone(), ("plain_native", name));
                    continue;
                };
                // A name or tag match only classifies. The axiom counts as a run of `p` only
                // if a recorded native use of `p` produced exactly this axiom (the core also
                // checks that its statement mentions the evaluated function). Otherwise it is
                // unverified, and if the core called it verified, the counts below disagree.
                if !native_uses.contains(&(p.as_str(), a.as_str())) {
                    rows.insert(a.clone(), ("unverified_native", p));
                    continue;
                }
                let class = if name_prefix(&d.decl, &owner) || name_prefix(&owner, &d.decl) {
                    own.push(p.clone());
                    "own_native"
                } else {
                    dep.push(p.clone());
                    "dep_native"
                };
                rows.insert(a.clone(), (class, p));
            }
            for (p, a) in &d.unverified {
                if !d.native_axioms.contains(a) {
                    self.err(format!(
                        "decl {}: unverified {a} ({p}) is not among its native axioms",
                        d.decl
                    ));
                }
            }
            for a in &d.axioms {
                if native_axiom(a).is_some() {
                    self.err(format!(
                        "decl {}: native axiom {a} listed as an other axiom",
                        d.decl
                    ));
                }
                rows.insert(a.clone(), ("other", String::new()));
            }
            for (what, mine, theirs) in [
                ("own_native", &own, &d.own_native),
                ("dep_native", &dep, &d.dep_native),
            ] {
                if sorted(mine) != sorted(theirs) {
                    self.err(format!(
                        "decl {}: {what} {theirs:?} does not match its native axioms that a recorded use produced ({mine:?})",
                        d.decl
                    ));
                }
            }
            for (a, (class, p)) in rows {
                t.decl_axioms.push(TrustDeclAxiom {
                    module: d.module.clone(),
                    decl: d.decl.clone(),
                    axiom: a,
                    class: class.into(),
                    procedure: p,
                });
            }
        }

        // ---- violations (the `trust_violations` view computes the same rows)
        let covered = |m: &str| described.contains_key(m) && !excluded.contains_key(m);
        let mut violations: BTreeSet<(String, String, String, &'static str)> = BTreeSet::new();
        let mut per_decl: BTreeMap<String, usize> = BTreeMap::new();
        for x in &t.decl_axioms {
            if !covered(&x.module) {
                continue;
            }
            let Some(sets5) = allowed.get(&x.module) else {
                continue;
            };
            let why = match x.class.as_str() {
                "own_native" if !sets5[4].contains(&x.procedure) => "own-native-not-allowed",
                "dep_native" if !sets5[2].contains(&x.procedure) => "dep-native-outside-deps",
                "plain_native" => "unregistered-native",
                "unverified_native" => "unverified-native",
                "other" if !sets5[3].contains(&x.axiom) => "axiom-outside-set",
                _ => continue,
            };
            let subject = if x.class == "other" {
                x.axiom.clone()
            } else {
                x.procedure.clone()
            };
            *per_decl.entry(x.decl.clone()).or_default() += 1;
            violations.insert((x.module.clone(), x.decl.clone(), subject, why));
        }
        // The core's audit is authoritative; the recomputed violations must agree with it.
        for d in t.decls.iter().filter(|d| covered(&d.module)) {
            let (mine, theirs) = (
                per_decl.get(&d.decl).copied().unwrap_or(0),
                core_counts.get(&d.decl).copied().unwrap_or(0),
            );
            if mine != theirs {
                self.err(format!(
                    "decl {}: the core's audit lists {theirs} violation(s), the recomputed audit {mine}",
                    d.decl
                ));
            }
        }
        for (m, decl, subject, why) in &violations {
            let (at, msg) = (format!("trust {m}"), format!("{why}: {decl}: {subject}"));
            if self.strict {
                self.o.error(at, msg);
            } else {
                self.o.warn(at, msg);
            }
        }
        if self.strict {
            for m in t.modules.iter().filter(|m| m.coverage == "covered") {
                if m.freshness != "consistent" {
                    self.o.error(
                        format!("trust {}", m.name),
                        format!(
                            "--strict-trust: digests are {} (source {})",
                            m.freshness, m.source_status
                        ),
                    );
                }
                for dep in deps.get(&m.name).into_iter().flatten() {
                    if t.modules
                        .iter()
                        .any(|x| &x.name == dep && x.coverage == "undescribed")
                    {
                        self.o.error(
                            format!("trust {}", m.name),
                            format!("--strict-trust: imports {dep}, which the trust dump does not describe"),
                        );
                    }
                }
            }
        }

        // ---- report
        let count = |c: &str| t.modules.iter().filter(|m| m.coverage == c).count();
        let fresh = |c: &str| {
            t.modules
                .iter()
                .filter(|m| m.coverage == "covered" && m.freshness == c)
                .count()
        };
        let native_uses = t.uses.iter().filter(|u| u.mode == "native").count();
        let unregistered = t
            .uses
            .iter()
            .filter(|u| u.kernel_side == "unregistered")
            .count();
        let origin = h.origin.clone().unwrap_or_else(|| "unspecified".into());
        self.o.lines.push(format!(
            "trust dump: {} (origin {origin}); profile {}, ceiling {}",
            h.producer.as_deref().unwrap_or("unknown producer"),
            profile,
            ceiling
        ));
        self.o.lines.push(format!(
            "trust: {} procedures ({} with a kernel side), {} sets, {} scopes; {} uses ({native_uses} native, {unregistered} kernel runs of a checker the registry does not name)",
            t.procedures.len(),
            t.procedures.iter().filter(|p| p.kernel_fallback || p.kernel_check.is_some()).count(),
            t.sets.len(),
            t.scopes.len(),
            t.uses.len()
        ));
        self.o.lines.push(format!(
            "trust modules: {} covered, {} excluded, {} unsupported, {} undescribed, {} external; {} declarations audited{}{}",
            count("covered"),
            count("excluded"),
            count("unsupported"),
            count("undescribed"),
            count("external"),
            t.decls.iter().filter(|d| covered(&d.module)).count(),
            {
                let skipped = t.decls.iter().filter(|d| !covered(&d.module)).count();
                if skipped > 0 { format!(" ({skipped} more in excluded modules, listed but not audited)") } else { String::new() }
            },
            if repeated > 0 { format!(" ({repeated} repeated audit lines of realized constants merged)") } else { String::new() }
        ));
        let by = |w: &str| violations.iter().filter(|v| v.3 == w).count();
        self.o.lines.push(format!(
            "trust violations: {} ({} own native not allowed, {} inherited native outside deps, {} unregistered native, {} unverified native, {} axioms outside the set)",
            violations.len(),
            by("own-native-not-allowed"),
            by("dep-native-outside-deps"),
            by("unregistered-native"),
            by("unverified-native"),
            by("axiom-outside-set")
        ));
        self.o.lines.push(format!(
            "trust digests: inputs {}, covered modules {} consistent, {} stale, {} unknown (consistent digests are not proof of freshness)",
            if t.inputs.is_empty() { "none recorded" } else if inputs_ok { "match" } else { "changed" },
            fresh("consistent"),
            fresh("stale"),
            fresh("unknown")
        ));
        let gaps: Vec<String> = ["excluded", "unsupported", "undescribed"]
            .iter()
            .filter(|c| count(c) > 0)
            .map(|c| format!("{} {c}", count(c)))
            .collect();
        let coverage = if gaps.is_empty() {
            "complete"
        } else {
            "partial"
        };
        self.o.lines.push(if gaps.is_empty() {
            "trust coverage: complete (every module under the roots is described and covered; modules outside the roots are external)".into()
        } else {
            format!("trust coverage: partial ({} module(s); their uses are not audited)", gaps.join(", "))
        });
        self.o.lines.push(enforcement_line(self.strict));
        self.coverage = coverage;
        let mut m = vec![
            ("status", "present".to_string()),
            ("enforcement", enforcement(self.strict).into()),
            ("coverage", coverage.into()),
            ("core_api", h.core_api.clone()),
            ("sha256", sha256),
            ("producer", h.producer.clone().unwrap_or_default()),
            ("origin", origin),
            ("toolchain", h.toolchain.clone()),
            ("profile", profile.clone()),
            ("ceiling", ceiling.clone()),
            ("roots", roots.join(" ")),
        ];
        let mut pins: BTreeSet<(String, String)> = l
            .policy
            .iter()
            .map(|p| (p.file.clone(), p.pin.clone()))
            .collect();
        for sc in &l.scopes {
            if let (Some(f), Some(p)) = (&sc.policy_file, &sc.policy_pin) {
                pins.insert((f.clone(), p.clone()));
            }
        }
        match pins.len() {
            0 => {}
            1 => {
                let (f, p) = pins.into_iter().next().expect("one");
                m.push(("policy_file", f));
                m.push(("policy_pin", p));
            }
            _ => self.err(format!(
                "the lines name more than one policy file or pin: {pins:?}"
            )),
        }
        meta(
            self.o,
            &m.iter().map(|(k, v)| (*k, v.clone())).collect::<Vec<_>>(),
        );
    }
}

// ---------------------------------------------------------------- the producer

const DRIVER: &str = include_str!("Driver.lean");

/// Whether the core under `dir` (the package itself or `.lake/packages/silmaril`) has the stable
/// dump hooks (`moduleLine`, `auditLine`, #125 from `ba1b5f84`).
pub fn core_has_hooks(dir: &Path) -> Option<bool> {
    let rel = "Silmaril/Prelude/Trust/Elab/Defs.lean";
    [dir.join(rel), dir.join(".lake/packages/silmaril").join(rel)]
        .iter()
        .find_map(|p| fs::read_to_string(p).ok())
        .map(|t| t.contains("def moduleLine") && t.contains("def auditLine"))
}

fn lean_name_list(names: &[String]) -> String {
    let quoted: Vec<String> = names
        .iter()
        .map(|n| {
            format!(
                "`{}",
                n.split('.')
                    .map(|c| format!("«{c}»"))
                    .collect::<Vec<_>>()
                    .join(".")
            )
        })
        .collect();
    format!("[{}]", quoted.join(", "))
}

fn lean_str(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// The trust driver: imports `modules`, writes the core's lines (stable hooks) for the modules
/// under `roots` to `core_out`, and the adapter's to `out`.
pub fn driver(modules: &[String], roots: &[String], out: &Path, core_out: &Path) -> String {
    DRIVER
        .replace(
            "__IMPORTS__",
            &modules
                .iter()
                .map(|m| format!("import {m}"))
                .collect::<Vec<_>>()
                .join("\n"),
        )
        .replace("__ROOTS__", &lean_name_list(roots))
        .replace("__OUT__", &lean_str(&out.display().to_string()))
        .replace("__CORE_OUT__", &lean_str(&core_out.display().to_string()))
}

/// What `complete` adds besides the driver's lines.
pub struct Completion<'a> {
    pub roots: &'a [String],
    pub producer: &'a str,
    /// Files to record by digest, when they exist.
    pub inputs: &'a [&'a str],
    /// `(module, reason)`: modules whose theorems are not audited (`excluded`).
    pub excluded: &'a [(String, String)],
}

/// Complete the lines: the adapter's (producer, origin and roots in the header; the inputs; a
/// `source` line, with its digest, for every core `module` line whose `<dir>/<A/B/C>.lean`
/// exists; the exclusions), then the core's lines as they are, each checked to be
/// `silmaril.trust.v1`. Line order is kept.
pub fn complete(
    adapter: &str,
    core: &str,
    dir: &Path,
    c: &Completion,
) -> std::result::Result<String, String> {
    let tag = |mut v: serde_json::Value| -> String {
        if let Some(o) = v.as_object_mut() {
            o.insert("schema".into(), ADAPTER_SCHEMA.into());
        }
        serde_json::to_string(&v).expect("json")
    };
    let mut core_lines = Vec::new();
    let mut modules = Vec::new();
    for (i, l) in core
        .lines()
        .enumerate()
        .filter(|(_, l)| !l.trim().is_empty())
    {
        let v: serde_json::Value =
            serde_json::from_str(l).map_err(|e| format!("core line {}: {e}", i + 1))?;
        if v.get("schema").and_then(|s| s.as_str()) != Some(CORE_SCHEMA) {
            return Err(format!("core line {}: schema is not {CORE_SCHEMA}", i + 1));
        }
        if v.get("kind").and_then(|k| k.as_str()) == Some("module")
            && let Some(m) = v.get("module").and_then(|m| m.as_str())
        {
            modules.push(m.to_string());
        }
        core_lines.push(serde_json::to_string(&v).expect("json"));
    }
    let mut out = Vec::new();
    for (i, l) in adapter
        .lines()
        .enumerate()
        .filter(|(_, l)| !l.trim().is_empty())
    {
        let mut v: serde_json::Value =
            serde_json::from_str(l).map_err(|e| format!("adapter line {}: {e}", i + 1))?;
        let obj = v
            .as_object_mut()
            .ok_or_else(|| format!("adapter line {}: not an object", i + 1))?;
        if obj.get("kind").and_then(|k| k.as_str()) == Some("header") {
            obj.insert("producer".into(), c.producer.into());
            obj.insert("origin".into(), "lean".into());
            obj.insert("roots".into(), serde_json::json!(c.roots));
            out.push(tag(v));
            for p in c.inputs {
                if let Some(h) = sha256_of(dir, p) {
                    out.push(tag(
                        serde_json::json!({"kind": "input", "path": p, "sha256": h}),
                    ));
                }
            }
            for m in &modules {
                let path = format!("{}.lean", m.replace('.', "/"));
                if let Some(h) = sha256_of(dir, &path) {
                    out.push(tag(serde_json::json!({"kind": "source", "module": m, "path": path, "sha256": h})));
                }
            }
            continue;
        }
        out.push(tag(v));
    }
    for (m, why) in c.excluded {
        out.push(tag(serde_json::json!({"kind": "excluded", "module": m, "coverage": "excluded", "reason": why})));
    }
    out.extend(core_lines);
    Ok(out.join("\n") + "\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_axiom_names() {
        assert_eq!(
            native_axiom("_private.M.0.A.b._native.edge.bytes.sameBytes.ax_1_1"),
            Some(("A.b".into(), "bytes.sameBytes".into(), true))
        );
        assert_eq!(
            native_axiom("A.b._native.bv_decide.ax_1_2"),
            Some(("A.b".into(), "bv_decide".into(), false))
        );
        assert_eq!(native_axiom("propext"), None);
        assert!(name_prefix("Silmaril", "Silmaril.X") && name_prefix("Silmaril", "Silmaril"));
        assert!(!name_prefix("Silmaril", "SilmarilX"));
    }

    #[test]
    fn driver_and_completion() {
        let p = Path::new("/tmp/x \"q\".jsonl");
        let d = driver(
            &["A.B".into()],
            &["Silmaril".into()],
            p,
            Path::new("/c.jsonl"),
        );
        assert!(d.contains("import A.B\n") && d.contains("[`«Silmaril»]"));
        assert!(d.contains(r#""/tmp/x \"q\".jsonl""#) && d.contains(r#""/c.jsonl""#));
        assert!(d.contains("moduleLine") && d.contains("auditLine") && !d.contains("__"));
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir_all(dir.path().join("A")).unwrap();
        fs::write(dir.path().join("A/B.lean"), "x").unwrap();
        fs::write(dir.path().join("lean-toolchain"), "t").unwrap();
        let adapter = "{\"schema\":\"x\",\"kind\":\"header\",\"core_api\":\"v1-hooks\",\"toolchain\":\"t\"}\n";
        let core = "{\"schema\":\"silmaril.trust.v1\",\"kind\":\"module\",\"module\":\"A.B\",\"imports\":[],\"profile\":\"default\",\"ceiling\":\"local\",\"max\":\"all\",\"default\":[],\"deps\":\"all\",\"axioms\":[],\"allowed\":[],\"scopes\":[\"A\"]}\n";
        let ex = [("A.B".to_string(), "tests".to_string())];
        let c = Completion {
            roots: &["A".into()],
            producer: "p",
            inputs: &["lean-toolchain", "absent"],
            excluded: &ex,
        };
        let out = complete(adapter, core, dir.path(), &c).unwrap();
        let ls: Vec<serde_json::Value> = out
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(ls.len(), 5);
        assert_eq!(ls[0]["origin"], "lean");
        assert_eq!(ls[0]["schema"], ADAPTER_SCHEMA);
        assert_eq!(ls[1]["path"], "lean-toolchain");
        assert_eq!(ls[2]["kind"], "source");
        assert_eq!(ls[3]["kind"], "excluded");
        assert_eq!(ls[4]["schema"], CORE_SCHEMA);
        assert!(complete(adapter, "{\"kind\":\"set\"}", dir.path(), &c).is_err());
        let (lines, ignored) = read_lines(&out).unwrap();
        assert!(ignored.is_empty());
        assert_eq!(
            lines.len(),
            6,
            "a core module line is a module and its effective sets"
        );
        assert!(read_lines("{\"schema\":\"silmaril.trust.v1\",\"kind\":\"header\"}").is_err());
        assert!(read_lines("{\"schema\":\"nope\",\"kind\":\"set\",\"name\":\"s\"}").is_err());
        // A field the core added within v1 is dropped and reported; an adapter field is an error.
        let (_, ignored) = read_lines(
            "{\"schema\":\"silmaril.trust.v1\",\"kind\":\"set\",\"name\":\"s\",\"new_field\":1}",
        )
        .unwrap();
        assert_eq!(ignored.into_iter().collect::<Vec<_>>(), ["set.new_field"]);
        assert!(read_lines("{\"schema\":\"silmaril.trust-adapter.v0.2\",\"kind\":\"input\",\"path\":\"p\",\"sha256\":\"h\",\"x\":1}").is_err());
    }
}
