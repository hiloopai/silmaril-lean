//! `version`: take a `WebAssembly/spec` revision through the SpecTec import and report on it.
//!
//! * `version vendor` — run the SpecTec frontend of a checkout over every
//!   `specification/wasm-*` directory, write the `--ast` streams and a `manifest.json` with
//!   provenance (revision, frontend, SHA-256 of every stream and source), and check them with the
//!   same reader the generator uses (definition counts, byte-for-byte reprint);
//! * `version scripts` — write the streams' `Original` scripts as Lean, under a channel name,
//!   to a scratch directory (never into `Silmaril/`);
//! * `version report` — a Markdown report: what changed against a base revision, the status of
//!   every erratum, the known defects whose declarations changed, and generic lints;
//! * `version lean` — run the Lean checks on the streams through the guarded Lake wrapper
//!   (`scripts/worktree-setup.sh lake`): `Sem.checkStreamFile`, the instruction-shape
//!   crosscheck, and an evaluation of every defect predicate decided by one evaluation
//!   (`Silmaril.Wasm.SpecTec.VersionEval`); its log feeds the report's Lean columns;
//! * `version all` — the three in order (and `--build` builds the frontend first; `--lean` adds
//!   the Lean step before the report).
//!
//! Everything here is unverified tooling; the report says which statements carry over from Lean
//! theorems and which need a Lean re-check.

use crate::{json, sexp, sha256};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The command line the vendored streams were printed with (`specs/spectec/*/README.md`).
const COMMAND: &str = "spectec specification/wasm-N/* --ast-width 80 --ast -o wasm-N.ast";
const AST_WIDTH: usize = 80;
const UPSTREAM: &str = "https://github.com/WebAssembly/spec";
/// The nixpkgs revision the vendored streams' frontends were built with.
const NIXPKGS: &str =
    "https://github.com/NixOS/nixpkgs/archive/da6dc0e7b26060f2f71ce3ef7088fb56ee44fa36.tar.gz";
/// What the frontend built with `NIXPKGS` is, as `manifest.json` records it.
const FRONTEND_BUILD: &str = "dune build src/exe-spectec/main.exe (OCaml 5.4.1, dune 3, menhir 20260203, zarith 1.14 from nixpkgs)";
/// `make exe` of `spectec/Makefile` without its `opam install` step; run in `<checkout>/spectec`
/// with `$NIXPKGS` set.
const BUILD_RECIPE: &str = r#"set -eu
rm -rf src/backend-interpreter/reference-interpreter
cp -R ../interpreter src/backend-interpreter/reference-interpreter
rm -r src/backend-interpreter/reference-interpreter/dune-project src/backend-interpreter/reference-interpreter/jslib
cp src/backend-interpreter/dune-ref-interp src/backend-interpreter/reference-interpreter/dune
nix-shell -I "nixpkgs=$NIXPKGS" -p ocamlPackages.ocaml ocamlPackages.dune_3 ocamlPackages.menhir ocamlPackages.menhirLib ocamlPackages.zarith ocamlPackages.findlib --run 'dune build src/exe-spectec/main.exe'
"#;
const FRONTEND_REL: &str = "spectec/_build/default/src/exe-spectec/main.exe";

/// `--key value` options and bare `--flag`s.
struct Opts {
    vals: BTreeMap<String, String>,
    flags: Vec<String>,
}

impl Opts {
    fn parse(args: &[String], flags: &[&str]) -> Result<Opts, String> {
        let mut o = Opts {
            vals: BTreeMap::new(),
            flags: Vec::new(),
        };
        let mut it = args.iter();
        while let Some(a) = it.next() {
            let k = a
                .strip_prefix("--")
                .ok_or(format!("unexpected argument {a}"))?;
            if flags.contains(&k) {
                o.flags.push(k.to_string());
            } else {
                let v = it.next().ok_or(format!("--{k} needs a value"))?;
                o.vals.insert(k.to_string(), v.clone());
            }
        }
        Ok(o)
    }
    fn get(&self, k: &str) -> Option<&str> {
        self.vals.get(k).map(String::as_str)
    }
    fn need(&self, k: &str) -> Result<&str, String> {
        self.get(k).ok_or(format!("--{k} is required"))
    }
    fn flag(&self, k: &str) -> bool {
        self.flags.iter().any(|f| f == k)
    }
}

const USAGE: &str = "usage: spectec-gen version <command>
  vendor  --checkout DIR --out DIR [--revision REV] [--frontend BIN] [--frontend-revision REV] [--build] [--nixpkgs URL]
  scripts --manifest FILE --channel NAME [--scripts-dir DIR]
  report  --manifest FILE [--base FILE] [--checkout DIR] [--report FILE] [--lean-log FILE]
  lean    --manifest FILE [--log FILE] [--wrapper CMD]
  all     --checkout DIR [--revision REV] [--out DIR] [--build] [--frontend BIN] [--base FILE] [--channel NAME] [--report FILE] [--lean] [--wrapper CMD]";

pub fn run(args: &[String]) -> Result<(), String> {
    let rest = args.get(1..).unwrap_or(&[]);
    match args.first().map(String::as_str) {
        Some("vendor") => {
            let o = Opts::parse(rest, &["build"])?;
            vendor(&o).map(|m| println!("wrote {m}"))
        }
        Some("scripts") => {
            let o = Opts::parse(rest, &[])?;
            let dir = scripts(
                o.need("manifest")?,
                o.need("channel")?,
                o.get("scripts-dir"),
            )?;
            println!("wrote scripts under {dir}");
            Ok(())
        }
        Some("report") => {
            let o = Opts::parse(rest, &[])?;
            let lean_log = o.get("lean-log").map(crate::read).transpose()?;
            let text = report(
                o.need("manifest")?,
                o.get("base").unwrap_or(crate::MAIN_MANIFEST),
                o.get("checkout").map(Path::new),
                None,
                lean_log.as_deref(),
            )?;
            emit_report(&text, o.get("report"))
        }
        Some("lean") => {
            let o = Opts::parse(rest, &[])?;
            let log = lean(o.need("manifest")?, o.get("wrapper").unwrap_or(WRAPPER))?;
            match o.get("log") {
                Some(p) => {
                    std::fs::write(p, &log).map_err(|e| format!("{p}: {e}"))?;
                    println!("wrote {p}");
                }
                None => print!("{log}"),
            }
            let failed = parse_lean_log(&log).checks.iter().any(|c| !c.ok);
            if failed {
                return Err("a Lean check failed (see the CHECK lines)".into());
            }
            Ok(())
        }
        Some("all") => {
            let o = Opts::parse(rest, &["build", "lean"])?;
            let manifest = vendor(&o)?;
            let revision = manifest_revision(&manifest)?;
            let channel = o
                .get("channel")
                .map_or_else(|| format!("Rev{}", &revision[..8]), str::to_string);
            let dir = scripts(&manifest, &channel, o.get("scripts-dir"))?;
            let lean_log = if o.flag("lean") {
                Some(lean(&manifest, o.get("wrapper").unwrap_or(WRAPPER))?)
            } else {
                None
            };
            let text = report(
                &manifest,
                o.get("base").unwrap_or(crate::MAIN_MANIFEST),
                Some(Path::new(o.need("checkout")?)),
                Some((&channel, &dir)),
                lean_log.as_deref(),
            )?;
            let default = format!("{}/report.md", out_dir(&o, &revision));
            emit_report(&text, Some(o.get("report").unwrap_or(&default)))
        }
        _ => Err(USAGE.into()),
    }
}

fn emit_report(text: &str, path: Option<&str>) -> Result<(), String> {
    match path {
        Some(p) => {
            std::fs::write(p, text).map_err(|e| format!("{p}: {e}"))?;
            println!("wrote {p}");
        }
        None => print!("{text}"),
    }
    Ok(())
}

fn out_dir(o: &Opts, revision: &str) -> String {
    o.get("out").map_or_else(
        || format!("specs/spectec/{}", &revision[..8]),
        str::to_string,
    )
}

fn manifest_revision(path: &str) -> Result<String, String> {
    json::parse(&crate::read(path)?)?
        .get("revision")
        .and_then(json::Json::as_str)
        .map(str::to_string)
        .ok_or(format!("{path}: no revision"))
}

fn git(dir: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .map_err(|e| format!("git: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "git -C {} {}: {}",
            dir.display(),
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// The non-hidden entries of a directory, sorted bytewise (the `LC_ALL=C` glob order).
fn sorted_entries(dir: &Path, want_dirs: bool) -> Result<Vec<String>, String> {
    let mut names = Vec::new();
    for e in std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let e = e.map_err(|e| e.to_string())?;
        let name = e.file_name().to_string_lossy().into_owned();
        if !name.starts_with('.') && e.path().is_dir() == want_dirs {
            names.push(name);
        }
    }
    names.sort();
    Ok(names)
}

fn obj(fields: Vec<(&str, json::Json)>) -> json::Json {
    json::Json::Obj(
        fields
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}

fn jstr(s: &str) -> json::Json {
    json::Json::Str(s.to_string())
}

/// The module name of a stream: `wasm-3.0` → `Wasm30`, `wasm-latest` → `WasmLatest`.
fn module_name(name: &str) -> String {
    let digits: String = name.chars().filter(char::is_ascii_digit).collect();
    if !digits.is_empty() {
        return format!("Wasm{digits}");
    }
    name.split('-')
        .map(|w| {
            let mut c = w.chars();
            c.next()
                .map(|f| f.to_ascii_uppercase().to_string() + c.as_str())
                .unwrap_or_default()
        })
        .collect()
}

/// `version vendor`: returns the path of the written manifest.
fn vendor(o: &Opts) -> Result<String, String> {
    let checkout = PathBuf::from(o.need("checkout")?);
    if let Some(rev) = o.get("revision")
        && git(&checkout, &["rev-parse", "HEAD"])? != git(&checkout, &["rev-parse", rev])?
    {
        git(&checkout, &["checkout", "-q", "--detach", rev])?;
    }
    let revision = git(&checkout, &["rev-parse", "HEAD"])?;
    if !git(&checkout, &["status", "--porcelain", "--", "specification"])?.is_empty() {
        return Err(format!(
            "{}/specification has local changes; the streams would not be those of {revision}",
            checkout.display()
        ));
    }
    let (frontend, frontend_rev, build) = match o.get("frontend") {
        Some(f) => {
            let f = PathBuf::from(f);
            let rev = match o.get("frontend-revision") {
                Some(r) => r.to_string(),
                None => git(f.parent().unwrap_or(Path::new(".")), &["rev-parse", "HEAD"])
                    .map_err(|e| format!("{e}\n(pass --frontend-revision)"))?,
            };
            (f, rev, FRONTEND_BUILD.to_string())
        }
        None => {
            let nixpkgs = o.get("nixpkgs").unwrap_or(NIXPKGS);
            let bin = checkout.join(FRONTEND_REL);
            if o.flag("build") {
                eprintln!(
                    "building the SpecTec frontend in {}/spectec",
                    checkout.display()
                );
                let st = Command::new("sh")
                    .args(["-c", BUILD_RECIPE])
                    .current_dir(checkout.join("spectec"))
                    .env("NIXPKGS", nixpkgs)
                    .status()
                    .map_err(|e| format!("sh: {e}"))?;
                if !st.success() {
                    return Err(format!("frontend build failed ({st})"));
                }
            } else if !bin.exists() {
                return Err(format!(
                    "{} missing: pass --build to build it, or --frontend BIN",
                    bin.display()
                ));
            }
            let build = if nixpkgs == NIXPKGS {
                FRONTEND_BUILD.to_string()
            } else {
                format!("dune build src/exe-spectec/main.exe (nixpkgs {nixpkgs})")
            };
            (bin, revision.clone(), build)
        }
    };
    let frontend =
        std::fs::canonicalize(&frontend).map_err(|e| format!("{}: {e}", frontend.display()))?;
    let out = out_dir(o, &revision);
    std::fs::create_dir_all(&out).map_err(|e| format!("{out}: {e}"))?;
    let out_abs = std::fs::canonicalize(&out).map_err(|e| format!("{out}: {e}"))?;

    let mut specs = Vec::new();
    let mut aliases = Vec::new();
    // (name, stream bytes) of the streams kept so far.
    let mut kept: Vec<(String, Vec<u8>)> = Vec::new();
    let spec_root = checkout.join("specification");
    for name in sorted_entries(&spec_root, true)? {
        if !name.starts_with("wasm-") {
            continue;
        }
        let files = sorted_entries(&spec_root.join(&name), false)?;
        let rel: Vec<String> = files
            .iter()
            .map(|f| format!("specification/{name}/{f}"))
            .collect();
        let target = out_abs.join(format!("{name}.ast"));
        let st = Command::new(&frontend)
            .args(&rel)
            .args(["--ast-width", &AST_WIDTH.to_string(), "--ast", "-o"])
            .arg(&target)
            .current_dir(&checkout)
            .env("LC_ALL", "C")
            .status()
            .map_err(|e| format!("{}: {e}", frontend.display()))?;
        if !st.success() {
            return Err(format!("spectec failed on specification/{name} ({st})"));
        }
        let bytes = std::fs::read(&target).map_err(|e| format!("{}: {e}", target.display()))?;
        let text = String::from_utf8(bytes.clone()).map_err(|e| e.to_string())?;
        let defs = sexp::parse_stream(&text).map_err(|e| format!("{name}: {e}"))?;
        let mut sources = Vec::new();
        for r in &rel {
            let b = std::fs::read(checkout.join(r)).map_err(|e| format!("{r}: {e}"))?;
            sources.push(obj(vec![
                ("path", jstr(r)),
                ("sha256", jstr(&sha256::hex(&b))),
            ]));
        }
        let mut fields = vec![
            ("definitions", json::Json::Num(defs.len().to_string())),
            ("name", jstr(&name)),
            ("sha256", jstr(&sha256::hex(&bytes))),
            ("sources", json::Json::Arr(sources)),
        ];
        if let Some((same, _)) = kept.iter().find(|(_, b)| *b == bytes) {
            std::fs::remove_file(&target).map_err(|e| e.to_string())?;
            fields.push(("sameAs", jstr(same)));
            aliases.push(obj(fields));
            continue;
        }
        fields.push(("path", jstr(&format!("{out}/{name}.ast"))));
        if crate::module_of(&name) != module_name(&name) {
            fields.push(("module", jstr(&module_name(&name))));
        }
        specs.push(obj(fields));
        kept.push((name, bytes));
    }
    if specs.is_empty() {
        return Err(format!(
            "no specification/wasm-* under {}",
            checkout.display()
        ));
    }
    let mut fields = vec![
        ("astWidth", json::Json::Num(AST_WIDTH.to_string())),
        ("command", jstr(COMMAND)),
        (
            "frontend",
            obj(vec![
                ("build", jstr(&build)),
                ("revision", jstr(&frontend_rev)),
            ]),
        ),
        ("revision", jstr(&revision)),
        ("specs", json::Json::Arr(specs)),
        ("upstream", jstr(UPSTREAM)),
    ];
    if !aliases.is_empty() {
        fields.push(("aliases", json::Json::Arr(aliases)));
    }
    let manifest = format!("{out}/manifest.json");
    std::fs::write(&manifest, json::pretty(&obj(fields)) + "\n")
        .map_err(|e| format!("{manifest}: {e}"))?;
    // The generator's own reader: SHA-256, definition count and byte-for-byte reprint.
    let loaded = crate::load_specs_from(&manifest)?;
    let readme = format!("{out}/README.md");
    if !Path::new(&readme).exists() {
        std::fs::write(
            &readme,
            readme_text(&revision, &frontend_rev, &build, &loaded),
        )
        .map_err(|e| format!("{readme}: {e}"))?;
    }
    Ok(manifest)
}

fn readme_text(revision: &str, frontend_rev: &str, build: &str, specs: &[crate::Spec]) -> String {
    let mut s = format!(
        "# `spectec --ast` streams of `WebAssembly/spec@{}`\n\n\
         Written by `spectec-gen version vendor` (tools/spectec-gen) from a checkout of\n\
         {UPSTREAM} at `{revision}`, with the SpecTec frontend of `{frontend_rev}`\n\
         ({build}), run as\n\n```\n{COMMAND}\n```\n\n\
         from the checkout root with the glob in `LC_ALL=C` order. `manifest.json` records the\n\
         revision, the SHA-256 and top-level definition count of every stream, the SHA-256 of\n\
         every source file (not vendored), and `aliases` for directories whose stream is byte for\n\
         byte another one's. The generator's reader reprints every stream byte for byte.\n\n\
         | stream | definitions | SHA-256 |\n| --- | --- | --- |\n",
        &revision[..10]
    );
    for sp in specs {
        s.push_str(&format!(
            "| `{}` | {} | `{}…` |\n",
            sp.path,
            sp.definitions,
            &sp.sha256[..8]
        ));
    }
    s.push_str(&format!(
        "\nThe frontend recipe is `make exe` without `opam install`, with nixpkgs\n`{NIXPKGS}`; \
         see `tools/spectec-gen/README.md`.\n"
    ));
    s
}

/// `version scripts`: the streams' `Original` scripts under `channel`, in `dir` (default a
/// scratch directory).  Returns the directory.
fn scripts(manifest: &str, channel: &str, dir: Option<&str>) -> Result<String, String> {
    if !channel
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_uppercase())
        || !channel.chars().all(|c| c.is_ascii_alphanumeric())
    {
        return Err(format!("channel {channel} is not a Lean module component"));
    }
    let specs = crate::load_specs_from(manifest)?;
    let dir = dir.map_or_else(
        || {
            std::env::temp_dir()
                .join(format!("spectec-version-{}", &specs[0].revision[..8]))
                .to_string_lossy()
                .into_owned()
        },
        str::to_string,
    );
    if Path::new(&dir)
        .canonicalize()
        .is_ok_and(|d| d.starts_with(std::env::current_dir().unwrap_or_default().join("Silmaril")))
    {
        return Err(format!(
            "{dir} is inside Silmaril/: promote a revision by changing MAIN_MANIFEST instead"
        ));
    }
    let mut out = BTreeMap::new();
    for sp in &specs {
        crate::emit_original(&mut out, sp, channel)?;
    }
    for (path, text) in &out {
        let rel = path
            .strip_prefix(crate::OUT_DIR)
            .ok_or(format!("unexpected output path {path}"))?;
        let target = format!("{dir}/Scripts{rel}");
        if let Some(p) = Path::new(&target).parent() {
            std::fs::create_dir_all(p).map_err(|e| format!("{}: {e}", p.display()))?;
        }
        std::fs::write(&target, text).map_err(|e| format!("{target}: {e}"))?;
    }
    Ok(dir)
}

/// The guarded Lake wrapper (checks the package link and toolchain, refuses `lake update`).
const WRAPPER: &str = "scripts/worktree-setup.sh lake";
/// The Lean module whose `run` the `lean` step evaluates.
const EVAL_MODULE: &str = "Silmaril.Wasm.SpecTec.VersionEval.Defs";

/// `version lean`: build `EVAL_MODULE` and run its `run` on the manifest's streams with
/// `lake env lean`, both through `wrapper` (split on spaces).  Returns the run's stdout (the
/// `CHECK`/`DEFECT` lines and the checkers' own messages).
fn lean(manifest: &str, wrapper: &str) -> Result<String, String> {
    let specs = crate::load_specs_from(manifest)?;
    let streams: Vec<String> = specs
        .iter()
        .map(|sp| format!("{}={}", sp.module, sp.path))
        .collect();
    let dir = std::env::temp_dir().join(format!(
        "spectec-version-lean-{}-{}",
        &specs[0].revision[..8],
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let file = dir.join("VersionCheck.lean");
    std::fs::write(
        &file,
        format!(
            "import {EVAL_MODULE}\n#eval show IO Unit from do\n  \
             Silmaril.Wasm.SpecTec.VersionEval.run ((← IO.getEnv \"SPECTEC_VERSION_STREAMS\").getD \"\")\n"
        ),
    )
    .map_err(|e| format!("{}: {e}", file.display()))?;
    let mut words = wrapper.split_whitespace();
    let prog = words.next().ok_or("empty --wrapper")?;
    let pre: Vec<&str> = words.collect();
    let run = |args: &[&str]| -> Result<String, String> {
        let out = Command::new(prog)
            .args(&pre)
            .args(args)
            .env("SPECTEC_VERSION_STREAMS", streams.join(";"))
            .output()
            .map_err(|e| format!("{prog}: {e}"))?;
        if !out.status.success() {
            return Err(format!(
                "{wrapper} {}: {}\n{}",
                args.join(" "),
                out.status,
                String::from_utf8_lossy(&out.stdout).trim_end().to_owned()
                    + "\n"
                    + String::from_utf8_lossy(&out.stderr).trim_end()
            ));
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    };
    eprintln!("building {EVAL_MODULE} with {wrapper}");
    run(&["build", EVAL_MODULE])?;
    eprintln!("running the Lean checks on {} streams", streams.len());
    let log = run(&["env", "lean", &file.to_string_lossy()])?;
    let _ = std::fs::remove_dir_all(&dir);
    Ok(log)
}

/// One `CHECK <stream> <check> ok|fail <message>` line.
struct LeanCheck {
    stream: String,
    check: String,
    ok: bool,
    message: String,
}

/// The parsed log of `version lean`.
#[derive(Default)]
struct LeanLog {
    checks: Vec<LeanCheck>,
    /// theorem name → `present`, `fixed` or `unknown …`.
    defects: BTreeMap<String, String>,
}

fn parse_lean_log(log: &str) -> LeanLog {
    let mut l = LeanLog::default();
    for line in log.lines() {
        if let Some(rest) = line.strip_prefix("CHECK ") {
            let mut w = rest.splitn(4, ' ');
            if let (Some(stream), Some(check), Some(status)) = (w.next(), w.next(), w.next()) {
                l.checks.push(LeanCheck {
                    stream: stream.into(),
                    check: check.into(),
                    ok: status == "ok",
                    message: w.next().unwrap_or("").into(),
                });
            }
        } else if let Some(rest) = line.strip_prefix("DEFECT ")
            && let Some((thm, verdict)) = rest.split_once(' ')
        {
            l.defects.insert(thm.into(), verdict.into());
        }
    }
    l
}

/// A declaration's key: `def utf8`, `rel Step`, …
fn decls(defs: &[sexp::SExp]) -> BTreeMap<String, &sexp::SExp> {
    fn walk<'a>(defs: &'a [sexp::SExp], m: &mut BTreeMap<String, &'a sexp::SExp>) {
        for d in defs {
            match d {
                sexp::SExp::Node(t, ks) if t == "rec" => walk(ks, m),
                d => {
                    if let Some((k, n)) = crate::emit::decl_kind(d) {
                        m.insert(format!("{k} {n}"), d);
                    }
                }
            }
        }
    }
    let mut m = BTreeMap::new();
    walk(defs, &mut m);
    m
}

/// The children of `d` tagged `tag` (`rule`, `clause`, `prod`).
fn parts<'a>(d: &'a sexp::SExp, tag: &str) -> Vec<&'a sexp::SExp> {
    match d {
        sexp::SExp::Node(_, ks) => ks
            .iter()
            .filter(|k| matches!(k, sexp::SExp::Node(t, _) if t == tag))
            .collect(),
        sexp::SExp::Atom(_) => Vec::new(),
    }
}

/// The name of a `rule` node (its first child, unquoted), or `""`.
fn rule_name(r: &sexp::SExp) -> String {
    match r {
        sexp::SExp::Node(_, ks) => match ks.first() {
            Some(sexp::SExp::Atom(a)) => a.trim_matches('"').to_string(),
            _ => String::new(),
        },
        sexp::SExp::Atom(_) => String::new(),
    }
}

/// One line describing how a changed declaration changed.
fn change_detail<'a>(key: &str, old: &'a sexp::SExp, new: &'a sexp::SExp) -> String {
    let (tag, what) = match key.split(' ').next() {
        Some("rel") => ("rule", "rules"),
        Some("def") => ("clause", "clauses"),
        Some("gram") => ("prod", "productions"),
        _ => return "signature or body".into(),
    };
    let (po, pn) = (parts(old, tag), parts(new, tag));
    let mut s = format!("{what} {} → {}", po.len(), pn.len());
    if tag == "rule" {
        let keyed = |ps: &[&'a sexp::SExp]| -> BTreeMap<String, &'a sexp::SExp> {
            let mut seen: BTreeMap<String, usize> = BTreeMap::new();
            ps.iter()
                .map(|r| {
                    let n = match rule_name(r) {
                        n if n.is_empty() => "(unnamed)".to_string(),
                        n => n,
                    };
                    let k = seen.entry(n.clone()).or_default();
                    *k += 1;
                    let key = if *k == 1 { n } else { format!("{n}#{k}") };
                    (key, *r)
                })
                .collect()
        };
        let (ko, kn) = (keyed(&po), keyed(&pn));
        let changed: Vec<String> = kn
            .iter()
            .filter(|(k, r)| ko.get(*k).is_some_and(|o| o != *r))
            .map(|(k, _)| k.clone())
            .collect();
        let added: Vec<String> = kn
            .keys()
            .filter(|k| !ko.contains_key(*k))
            .cloned()
            .collect();
        let removed: Vec<String> = ko
            .keys()
            .filter(|k| !kn.contains_key(*k))
            .cloned()
            .collect();
        for (label, xs) in [("changed", changed), ("added", added), ("removed", removed)] {
            if !xs.is_empty() {
                s.push_str(&format!("; {label}: {}", md_list(&xs)));
            }
        }
    } else if po.len() == pn.len() {
        let at: Vec<String> = (0..po.len())
            .filter(|&i| po[i] != pn[i])
            .map(|i| format!("#{i}"))
            .collect();
        if at.is_empty() {
            s.push_str("; same parts, signature changed");
        } else {
            s.push_str(&format!("; changed: {}", at.join(", ")));
        }
    }
    s
}

/// A known defect: its Lean status on the base revision and the declarations (or `rel`
/// rules, by index) its Lean statement reads.
struct Known {
    id: &'static str,
    module: &'static str,
    /// `def x`, `gram x`, or `rel R #i` (the `i`-th rule of `R`).
    decls: &'static [&'static str],
    /// `true` when the defect is present on the base revision.
    present: bool,
    theorem: &'static str,
}

/// The revision whose defect statuses `KNOWN` records.
const KNOWN_REVISION: &str = "e7a9df7cdd351df9d8d8546a53248669d51c1aa8";

/// The defects of `docs/projects/spectec-divergences.md`, as proved at `KNOWN_REVISION`.
const KNOWN: &[Known] = &[
    Known {
        id: "#654 `Bi32`/`Bi64` unsigned",
        module: "Wasm30",
        decls: &["gram Bi32", "gram Bi64"],
        present: false,
        theorem: "not_bi32Unsigned_main",
    },
    Known {
        id: "#655 `$cont(0x80)` undefined",
        module: "Wasm30",
        decls: &["def cont"],
        present: false,
        theorem: "not_contUndefAt80_main",
    },
    Known {
        id: "#656 four-byte UTF-8 rejects U+1F601",
        module: "Wasm30",
        decls: &["def utf8single"],
        present: false,
        theorem: "utf8singleAcceptsGrin_main",
    },
    Known {
        id: "#661 `\\u{E000}` guard",
        module: "Wasm30",
        decls: &["gram Tstringchar"],
        present: false,
        theorem: "not_escapeRejectsE000_main",
    },
    Known {
        id: "#803 `BsN(32)` loses `FF 7E`",
        module: "Wasm30",
        decls: &["gram BsN", "gram BiN"],
        present: true,
        theorem: "bsnLosesFF7E_main",
    },
    Known {
        id: "U5 `$sx` undefined at references",
        module: "Wasm30",
        decls: &["def sx"],
        present: false,
        theorem: "not_sxUndefAtRef_main",
    },
    Known {
        id: "`$s33_to_u32` has no clauses",
        module: "Wasm30",
        decls: &["def s33_to_u32"],
        present: true,
        theorem: "s33ToU32Undefined_main",
    },
    Known {
        id: "`$ieee_` has no clauses",
        module: "Wasm30",
        decls: &["def ieee_"],
        present: true,
        theorem: "ieeeUndefined_main",
    },
    Known {
        id: "dead `Step` rules (8)",
        module: "Wasm30",
        decls: &[
            "rel Step #15",
            "rel Step #19",
            "rel Step #21",
            "rel Step #23",
            "rel Step #25",
            "rel Step #26",
            "rel Step #31",
            "rel Step #35",
        ],
        present: true,
        theorem: "ruleDead_*_main",
    },
    Known {
        id: "dead `Step_read` rules (10)",
        module: "Wasm30",
        decls: &[
            "rel Step_read #0",
            "rel Step_read #1",
            "rel Step_read #22",
            "rel Step_read #27",
            "rel Step_read #41",
            "rel Step_read #45",
            "rel Step_read #47",
            "rel Step_read #49",
            "rel Step_read #51",
            "rel Step_read #52",
        ],
        present: true,
        theorem: "ruleDead_*_main",
    },
    Known {
        id: "wasm-1.0 #684 four-byte bound",
        module: "Wasm10",
        decls: &["def utf8"],
        present: false,
        theorem: "not_utf8RejectsGrin10_main",
    },
    Known {
        id: "wasm-1.0 #685 `C2 C0` accepted",
        module: "Wasm10",
        decls: &["def utf8"],
        present: true,
        theorem: "utf8AcceptsC2C0_main",
    },
    Known {
        id: "wasm-2.0 twin of #684",
        module: "Wasm20",
        decls: &["def utf8"],
        present: false,
        theorem: "utf8AcceptsGrin20_main",
    },
    Known {
        id: "wasm-2.0 twin of #685",
        module: "Wasm20",
        decls: &["def utf8"],
        present: true,
        theorem: "utf8AcceptsC2C0_20_main",
    },
    Known {
        id: "wasm-2.0 #673 `$dataidx_instrs`",
        module: "Wasm20",
        decls: &["def dataidx_instrs"],
        present: true,
        theorem: "dataidxMissesNested_main",
    },
];

/// The declaration (or rule) a `Known::decls` entry names.
fn lookup<'a>(ds: &BTreeMap<String, &'a sexp::SExp>, key: &str) -> Option<&'a sexp::SExp> {
    match key.split_once(" #") {
        Some((rel, i)) => {
            let i: usize = i.parse().ok()?;
            parts(ds.get(rel)?, "rule").get(i).copied()
        }
        None => ds.get(key).copied(),
    }
}

/// Functions declared with no clauses.
fn clauseless(ds: &BTreeMap<String, &sexp::SExp>) -> Vec<String> {
    ds.iter()
        .filter(|(k, d)| k.starts_with("def ") && parts(d, "clause").is_empty())
        .map(|(k, _)| k["def ".len()..].to_string())
        .collect()
}

/// Grammars with no productions.
fn empty_grammars(ds: &BTreeMap<String, &sexp::SExp>) -> Vec<String> {
    ds.iter()
        .filter(|(k, d)| k.starts_with("gram ") && parts(d, "prod").is_empty())
        .map(|(k, _)| k["gram ".len()..].to_string())
        .collect()
}

/// Whether a source line declares `def $name` with `hint(builtin)`.
fn has_builtin_hint(sources: &[String], name: &str) -> bool {
    let decl = format!("def ${name}");
    sources.iter().any(|text| {
        text.lines().any(|l| {
            l.trim_start().strip_prefix(&decl).is_some_and(|rest| {
                !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_' || c == '\'')
                    && l.contains("hint(builtin)")
            })
        })
    })
}

fn md_list(xs: &[String]) -> String {
    if xs.is_empty() {
        "none".into()
    } else {
        xs.iter()
            .map(|x| format!("`{x}`"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// `version report`: Markdown text.  `checkout` (the new revision's sources) enables the
/// builtin-hint lint; `scripts` names the channel and directory of generated scripts.
fn report(
    manifest: &str,
    base: &str,
    checkout: Option<&Path>,
    scripts: Option<(&str, &str)>,
    lean_log: Option<&str>,
) -> Result<String, String> {
    let new = crate::load_specs_from(manifest)?;
    let old = crate::load_specs_from(base)?;
    let pinned = crate::load_specs()?;
    let (nrev, orev) = (&new[0].revision, &old[0].revision);
    let mut s = format!(
        "# SpecTec version report: `WebAssembly/spec@{}`\n\n\
         Generated by {} `version report` from `{manifest}` against the base `{base}`\n\
         (`{}`) and the pinned errata of `{}`. Unverified tooling: statements marked\n\
         *carries over* rely on a Lean theorem about the base and on the listed declarations being\n\
         identical; everything else needs a Lean check.\n\n\
         ## Streams\n\n| stream | base definitions | new definitions | new SHA-256 |\n\
         | --- | --- | --- | --- |\n",
        &nrev[..10],
        crate::GENERATOR,
        &orev[..10],
        crate::MANIFEST
    );
    for sp in &new {
        let od = old
            .iter()
            .find(|o| o.module == sp.module)
            .map_or("—".to_string(), |o| o.definitions.to_string());
        s.push_str(&format!(
            "| `{}` ({}) | {od} | {} | `{}…` |\n",
            sp.name,
            sp.module,
            sp.definitions,
            &sp.sha256[..8]
        ));
    }
    for o in old
        .iter()
        .filter(|o| !new.iter().any(|n| n.module == o.module))
    {
        s.push_str(&format!(
            "| `{}` ({}) | {} | gone | |\n",
            o.name, o.module, o.definitions
        ));
    }

    s.push_str("\n## What changed\n\n");
    for sp in &new {
        let Some(o) = old.iter().find(|o| o.module == sp.module) else {
            s.push_str(&format!("### {}\n\nNew stream (no base).\n\n", sp.name));
            continue;
        };
        let (dn, dold) = (decls(&sp.defs), decls(&o.defs));
        let added: Vec<String> = dn
            .keys()
            .filter(|k| !dold.contains_key(*k))
            .cloned()
            .collect();
        let removed: Vec<String> = dold
            .keys()
            .filter(|k| !dn.contains_key(*k))
            .cloned()
            .collect();
        let changed: Vec<&String> = dn
            .iter()
            .filter(|(k, d)| dold.get(*k).is_some_and(|od| od != *d))
            .map(|(k, _)| k)
            .collect();
        s.push_str(&format!(
            "### {}\n\n{} declarations changed, {} added, {} removed.\n\n",
            sp.name,
            changed.len(),
            added.len(),
            removed.len()
        ));
        if !added.is_empty() {
            s.push_str(&format!("* added: {}\n", md_list(&added)));
        }
        if !removed.is_empty() {
            s.push_str(&format!("* removed: {}\n", md_list(&removed)));
        }
        for k in &changed {
            let detail = change_detail(k, dold[*k], dn[*k]);
            s.push_str(&format!("* changed `{k}`: {detail}\n"));
        }
        s.push('\n');
    }

    s.push_str(&format!(
        "## Errata\n\nEach `spectec_erratum` command of `{}/` (written against the pinned \
         streams), classified on the new streams.\n\n| issue | file | target | status |\n\
         | --- | --- | --- | --- |\n",
        crate::ERRATA_DIR
    ));
    let rows = crate::errata_status(&pinned, &new)?;
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for r in &rows {
        *counts.entry(r.status.tag()).or_default() += 1;
        s.push_str(&format!(
            "| #{} | `{}` | `{}` | {} — {} |\n",
            r.issue,
            r.file,
            r.target,
            r.status.tag(),
            r.status.describe()
        ));
    }
    let summary: Vec<String> = counts.iter().map(|(k, n)| format!("{n} {k}")).collect();
    s.push_str(&format!("\nSummary: {}.\n", summary.join(", ")));

    let lean = lean_log.map(parse_lean_log);
    let evaluated = lean.as_ref().is_some_and(|l| !l.defects.is_empty());
    s.push_str(&format!(
        "\n## Known defects\n\nThe defects proved present or fixed at `{}` \
         (`docs/projects/spectec-divergences.md`, theorems in `Silmaril.Wasm.SpecTec.Versions`). Against \
         that base, when every listed declaration is identical on the new revision the base \
         status *carries over* (for these declarations; a change elsewhere that they call is not \
         seen); otherwise the Lean predicate must be re-proved.",
        &KNOWN_REVISION[..10]
    ));
    if evaluated {
        s.push_str(
            " The last column is the Lean predicate *evaluated* on the new streams by \
             `version lean` (`Silmaril.Wasm.SpecTec.VersionEval`: the `callDef`/`premsHold`/\
             `findDef?` evaluation the kernel proof uses, run by `#eval` at fuel 100, not \
             proved); `unknown` when the predicate is not decided by one evaluation \
             (grammar and rule predicates).",
        );
    }
    s.push_str("\n\n| defect | base status (theorem) | declarations | new revision |");
    s.push_str(if evaluated {
        " Lean evaluation |\n| --- | --- | --- | --- | --- |\n"
    } else {
        "\n| --- | --- | --- | --- |\n"
    });
    let at_known = orev == KNOWN_REVISION;
    for k in KNOWN.iter().filter(|_| at_known || evaluated) {
        let Some(n) = new.iter().find(|x| x.module == k.module) else {
            continue;
        };
        let dn = decls(&n.defs);
        let base = if k.present { "present" } else { "fixed" };
        let verdict = match old.iter().find(|x| x.module == k.module) {
            Some(o) if at_known => {
                let dold = decls(&o.defs);
                let differ: Vec<String> = k
                    .decls
                    .iter()
                    .filter(|d| lookup(&dold, d) != lookup(&dn, d) || lookup(&dn, d).is_none())
                    .map(|d| d.to_string())
                    .collect();
                if differ.is_empty() {
                    format!("identical: **{base}** (carries over)")
                } else {
                    format!("changed ({}): **re-check in Lean**", md_list(&differ))
                }
            }
            _ => "— (base is not the revision the statuses were proved at)".into(),
        };
        s.push_str(&format!(
            "| {} ({}) | {base} (`{}`) | {} | {verdict} |",
            k.id,
            k.module,
            k.theorem,
            md_list(&k.decls.iter().map(|d| d.to_string()).collect::<Vec<_>>())
        ));
        if let Some(l) = lean.as_ref().filter(|_| evaluated) {
            let e = l
                .defects
                .get(k.theorem)
                .map_or("not evaluated".to_string(), |v| {
                    if v == base {
                        format!("**{v}** (as proved at `e7a9df7c`)")
                    } else if v == "present" || v == "fixed" {
                        format!("**{v}** (differs from `e7a9df7c`)")
                    } else {
                        v.clone()
                    }
                });
            s.push_str(&format!(" {e} |"));
        }
        s.push('\n');
    }

    if !at_known && !evaluated {
        s.push_str(&format!(
            "| (statuses are recorded for `{}` only; rerun with that base, or run `version lean`) | | | |\n",
            &KNOWN_REVISION[..10]
        ));
    }

    s.push_str("\n## Lints\n\n");
    for sp in &new {
        let dn = decls(&sp.defs);
        let base_cl = old
            .iter()
            .find(|o| o.module == sp.module)
            .map(|o| clauseless(&decls(&o.defs)))
            .unwrap_or_default();
        let cl = clauseless(&dn);
        let fresh: Vec<String> = cl
            .iter()
            .filter(|c| !base_cl.contains(c))
            .cloned()
            .collect();
        s.push_str(&format!(
            "* `{}`: {} functions without clauses ({} new since the base: {}).",
            sp.name,
            cl.len(),
            fresh.len(),
            md_list(&fresh)
        ));
        if let Some(c) = checkout {
            let dir = c.join("specification").join(&sp.name);
            let mut sources = Vec::new();
            for f in sorted_entries(&dir, false)? {
                sources.push(crate::read(&dir.join(f).to_string_lossy())?);
            }
            let undefined: Vec<String> = cl
                .iter()
                .filter(|n| !has_builtin_hint(&sources, n))
                .cloned()
                .collect();
            s.push_str(&format!(
                " Without `hint(builtin)` on any `def ${{name}}` line of the sources (so \
                 undefined everywhere, like `$s33_to_u32`): {}.",
                md_list(&undefined)
            ));
        }
        let eg = empty_grammars(&dn);
        s.push_str(&format!(
            " Grammars without productions: {}.\n",
            md_list(&eg)
        ));
    }

    s.push_str("\n## Lean\n\n");
    if let Some((channel, dir)) = scripts {
        s.push_str(&format!(
            "The `Original` scripts were written under channel `{channel}` to `{dir}/Scripts/` \
             (namespace `{}.{channel}.*`), outside the tree.\n",
            crate::NAMESPACE_ROOT
        ));
    }
    match (lean_log, lean.as_ref()) {
        (Some(_), Some(l)) if !l.checks.is_empty() => {
            s.push_str(
                "\nLean checks (`version lean`, compiled code run through the guarded Lake \
                 wrapper, as `Silmaril.Proofs.Wasm.SpecTec.Versions.Checks` runs them at build \
                 time):\n\n| stream | check | result |\n| --- | --- | --- |\n",
            );
            for c in &l.checks {
                s.push_str(&format!(
                    "| {} | `{}` | {} {} |\n",
                    c.stream,
                    c.check,
                    if c.ok { "ok" } else { "**fail**" },
                    c.message.replace('|', "\\|")
                ));
            }
        }
        (Some(log), _) => s.push_str(&format!(
            "\nLean checks (`--lean-log`):\n\n```\n{}\n```\n",
            log.trim_end()
        )),
        (None, _) => s.push_str(
            "\nNot run here (`version lean`, or `version all --lean`, runs the Lean checks and \
             evaluates the defect predicates). To make this revision the `Main` channel: point `MAIN_MANIFEST` \
             (tools/spectec-gen/src/main.rs) at the new manifest, run `generate`, build \
             `Silmaril.Proofs.Wasm.SpecTec.Versions.Checks` (reader, reprint, well-formedness, \
             instruction shapes) and re-prove every row above marked *re-check*.\n",
        ),
    }
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at_root() {
        std::env::set_current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../..")).unwrap();
    }

    #[test]
    fn module_names() {
        assert_eq!(module_name("wasm-3.0"), "Wasm30");
        assert_eq!(module_name("wasm-latest"), "WasmLatest");
        assert_eq!(crate::module_of("wasm-3.0"), module_name("wasm-3.0"));
    }

    #[test]
    fn builtin_hints() {
        let src = vec![
            "def $ibits_  hint(builtin)\ndef $s33_to_u32(s33) : u32  hint(show %)\n".to_string(),
        ];
        assert!(has_builtin_hint(&src, "ibits_"));
        assert!(!has_builtin_hint(&src, "s33_to_u32"));
        assert!(!has_builtin_hint(&src, "ibits"));
    }

    /// The pinned streams against main: the report reproduces the documented status.
    #[test]
    fn report_pin_to_main() {
        at_root();
        let r = report(crate::MAIN_MANIFEST, crate::MANIFEST, None, None, None).unwrap();
        // #654's target equals the erratum's correction on main.
        assert!(r.contains("| #654 | `Binary51.lean` | `Bi32` | fixedAsErratum"));
        // `$utf8single` is new; seven `Step` rules were rewritten.
        assert!(r.contains(
            "* added: `def R_idot_add`, `def f`, `def ivrelaxed_dot_`, `def s`, `def utf8single`"
        ));
        assert!(r.contains("`call_ref-func`"));
        // Known-defect statuses are only stated against the revision they were proved at.
        assert!(r.contains("statuses are recorded for `e7a9df7cdd` only"));
        assert!(!r.contains("carries over)"));
        assert!(r.contains("* changed `rel Step`: rules"));
        assert!(r.contains("Grammars without productions"));
    }

    /// Main against itself: nothing changed and every known status carries over.
    #[test]
    fn report_main_to_main() {
        at_root();
        let r = report(crate::MAIN_MANIFEST, crate::MAIN_MANIFEST, None, None, None).unwrap();
        assert!(r.contains("0 declarations changed, 0 added, 0 removed"));
        assert!(!r.contains("re-check in Lean"));
        assert_eq!(r.matches("(carries over)").count(), KNOWN.len());
    }

    /// The pinned streams *as if* they were a new revision after main: the declarations of
    /// defects fixed on main changed, so those rows ask for a Lean re-check.
    #[test]
    fn report_main_to_pin_rechecks() {
        at_root();
        let r = report(crate::MANIFEST, crate::MAIN_MANIFEST, None, None, None).unwrap();
        assert!(r.contains("| #655 `$cont(0x80)` undefined (Wasm30) | fixed (`not_contUndefAt80_main`) | `def cont` | changed (`def cont`): **re-check in Lean** |"));
        assert!(r.contains("| `$s33_to_u32` has no clauses (Wasm30) | present (`s33ToU32Undefined_main`) | `def s33_to_u32` | identical: **present** (carries over) |"));
    }

    const LOG: &str = "noise from checkStreamFile\n\
        CHECK Wasm30 checkStreamFile ok specs/x.ast\n\
        CHECK Wasm30 crosscheck fail disagrees at NOP\n\
        DEFECT not_contUndefAt80_main present\n\
        DEFECT s33ToU32Undefined_main fixed\n\
        DEFECT bsnLosesFF7E_main unknown grammar predicate (gramRelSup)\n";

    #[test]
    fn lean_log_parsing() {
        let l = parse_lean_log(LOG);
        assert_eq!(l.checks.len(), 2);
        assert!(l.checks[0].ok && !l.checks[1].ok);
        assert_eq!(l.checks[1].message, "disagrees at NOP");
        assert_eq!(l.defects["not_contUndefAt80_main"], "present");
        assert_eq!(
            l.defects["bsnLosesFF7E_main"],
            "unknown grammar predicate (gramRelSup)"
        );
    }

    /// With a Lean log the report has an evaluation column, also against a base the statuses
    /// were not proved at, and a table of the Lean checks.
    #[test]
    fn report_with_lean_log() {
        at_root();
        let r = report(crate::MANIFEST, crate::MAIN_MANIFEST, None, None, Some(LOG)).unwrap();
        assert!(r.contains("| #655 `$cont(0x80)` undefined (Wasm30) | fixed (`not_contUndefAt80_main`) | `def cont` | changed (`def cont`): **re-check in Lean** | **present** (differs from `e7a9df7c`) |"));
        assert!(r.contains("(`s33ToU32Undefined_main`) | `def s33_to_u32` | identical: **present** (carries over) | **fixed** (differs from `e7a9df7c`) |"));
        assert!(
            r.contains("| `def ieee_` | identical: **present** (carries over) | not evaluated |")
        );
        assert!(r.contains("| Wasm30 | `crosscheck` | **fail** disagrees at NOP |"));
        let p = report(crate::MAIN_MANIFEST, crate::MANIFEST, None, None, Some(LOG)).unwrap();
        assert!(p.contains("— (base is not the revision the statuses were proved at) | **present** (differs from `e7a9df7c`) |"));
        assert!(!p.contains("statuses are recorded for"));
    }

    /// `version lean` through a stand-in wrapper: it is asked to build the evaluation module,
    /// then to run `lake env lean` on a file importing it, with the streams in the environment.
    #[test]
    fn lean_step_with_stub_wrapper() {
        at_root();
        let tmp = std::env::temp_dir().join(format!("spectec-lean-test-{}", std::process::id()));
        std::fs::create_dir_all(&tmp).unwrap();
        let stub = tmp.join("wrapper");
        let calls = tmp.join("calls");
        std::fs::write(
            &stub,
            format!(
                "#!/bin/sh\necho \"$*\" >>{0}\nif [ \"$1\" = env ]; then head -1 \"$3\" >>{0}; \
                 echo \"$SPECTEC_VERSION_STREAMS\" >>{0}; echo 'DEFECT ieeeUndefined_main present'; fi\n",
                calls.display()
            ),
        )
        .unwrap();
        Command::new("chmod").arg("+x").arg(&stub).status().unwrap();
        let log = lean(crate::MAIN_MANIFEST, stub.to_str().unwrap()).unwrap();
        assert_eq!(log, "DEFECT ieeeUndefined_main present\n");
        let c = std::fs::read_to_string(&calls).unwrap();
        let lines: Vec<&str> = c.lines().collect();
        assert_eq!(lines[0], format!("build {EVAL_MODULE}"));
        assert!(lines[1].starts_with("env lean ") && lines[1].ends_with("VersionCheck.lean"));
        assert_eq!(lines[2], format!("import {EVAL_MODULE}"));
        assert!(lines[3].starts_with("Wasm10=specs/spectec/e7a9df7c/wasm-1.0.ast;"));
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    /// `vendor` with a stand-in frontend that prints the main streams: the manifest it writes
    /// is the vendored one (up to paths), `wasm-latest` becomes an alias, and a dirty
    /// `specification/` is refused.
    #[test]
    fn vendor_with_stub_frontend() {
        at_root();
        let root = std::env::current_dir().unwrap();
        let tmp = std::env::temp_dir().join(format!("spectec-vendor-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        let co = tmp.join("spec");
        for d in ["wasm-1.0", "wasm-3.0", "wasm-latest"] {
            std::fs::create_dir_all(co.join("specification").join(d)).unwrap();
            std::fs::write(co.join("specification").join(d).join("a.spectec"), d).unwrap();
        }
        // The stub: `-o OUT` gets the main stream of the directory's version (latest = 3.0).
        let stub = tmp.join("spectec");
        let streams = root.join("specs/spectec/e7a9df7c");
        std::fs::write(
            &stub,
            format!(
                "#!/bin/sh\ncase \"$1\" in *wasm-1.0*) v=1.0;; *) v=3.0;; esac\n\
                 while [ \"$1\" != -o ]; do shift; done\ncp {}/wasm-$v.ast \"$2\"\n",
                streams.display()
            ),
        )
        .unwrap();
        Command::new("chmod").arg("+x").arg(&stub).status().unwrap();
        let g = |args: &[&str]| {
            let st = Command::new("git")
                .arg("-C")
                .arg(&co)
                .args(["-c", "user.name=t", "-c", "user.email=t@t"])
                .args(args)
                .status()
                .unwrap();
            assert!(st.success());
        };
        g(&["init", "-q"]);
        g(&["add", "."]);
        g(&["commit", "-qm", "x"]);
        let out = tmp.join("out");
        let args: Vec<String> = [
            "--checkout",
            co.to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
            "--frontend",
            stub.to_str().unwrap(),
            "--frontend-revision",
            "f00",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let o = Opts::parse(&args, &["build"]).unwrap();
        let m = vendor(&o).unwrap();
        let j = json::parse(&std::fs::read_to_string(&m).unwrap()).unwrap();
        let specs = j.get("specs").unwrap().as_arr().unwrap();
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[1].get("definitions").unwrap().as_usize(), Some(974));
        let alias = &j.get("aliases").unwrap().as_arr().unwrap()[0];
        assert_eq!(alias.get("sameAs").unwrap().as_str(), Some("wasm-3.0"));
        assert_eq!(alias.get("name").unwrap().as_str(), Some("wasm-latest"));
        assert!(!out.join("wasm-latest.ast").exists());
        assert!(out.join("README.md").exists());
        // The written scripts are those of the main channel, renamed.
        let dir = scripts(&m, "RevTest", Some(tmp.join("gen").to_str().unwrap())).unwrap();
        let orig =
            std::fs::read_to_string(format!("{dir}/Scripts/RevTest/Wasm10/Original.lean")).unwrap();
        assert!(orig.contains("namespace Silmaril.Wasm.SpecTec.Scripts.RevTest.Wasm10.Original"));
        // A local change under specification/ is refused.
        std::fs::write(co.join("specification/wasm-1.0/a.spectec"), "edited").unwrap();
        assert!(vendor(&o).unwrap_err().contains("local changes"));
        std::fs::remove_dir_all(&tmp).unwrap();
    }
}
