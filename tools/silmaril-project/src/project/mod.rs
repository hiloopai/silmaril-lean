//! `sil project`: silmaril projects (the guide is `docs/projects/silmaril-projects.md`).
//!
//! A project is a Lake package with an optional `silmaril.toml` (which must carry the project
//! sid). `init` writes that manifest with a random sid; `artifacts add` and `lock` maintain the
//! artifact registry `silmaril/artifacts.toml` (the single source of truth for blobs); `dump`
//! elaborates a small driver that runs `#silmaril_dump` (the only subcommand that runs Lean);
//! `check` reads the manifest, the registries, `lake-manifest.json` and the dump, hashes files
//! and applies the rules of [`check`]; `sqlite` writes the canonical SQL text and builds the
//! database from it; `explore` writes a static HTML page over that database ([`explore`]);
//! `findings`, `errors`, `gaps` and `deprecated` query its markings ([`query`]).
//! Works in any Lake project.
//!
//! Formats are defined once, in [`schema`].

mod check;
mod edges;
mod explore;
mod hash;
mod query;
pub mod schema;
mod sid;
mod sources;
mod sql;
mod trust;

use clap::{Args as ClapArgs, Subcommand};
use miette::{IntoDiagnostic, Result, WrapErr, bail, miette};
use schema::{
    ARTIFACTS_PATH, ARTIFACTS_SCHEMA, ARTIFACTS_SCHEMAS, ArtifactEntry, Artifacts, Derivation,
    Dump, FileRef, MANIFEST_SCHEMA, Manifest, ProjectRow, records,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command as Proc,
};

#[derive(Subcommand)]
pub enum Command {
    /// Start a project: write `silmaril.toml` (a fresh project sid), an empty artifact registry
    /// and a commented records file
    Init {
        #[command(flatten)]
        dir: DirArg,
    },
    /// Edit the artifact registry `silmaril/artifacts.toml` (the files Lean may read)
    #[command(subcommand)]
    Artifacts(ArtifactsCommand),
    /// Hash every registry path and write `cid`, `size`, `sha256` and `git_sha1`
    Lock {
        #[command(flatten)]
        dir: DirArg,
    },
    /// Check the records files (`silmaril.records.v0.2`) and the artifact registry, without Lean
    Lint {
        #[command(flatten)]
        dir: DirArg,
        /// Records files, relative to the project directory (default: every records file
        /// under `silmaril/`)
        paths: Vec<PathBuf>,
    },
    /// Elaborate the project's modules and write the Lean dump (`#silmaril_dump`)
    Dump {
        #[command(flatten)]
        dir: DirArg,
        /// Output, relative to the project directory (generated: not committed)
        #[arg(long, default_value = ".lake/silmaril/dump.json")]
        out: PathBuf,
        /// The Lake command (default: `$SIL_LAKE`, else `lake`); split on whitespace
        #[arg(long)]
        lake: Option<String>,
        /// Skip `lake build --wfail <modules>` before elaborating the driver
        #[arg(long)]
        no_build: bool,
    },
    /// Elaborate the trust driver over the core trust API and write the trust lines
    /// (`silmaril.trust.v1` and `silmaril.trust-adapter.v0.1` lines) that `check` and `sqlite` read with `--trust`
    TrustDump {
        #[command(flatten)]
        dir: DirArg,
        /// Modules to import (their imports are described too); default: the project's modules
        #[arg(long = "module")]
        modules: Vec<String>,
        /// Module prefixes to describe and audit (default: `Silmaril`)
        #[arg(long = "root")]
        roots: Vec<String>,
        /// Output, relative to the project directory (generated: not committed)
        #[arg(long, default_value = ".lake/silmaril/trust.jsonl")]
        out: PathBuf,
        /// The Lake command (default: `$SIL_LAKE`, else `lake`); split on whitespace
        #[arg(long)]
        lake: Option<String>,
        /// Skip `lake build --wfail <modules>` before elaborating the driver
        #[arg(long)]
        no_build: bool,
        /// `MODULE=REASON`: a module whose theorems are not audited (coverage becomes partial)
        #[arg(long)]
        exclude: Vec<String>,
    },
    /// Check the manifest, the registries, the dump and the files; print statuses and groups
    Check {
        #[command(flatten)]
        dir: DirArg,
        /// The dump (`sil project dump`), relative to the project directory
        #[arg(long, default_value = ".lake/silmaril/dump.json")]
        dump: PathBuf,
        /// The trust lines from `trust-dump` (or, optionally, a `silmaril.trust-core.v1` export), relative to the project directory;
        /// without it, decision-procedure and axiom use is reported as unaudited
        #[arg(long)]
        trust: Option<PathBuf>,
        /// Fail on trust violations, on a missing trust dump, on covered modules whose digests
        /// are not consistent or that import undescribed modules, and on uncollected axioms
        #[arg(long)]
        strict_trust: bool,
    },
    /// Check, then write the canonical SQL text and build the SQLite database from it
    Sqlite {
        #[command(flatten)]
        dir: DirArg,
        /// The dump (`sil project dump`), relative to the project directory
        #[arg(long, default_value = ".lake/silmaril/dump.json")]
        dump: PathBuf,
        /// The trust lines from `trust-dump` (or, optionally, a `silmaril.trust-core.v1` export), relative to the project directory;
        /// without it, the trust tables are empty and `meta` says `trust.status = absent`
        #[arg(long)]
        trust: Option<PathBuf>,
        /// Fail on trust violations and incomplete trust evidence (see `check --strict-trust`)
        #[arg(long)]
        strict_trust: bool,
        /// The canonical SQL text
        #[arg(long, default_value = ".lake/silmaril/project.sql")]
        sql: PathBuf,
        /// The database, built from the SQL text
        #[arg(long, default_value = ".lake/silmaril/project.sqlite")]
        db: PathBuf,
        /// Tune the file for lazy reads over HTTP (`sil project explore`): set the page size and
        /// `journal_mode = DELETE` (the content and indexes are the canonical ones)
        #[arg(long)]
        httpvfs: bool,
        /// The SQLite page size with `--httpvfs` (one HTTP Range request reads at least a page)
        #[arg(long, default_value_t = 4096, requires = "httpvfs", value_parser = page_size)]
        page_size: u32,
    },
    /// Write a static HTML page that opens the database in the browser (no data embedded)
    Explore {
        #[command(flatten)]
        dir: DirArg,
        /// The database the page opens by default over http(s), relative to the project
        #[arg(long, default_value = ".lake/silmaril/project.sqlite")]
        db: PathBuf,
        /// The page
        #[arg(long, default_value = ".lake/silmaril/explore.html")]
        out: PathBuf,
    },
    /// List the findings (classified refutations) of the database `sqlite` wrote
    Findings {
        #[command(flatten)]
        db: DbArg,
        /// Only this classification; `unclassified` lists the failing problems that are
        /// neither deprecated nor classified
        #[arg(long = "class", value_parser = ["error", "spec_bug", "model_gap", "unclear", "unclassified"])]
        class: Option<String>,
    },
    /// List the genuine errors: `error` findings, with versions, fix and disclosure
    Errors {
        #[command(flatten)]
        db: DbArg,
    },
    /// List the model gaps, one line per missing instruction or feature, most problems first
    Gaps {
        #[command(flatten)]
        db: DbArg,
    },
    /// List the deprecated problems, groups and specs with their replacements
    Deprecated {
        #[command(flatten)]
        db: DbArg,
        /// List every deprecated problem instead, with why (its own deprecation, its spec's,
        /// or its general problem's)
        #[arg(long)]
        problems: bool,
    },
    /// Print the records-file schema as JSON Schema
    Schema {
        /// Write it to this file instead of stdout
        #[arg(long)]
        out: Option<PathBuf>,
    },
}

/// `--page-size`: checked before the project is (SQLite takes powers of two, 512 to 65536).
fn page_size(s: &str) -> std::result::Result<u32, String> {
    let n: u32 = s.parse().map_err(|e| format!("{e}"))?;
    if (512..=65536).contains(&n) && n.is_power_of_two() {
        Ok(n)
    } else {
        Err(format!("a power of two from 512 to 65536, not {n}"))
    }
}

#[derive(Subcommand)]
pub enum ArtifactsCommand {
    /// Add a file to the registry and lock it
    Add {
        /// The file, relative to the package root (e.g. `data/hello.txt`)
        path: String,
        /// A dotted name for the blob
        #[arg(long)]
        name: Option<String>,
        /// The package the path is relative to (default: this project)
        #[arg(long)]
        package: Option<String>,
        #[command(flatten)]
        dir: DirArg,
    },
}

#[derive(ClapArgs)]
pub struct DirArg {
    /// The project directory (the Lake package root)
    #[arg(long, default_value = ".")]
    dir: PathBuf,
}

/// The database a query reads.
#[derive(ClapArgs)]
pub struct DbArg {
    /// The project directory (the Lake package root)
    #[arg(long, default_value = ".")]
    dir: PathBuf,
    /// The database (`sil project sqlite`), relative to the project directory
    #[arg(long, default_value = ".lake/silmaril/project.sqlite")]
    db: PathBuf,
}

/// Print a query's lines.
fn print_query(db: &DbArg, q: query::Query) -> Result<()> {
    for l in query::run(&db.dir.join(&db.db), q)? {
        println!("{l}");
    }
    Ok(())
}

/// A Lake package the project can see.
#[derive(Debug, Clone)]
pub struct Package {
    pub dir: PathBuf,
    pub url: Option<String>,
    pub rev: Option<String>,
    /// Module roots of its `[[lean_lib]]`s; `None` without a `lakefile.toml`.
    pub libs: Option<Vec<String>>,
}

/// The project as read from disk: manifest, lakefile defaults and Lake packages.
#[derive(Debug, Clone)]
pub struct Project {
    /// Every package's `silmaril.toml` (the local one too), by package name; `Err` holds why
    /// it could not be read.
    pub manifests: BTreeMap<String, std::result::Result<Option<Manifest>, String>>,
    pub dir: PathBuf,
    pub manifest: Option<Manifest>,
    pub name: String,
    pub modules: Vec<String>,
    /// Module prefixes that are local.
    pub roots: Vec<String>,
    /// Dependencies from `lake-manifest.json`, by name.
    pub packages: BTreeMap<String, Package>,
}

fn unquote(name: &str) -> String {
    name.trim_start_matches('«')
        .trim_end_matches('»')
        .to_string()
}

/// `(name, lean_lib roots and glob prefixes)` of a `lakefile.toml`, if there is one.
fn lakefile(dir: &Path) -> Result<Option<(Option<String>, Vec<String>)>> {
    let path = dir.join("lakefile.toml");
    let Ok(text) = fs::read_to_string(&path) else {
        return Ok(None);
    };
    let v: toml::Value = toml::from_str(&text)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not parse {}", path.display()))?;
    let name = v.get("name").and_then(|n| n.as_str()).map(unquote);
    let mut libs = Vec::new();
    for lib in v
        .get("lean_lib")
        .and_then(|l| l.as_array())
        .into_iter()
        .flatten()
    {
        let roots: Vec<String> = match lib.get("roots").and_then(|r| r.as_array()) {
            Some(rs) => rs.iter().filter_map(|r| r.as_str()).map(unquote).collect(),
            None => lib
                .get("name")
                .and_then(|n| n.as_str())
                .map(unquote)
                .into_iter()
                .collect(),
        };
        libs.extend(roots);
        // A library may narrow `roots` and list its modules by `globs` (`Silmaril` does): a glob
        // `A.B.+`/`A.B.*` owns the modules under `A.B`, a plain `A.B` that module.
        if let Some(gs) = lib.get("globs").and_then(|g| g.as_array()) {
            libs.extend(gs.iter().filter_map(|g| g.as_str()).map(|g| {
                let g = unquote(g);
                g.strip_suffix(".+")
                    .or_else(|| g.strip_suffix(".*"))
                    .map(str::to_string)
                    .unwrap_or(g)
            }));
        }
    }
    Ok(Some((name, libs)))
}

/// The directories module paths are relative to: the package root, the package's `srcDir` and
/// each `[[lean_lib]]`'s `srcDir` (relative to the package's) in `lakefile.toml`, deduplicated.
fn source_dirs(dir: &Path) -> Vec<PathBuf> {
    let mut out = vec![dir.to_path_buf()];
    let Some(v) = fs::read_to_string(dir.join("lakefile.toml"))
        .ok()
        .and_then(|t| toml::from_str::<toml::Value>(&t).ok())
    else {
        return out;
    };
    let src = |t: &toml::Value| t.get("srcDir").and_then(|s| s.as_str()).map(String::from);
    let pkg = dir.join(src(&v).unwrap_or_default());
    let libs = v.get("lean_lib").and_then(|l| l.as_array());
    let dirs = std::iter::once(pkg.clone()).chain(
        libs.into_iter()
            .flatten()
            .filter_map(src)
            .map(|s| pkg.join(s)),
    );
    for d in dirs {
        if !out.contains(&d) {
            out.push(d);
        }
    }
    out
}

fn read_manifest(dir: &Path) -> std::result::Result<Option<Manifest>, String> {
    match fs::read_to_string(dir.join("silmaril.toml")) {
        Ok(text) => toml::from_str(&text)
            .map(Some)
            .map_err(|e| format!("could not parse silmaril.toml: {e}")),
        Err(_) => Ok(None),
    }
}

/// A path relative to a package root: not empty, not absolute, no `.` or `..`.
/// Where `dump` writes the dump and `check`, `sqlite` and `lint` read it.
const DEFAULT_DUMP: &str = ".lake/silmaril/dump.json";

fn relative_path_ok(path: &str) -> bool {
    let rel = Path::new(path);
    !path.is_empty()
        && !rel.is_absolute()
        && rel
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)))
}

impl Project {
    pub fn load(dir: &Path) -> Result<Self> {
        let manifest = read_manifest(dir).map_err(|e| miette!("{e}"))?;
        let (lake_name, libs) = lakefile(dir)?.unwrap_or_default();
        let mut lake_manifest_name = None;
        let mut packages = BTreeMap::new();
        if let Ok(text) = fs::read_to_string(dir.join("lake-manifest.json")) {
            let v: serde_json::Value = serde_json::from_str(&text)
                .into_diagnostic()
                .wrap_err("could not parse lake-manifest.json")?;
            lake_manifest_name = v.get("name").and_then(|n| n.as_str()).map(unquote);
            let pkgs_dir = v
                .get("packagesDir")
                .and_then(|d| d.as_str())
                .unwrap_or(".lake/packages");
            for pk in v
                .get("packages")
                .and_then(|p| p.as_array())
                .into_iter()
                .flatten()
            {
                let s = |k: &str| pk.get(k).and_then(|x| x.as_str()).map(String::from);
                let Some(name) = s("name").map(|n| unquote(&n)) else {
                    continue;
                };
                let pdir = match (s("type").as_deref(), s("dir")) {
                    (Some("path"), Some(d)) => dir.join(d),
                    _ => dir.join(pkgs_dir).join(&name),
                };
                let libs = lakefile(&pdir)?.map(|(_, l)| l);
                packages.insert(
                    name,
                    Package {
                        dir: pdir,
                        url: s("url"),
                        rev: s("rev"),
                        libs,
                    },
                );
            }
        }
        let m = manifest.as_ref();
        let name = m
            .and_then(|m| m.name.clone())
            .or(lake_name)
            .or(lake_manifest_name)
            .unwrap_or_else(|| "project".into());
        let modules = m.and_then(|m| m.modules.clone()).unwrap_or(libs);
        let mut manifests = BTreeMap::new();
        for (n, pk) in &packages {
            manifests.insert(n.clone(), read_manifest(&pk.dir));
        }
        manifests.insert(name.clone(), Ok(manifest.clone()));
        let mut p = Project {
            manifests,
            dir: dir.to_path_buf(),
            manifest,
            name,
            modules,
            roots: Vec::new(),
            packages,
        };
        p.set_roots();
        Ok(p)
    }

    fn set_roots(&mut self) {
        self.roots = match self.manifest.as_ref().and_then(|m| m.roots.clone()) {
            Some(r) => r,
            None => {
                let mut r: Vec<String> = self
                    .modules
                    .iter()
                    .map(|m| m.split('.').next().unwrap_or(m).to_string())
                    .collect();
                r.sort();
                r.dedup();
                r
            }
        };
    }

    pub fn is_local(&self, module: &str) -> bool {
        self.roots.iter().any(|r| {
            module == r
                || module
                    .strip_prefix(r.as_str())
                    .is_some_and(|s| s.starts_with('.'))
        })
    }

    /// The package that owns `module`: this project if it is local, else the package one of
    /// whose `[[lean_lib]]` roots is a prefix.
    pub fn package_of(&self, module: &str) -> Option<String> {
        if self.is_local(module) {
            return Some(self.name.clone());
        }
        let under = |r: &String| {
            module == r
                || module
                    .strip_prefix(r.as_str())
                    .is_some_and(|s| s.starts_with('.'))
        };
        self.packages
            .iter()
            .find(|(_, p)| p.libs.iter().flatten().any(under))
            .map(|(n, _)| n.clone())
    }

    pub fn package_dir(&self, package: &str) -> Option<PathBuf> {
        if package == self.name {
            return Some(self.dir.clone());
        }
        self.packages.get(package).map(|p| p.dir.clone())
    }

    fn manifest_of(&self, package: &str) -> std::result::Result<Option<&Manifest>, String> {
        match self.manifests.get(package) {
            None => Err(format!("package {package} is not in lake-manifest.json")),
            Some(Err(e)) => Err(e.clone()),
            Some(Ok(m)) => Ok(m.as_ref()),
        }
    }

    /// The project sid of a package (R1: mandatory, never derived).
    pub fn project_sid(&self, package: &str) -> std::result::Result<[u8; 32], String> {
        let m = self.manifest_of(package)?.ok_or_else(|| {
            "declares objects but has no silmaril.toml with a project sid (`sil project init`)"
                .to_string()
        })?;
        let s = m
            .sid
            .as_deref()
            .ok_or_else(|| "silmaril.toml has no project sid".to_string())?;
        sid::parse(s).ok_or_else(|| format!("project sid {s:?} is not 64 lowercase hex digits"))
    }

    pub fn project_row(&self, package: &str, sid: [u8; 32], local: bool) -> ProjectRow {
        let m = self.manifest_of(package).ok().flatten();
        ProjectRow {
            sid: hash::hex(&sid),
            name: package.into(),
            origin: if local { "local" } else { "imported" }.into(),
            version: m.and_then(|m| m.version.clone()),
            description: m.and_then(|m| m.description.clone()),
            root: None,
            url: None,
            rev: None,
        }
    }

    /// The registry path of a package, relative to its root.
    pub fn registry_path(&self, package: &str) -> String {
        self.manifest_of(package)
            .ok()
            .flatten()
            .and_then(|m| m.artifacts.clone())
            .unwrap_or_else(|| ARTIFACTS_PATH.into())
    }

    pub fn registry_exists(&self, package: &str) -> bool {
        self.package_dir(package)
            .is_some_and(|d| d.join(self.registry_path(package)).is_file())
    }

    /// A package's registry, with its path.
    pub fn registry(&self, package: &str) -> std::result::Result<(String, Artifacts), String> {
        let path = self.registry_path(package);
        let text = self.read_package_file(package, &path)?;
        let text = String::from_utf8(text).map_err(|_| format!("{path} is not UTF-8"))?;
        let reg = toml::from_str(&text).map_err(|e| format!("could not parse {path}: {e}"))?;
        Ok((path, reg))
    }

    /// The bytes of `package:path`.
    pub fn read_package_file(
        &self,
        package: &str,
        path: &str,
    ) -> std::result::Result<Vec<u8>, String> {
        if !relative_path_ok(path) {
            return Err(format!(
                "path {path:?} must be relative, without '..' or '.'"
            ));
        }
        let dir = self
            .package_dir(package)
            .ok_or_else(|| format!("package {package} is not in lake-manifest.json"))?;
        fs::read(dir.join(path)).map_err(|_| format!("{package}:{path} does not exist"))
    }

    /// The local records files (`silmaril.records.*`, read by `silmaril load`): every `*.toml`
    /// under [`records::RECORDS_DIR`] except other silmaril files (the artifact registry, a
    /// manifest), as `(path relative to the package root, text)`, sorted by path.
    pub fn records_files(&self) -> Vec<(String, String)> {
        fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
            let Ok(rd) = fs::read_dir(dir) else { return };
            for e in rd.flatten() {
                let path = e.path();
                if path.is_dir() {
                    walk(&path, out);
                } else if path.extension().is_some_and(|x| x == "toml") {
                    out.push(path);
                }
            }
        }
        let mut found = Vec::new();
        walk(&self.dir.join(records::RECORDS_DIR), &mut found);
        let mut out: Vec<(String, String)> = found
            .into_iter()
            .filter_map(|f| {
                let text = fs::read_to_string(&f).ok()?;
                let schema = toml::from_str::<toml::Table>(&text)
                    .ok()
                    .and_then(|t| t.get("schema").and_then(|s| s.as_str()).map(String::from));
                let other = schema.as_deref().is_some_and(|s| {
                    s.starts_with("silmaril.artifacts.") || s.starts_with("silmaril.project.")
                });
                let rel = f
                    .strip_prefix(&self.dir)
                    .ok()?
                    .to_string_lossy()
                    .replace('\\', "/");
                (!other).then_some((rel, text))
            })
            .collect();
        out.sort();
        out
    }

    /// The `[[input_file]]` paths of the local `lakefile.toml` (`None` without one).
    pub fn input_files(&self) -> Option<BTreeSet<String>> {
        self.lake_inputs("input_file")
    }

    /// The `[[input_dir]]` paths of the local `lakefile.toml` (`None` without one): Lake
    /// tracks every file below them.
    pub fn input_dirs(&self) -> Option<BTreeSet<String>> {
        self.lake_inputs("input_dir")
    }

    fn lake_inputs(&self, table: &str) -> Option<BTreeSet<String>> {
        let text = fs::read_to_string(self.dir.join("lakefile.toml")).ok()?;
        let v: toml::Value = toml::from_str(&text).ok()?;
        Some(
            v.get(table)
                .and_then(|l| l.as_array())
                .into_iter()
                .flatten()
                .filter_map(|f| f.get("path").and_then(|p| p.as_str()))
                .map(|p| p.trim_end_matches('/').to_string())
                .collect(),
        )
    }
}

/// The canonical text of a registry (what `lock` writes): entries sorted by CID, keys in
/// [`ArtifactEntry`] order, absent keys omitted.
pub fn registry_text(reg: &Artifacts) -> String {
    let q = |s: &str| toml::Value::String(s.into()).to_string();
    let mut out = format!(
        "# A silmaril artifact registry. `sil project lock` writes cid, size, sha256 and\n\
         # git_sha1; edit paths, name, package, type and doc by hand.\n\
         schema = {}\n",
        q(&reg.schema)
    );
    for e in &reg.artifacts {
        out += "\n[[artifact]]\n";
        let mut kv = |k: &str, v: String| out += &format!("{k} = {v}\n");
        if let Some(c) = &e.cid {
            kv("cid", q(c));
        }
        kv("type", q(&e.r#type));
        if let Some(n) = &e.name {
            kv("name", q(n));
        }
        if let Some(pk) = &e.package {
            kv("package", q(pk));
        }
        let paths: Vec<String> = e.paths.iter().map(|p| q(p)).collect();
        kv("paths", format!("[{}]", paths.join(", ")));
        if let Some(s) = e.size {
            kv("size", s.to_string());
        }
        if let Some(s) = &e.sha256 {
            kv("sha256", q(s));
        }
        if let Some(s) = &e.git_sha1 {
            kv("git_sha1", q(s));
        }
        if let Some(d) = &e.doc {
            kv("doc", q(d));
        }
        if let Some(d) = &e.derivation {
            kv("derivation", q(d));
        }
        if let Some(m) = &e.meta {
            kv("meta", toml::Value::Table(m.clone()).to_string());
        }
    }
    for d in &reg.derivations {
        out += &derivation_text(d);
    }
    out
}

/// A derivation as TOML: `[[derivation]]` with inline tables, then its `[[derivation.input]]`s.
fn derivation_text(d: &Derivation) -> String {
    let q = |s: &str| toml::Value::String(s.into()).to_string();
    let arr = |xs: Vec<String>| format!("[{}]", xs.join(", "));
    let inline = |kvs: Vec<(&str, String)>| {
        let kvs: Vec<String> = kvs.into_iter().map(|(k, v)| format!("{k} = {v}")).collect();
        format!("{{ {} }}", kvs.join(", "))
    };
    let file = |f: &FileRef| {
        let mut kvs = vec![("path", q(&f.path))];
        if let Some(c) = &f.cid {
            kvs.push(("cid", q(c)));
        }
        inline(kvs)
    };
    let mut out = String::from("\n[[derivation]]\n");
    let mut kv = |k: &str, v: String| out += &format!("{k} = {v}\n");
    kv("name", q(&d.name));
    kv("op", q(&d.op));
    kv("status", q(&d.status));
    if let Some(r) = &d.recipe {
        let mut kvs = vec![("path", q(&r.path))];
        if !r.args.is_empty() {
            kvs.push(("args", arr(r.args.iter().map(|a| q(a)).collect())));
        }
        if let Some(c) = &r.cid {
            kvs.push(("cid", q(c)));
        }
        kv("recipe", inline(kvs));
    }
    if !d.toolchain.is_empty() {
        let tools = d
            .toolchain
            .iter()
            .map(|t| inline(vec![("name", q(&t.name)), ("version", q(&t.version))]));
        kv("toolchain", arr(tools.collect()));
    }
    if !d.flags.is_empty() {
        kv("flags", arr(d.flags.iter().map(|f| q(f)).collect()));
    }
    if let Some(e) = &d.environment {
        let mut kvs = Vec::new();
        if let Some(os) = &e.os {
            kvs.push(("os", q(os)));
        }
        if let Some(a) = &e.arch {
            kvs.push(("arch", q(a)));
        }
        if !e.vars.is_empty() {
            let vars = e.vars.iter().map(|(k, v)| (k.as_str(), q(v))).collect();
            kvs.push(("vars", inline(vars)));
        }
        kv("environment", inline(kvs));
    }
    if let Some(r) = &d.receipt {
        kv("receipt", file(r));
    }
    if let Some(doc) = &d.doc {
        kv("doc", q(doc));
    }
    if let Some(m) = &d.meta {
        kv("meta", toml::Value::Table(m.clone()).to_string());
    }
    for i in &d.inputs {
        out += "\n[[derivation.input]]\n";
        let mut kv = |k: &str, v: String| out += &format!("{k} = {v}\n");
        kv("role", q(&i.role));
        for (k, v) in [
            ("name", &i.name),
            ("artifact", &i.artifact),
            ("path", &i.path),
            ("cid", &i.cid),
            ("url", &i.url),
            ("sha256", &i.sha256),
        ] {
            if let Some(v) = v {
                kv(k, q(v));
            }
        }
        if let Some(g) = &i.git {
            kv(
                "git",
                inline(vec![("repo", q(&g.repo)), ("rev", q(&g.rev))]),
            );
        }
        if let Some(a) = &i.available {
            kv("available", q(a));
        }
    }
    out
}

/// `sil project lock`: hash every path of the local registry, fill the digests, merge entries
/// with one CID, sort, and write the canonical text. Returns the lines to print.
pub fn lock(p: &Project) -> Result<Vec<String>> {
    let (_, reg) = p.registry(&p.name).map_err(|e| miette!("{e}"))?;
    let (text, lines) = locked(p, reg)?;
    let path = p.registry_path(&p.name);
    write_atomic(&p.dir.join(&path), &text)?;
    Ok(lines)
}

/// Write `text` to `path` through a temporary file in the same directory and a rename, so a
/// failed write never leaves a half-written file.
fn write_atomic(path: &Path, text: &str) -> Result<()> {
    // Write through a symlink (the self-test mirrors `silmaril/artifacts.toml` as one): renaming
    // over the link would replace it with a regular file.
    let resolved = if path.is_symlink() {
        fs::canonicalize(path).into_diagnostic()?
    } else {
        path.to_path_buf()
    };
    let path = resolved.as_path();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).into_diagnostic()?;
    }
    let tmp = path.with_extension("tmp~");
    fs::write(&tmp, text)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not write {}", tmp.display()))?;
    fs::rename(&tmp, path)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not write {}", path.display()))
}

/// Lock a registry in memory: hash every path, fill the digests, merge entries with one CID and
/// sort. Returns the canonical text and the lines to print (the last one says what will be
/// written); writes nothing.
fn locked(p: &Project, mut reg: Artifacts) -> Result<(String, Vec<String>)> {
    let path = p.registry_path(&p.name);
    if !ARTIFACTS_SCHEMAS.contains(&reg.schema.as_str()) {
        bail!(
            "{path}: schema {:?} is not {ARTIFACTS_SCHEMA:?}",
            reg.schema
        );
    }
    if !reg.derivations.is_empty() && reg.schema != ARTIFACTS_SCHEMA {
        bail!("{path}: `[[derivation]]` needs schema = {ARTIFACTS_SCHEMA:?}");
    }
    let mut lines = Vec::new();
    let mut by_cid: BTreeMap<String, ArtifactEntry> = BTreeMap::new();
    for mut e in std::mem::take(&mut reg.artifacts) {
        let label = e
            .name
            .clone()
            .or_else(|| e.paths.first().cloned())
            .unwrap_or_default();
        let package = e.package.clone().unwrap_or_else(|| p.name.clone());
        if e.paths.is_empty() {
            bail!("{path}: entry {label:?} has no paths");
        }
        let mut digests: Option<hash::Digests> = None;
        for f in &e.paths {
            let bytes = p
                .read_package_file(&package, f)
                .map_err(|e| miette!("{path}: {e}"))?;
            let d = hash::Digests::of(&bytes);
            if let Some(prev) = &digests
                && prev.cid != d.cid
            {
                bail!(
                    "{path}: the paths of {label:?} have different contents ({} and {f})",
                    e.paths[0]
                );
            }
            digests = Some(d);
        }
        let d = digests.expect("paths is not empty");
        if e.cid.as_deref() != Some(d.cid.as_str()) {
            lines.push(format!(
                "{label}: {} -> {}",
                e.cid.as_deref().unwrap_or("(none)"),
                d.cid
            ));
        }
        e.cid = Some(d.cid.clone());
        e.size = Some(d.size);
        e.sha256 = Some(d.sha256);
        e.git_sha1 = Some(d.git_sha1);
        match by_cid.get_mut(&d.cid) {
            None => {
                by_cid.insert(d.cid, e);
            }
            Some(prev) => {
                if prev.package != e.package {
                    bail!(
                        "{path}: {} is registered from packages {:?} and {:?}",
                        d.cid,
                        prev.package,
                        e.package
                    );
                }
                match (&prev.name, &e.name) {
                    (Some(a), Some(b)) if a != b => {
                        bail!("{path}: {} is named both {a} and {b}", d.cid);
                    }
                    (None, Some(_)) => prev.name = e.name.clone(),
                    _ => {}
                }
                if prev.doc.is_none() {
                    prev.doc = e.doc.clone();
                }
                if prev.meta.is_none() {
                    prev.meta = e.meta.clone();
                }
                prev.paths.extend(e.paths);
                lines.push(format!("{label}: merged into {}", d.cid));
            }
        }
    }
    reg.artifacts = by_cid
        .into_values()
        .map(|mut e| {
            e.paths.sort();
            e.paths.dedup();
            e
        })
        .collect();
    // the CIDs of the files derivations name (recipes, receipts, path inputs)
    let cid_of = |f: &str| -> Result<String> {
        let bytes = p
            .read_package_file(&p.name, f)
            .map_err(|e| miette!("{path}: {e}"))?;
        Ok(hash::Digests::of(&bytes).cid)
    };
    for d in &mut reg.derivations {
        let mut files: Vec<(&str, &mut Option<String>)> = Vec::new();
        if let Some(r) = &mut d.recipe {
            files.push((&r.path, &mut r.cid));
        }
        if let Some(r) = &mut d.receipt {
            files.push((&r.path, &mut r.cid));
        }
        for i in &mut d.inputs {
            if let Some(f) = &i.path {
                files.push((f, &mut i.cid));
            }
        }
        for (f, cid) in files {
            let c = cid_of(f)?;
            if cid.as_deref() != Some(c.as_str()) {
                lines.push(format!(
                    "{}: {f}: {} -> {c}",
                    d.name,
                    cid.as_deref().unwrap_or("(none)")
                ));
                *cid = Some(c);
            }
        }
    }
    let n = reg.artifacts.len();
    lines.push(format!("wrote {path} ({n} artifacts)"));
    Ok((registry_text(&reg), lines))
}

/// `sil project init`: the manifest with a fresh sid, an empty registry and a commented
/// records file, so that `lock`, `lint` and `artifacts add` work right away.
fn init(dir: &Path) -> Result<()> {
    if !dir.is_dir() {
        bail!("{}: no such directory", dir.display());
    }
    let path = dir.join("silmaril.toml");
    if path.exists() {
        bail!("{} exists", path.display());
    }
    let mut p = Project::load(dir)?;
    if !dir.join("lakefile.toml").exists() && !dir.join("lake-manifest.json").exists() {
        let abs = fs::canonicalize(dir).into_diagnostic()?;
        p.name = abs
            .file_name()
            .map_or_else(|| "project".into(), |n| n.to_string_lossy().into_owned());
        let lean = if dir.join("lakefile.lean").exists() {
            " (lakefile.lean is not read)"
        } else {
            ""
        };
        eprintln!(
            "warning: no lakefile.toml{lean}: naming the project {:?} after its directory; \
             set `name` in silmaril.toml to the Lake package name",
            p.name
        );
    }
    let sid = sid::random().into_diagnostic()?;
    let q = |s: &str| toml::Value::String(s.into()).to_string();
    let text = format!(
        "schema = {}\nsid = {}\nname = {}\n",
        q(MANIFEST_SCHEMA),
        q(&sid),
        q(&p.name)
    );
    fs::write(&path, text).into_diagnostic()?;
    println!("wrote silmaril.toml (sid {sid})");
    let reg = p.registry_path(&p.name);
    if !dir.join(&reg).exists() {
        let empty = Artifacts {
            schema: ARTIFACTS_SCHEMA.into(),
            ..Default::default()
        };
        write_atomic(&dir.join(&reg), &registry_text(&empty))?;
        println!("wrote {reg} (no artifacts yet: `sil project artifacts add PATH`)");
    }
    if p.records_files().is_empty() {
        // a name prefix that is a valid dotted name
        let mut prefix: String = p
            .name
            .to_lowercase()
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        if !prefix.starts_with(|c: char| c.is_ascii_lowercase()) {
            prefix = format!("p{prefix}");
        }
        let rel = format!("{}/records.toml", records::RECORDS_DIR);
        write_atomic(&dir.join(&rel), &records_template(&prefix))?;
        println!("wrote {rel} (a commented example; `silmaril load \"{rel}\"` reads it)");
    }
    Ok(())
}

/// The records file `init` writes: valid and empty, with commented examples.
fn records_template(prefix: &str) -> String {
    format!(
        "# A silmaril records file. A module of the project reads it with
#   silmaril load \"silmaril/records.toml\"
# and `sil project lint` checks it without Lean. `sil project schema` lists every kind and key.
schema = {schema:?}

# The root group: every problem of the project is below it.
# root = \"{prefix}.all\"

# A value: an artifact of silmaril/artifacts.toml (`sil project artifacts add data/hello.txt`)
# read with a format. It declares the problem `{prefix}.hello.parses`.
# [[value]]
# name = \"{prefix}.hello\"
# format = \"bytes\"
# source = \"data/hello.txt\"

# A group of problems.
# [[group]]
# name = \"{prefix}.all\"
# title = \"Everything\"
# children = [\"{prefix}.hello.parses\"]
",
        schema = records::RECORDS_SCHEMA
    )
}

/// `sil project lint`: the records files (schema, duplicates, references between them) and the
/// artifact registry, without Lean.
fn lint_project(dir: &Path, paths: &[PathBuf]) -> Result<()> {
    if !dir.is_dir() {
        bail!("{}: no such directory", dir.display());
    }
    let p = Project::load(dir)?;
    if p.manifest.is_none() {
        bail!(
            "{}: no silmaril.toml; is this the project directory? (`sil project init` writes one)",
            dir.display()
        );
    }
    let files = if paths.is_empty() {
        p.records_files()
    } else {
        let mut v = Vec::new();
        for f in paths {
            let text = fs::read_to_string(dir.join(f))
                .into_diagnostic()
                .wrap_err_with(|| format!("could not read {}", f.display()))?;
            v.push((f.display().to_string(), text));
        }
        v
    };
    let extra = records::project_kinds(p.manifest.as_ref());
    let linted: Vec<(String, records::Linted)> = files
        .iter()
        .map(|(f, t)| (f.clone(), records::lint(t, &extra)))
        .collect();
    let mut errors = 0;
    for (f, l) in &linted {
        for d in &l.diags {
            println!("{f}:{}:{}: error: {}", d.line, d.col, d.msg);
            errors += 1;
        }
    }
    for (f, line, msg) in records::duplicates(linted.iter().map(|(f, l)| (f.as_str(), l))) {
        println!("{f}:{line}: error: {msg}");
        errors += 1;
    }
    let mut warnings = 0;
    for (f, line, msg) in dangling(&p, &linted) {
        println!("{f}:{line}: warning: {msg}");
        warnings += 1;
    }
    let reg_path = p.registry_path(&p.name);
    let mut artifacts = None;
    if p.registry_exists(&p.name) {
        match registry_lint(&p) {
            Ok(n) => artifacts = Some(n),
            Err(e) => {
                println!("{reg_path}: error: {e}");
                errors += 1;
            }
        }
    }
    if linted.is_empty() {
        println!(
            "warning: no records files under {}/ (a records file is a `*.toml` with schema = \
             {:?})",
            records::RECORDS_DIR,
            records::RECORDS_SCHEMA
        );
        warnings += 1;
    }
    let tables: usize = linted.iter().map(|(_, l)| l.tables.len()).sum();
    if errors > 0 {
        bail!(
            "{errors} error(s) in {} records file(s) and {reg_path}",
            linted.len()
        );
    }
    let reg = artifacts.map_or_else(
        || format!("no {reg_path}"),
        |n| format!("{reg_path}: {n} artifact(s), locked"),
    );
    let w = if warnings > 0 {
        format!(", {warnings} warning(s)")
    } else {
        String::new()
    };
    println!(
        "ok: {} records file(s), {tables} table(s); {reg}{w}",
        linted.len()
    );
    Ok(())
}

/// The local registry parses, every path exists, and it is locked (`lock` would not change
/// its entries). Returns the number of artifacts.
fn registry_lint(p: &Project) -> std::result::Result<usize, String> {
    let (_, reg) = p.registry(&p.name)?;
    let (text, _) = locked(p, reg.clone()).map_err(|e| e.to_string())?;
    let now: Artifacts = toml::from_str(&text).map_err(|e| e.to_string())?;
    if now.artifacts != reg.artifacts || now.derivations != reg.derivations {
        return Err("not locked: digests are missing or stale; run `sil project lock`".into());
    }
    Ok(reg.artifacts.len())
}

/// References between records (`children`, `of`, `root`) to names that are declared nowhere
/// lint can see: not in a records file, not written in a local `.lean` file, and not in the
/// last dump. Warnings: lint does not run Lean (`sil project check` decides).
fn dangling(p: &Project, linted: &[(String, records::Linted)]) -> Vec<(String, usize, String)> {
    let mut known: BTreeSet<String> = BTreeSet::new();
    let mut values: BTreeSet<String> = BTreeSet::new();
    for (_, l) in linted {
        for t in &l.tables {
            if let Some(n) = &t.name {
                known.insert(n.clone());
                if t.kind == "value" {
                    values.insert(n.clone());
                }
            }
        }
    }
    if let Ok(d) = read_dump(&p.dir.join(DEFAULT_DUMP)) {
        known.extend(d.problems.iter().map(|x| x.name.clone()));
        known.extend(d.records.iter().map(|r| r.key().to_string()));
    }
    let base = |n: &str| {
        n.strip_suffix(".parses")
            .or_else(|| n.rsplit_once(".agrees.").map(|(b, _)| b))
            .map(String::from)
    };
    let declared = |n: &str| {
        known.contains(n) || base(n).is_some_and(|b| values.contains(&b) || known.contains(&b))
    };
    // (file, line, label, what, reference) of the references not declared in a records file
    let mut open = Vec::new();
    for (f, l) in linted {
        for t in &l.tables {
            let label = format!("{} {}", t.kind, t.name.as_deref().unwrap_or_default());
            if let Some(serde_json::Value::Array(cs)) = t.keys.get("children") {
                for c in cs.iter().filter_map(|c| c.as_str()) {
                    open.push((f.clone(), t.line, label.clone(), "child", c.to_string()));
                }
            }
            if let Some(serde_json::Value::String(of)) = t.keys.get("of") {
                open.push((f.clone(), t.line, label.clone(), "problem", of.clone()));
            }
        }
        if let Some(r) = &l.root {
            open.push((f.clone(), 1, String::new(), "root", r.clone()));
        }
    }
    open.retain(|o| !declared(&o.4));
    // The rest may be declared in Lean: look for the name (or the value it is an obligation
    // of) in the `.lean` files of the local module roots.
    let mut wanted: BTreeSet<String> = open
        .iter()
        .flat_map(|o| [Some(o.4.clone()), base(&o.4)])
        .flatten()
        .collect();
    let mut found = BTreeSet::new();
    fn walk(path: &Path, wanted: &mut BTreeSet<String>, found: &mut BTreeSet<String>) {
        if wanted.is_empty() {
            return;
        }
        // Do not follow symlinked directories: a link loop would recurse without end.
        if fs::symlink_metadata(path).is_ok_and(|m| m.is_dir()) {
            for e in fs::read_dir(path).into_iter().flatten().flatten() {
                if !e.file_name().to_string_lossy().starts_with('.') {
                    walk(&e.path(), wanted, found);
                }
            }
        } else if path.extension().is_some_and(|x| x == "lean")
            && let Ok(text) = fs::read_to_string(path)
        {
            wanted.retain(|w| {
                let hit = text.contains(w.as_str());
                if hit {
                    found.insert(w.clone());
                }
                !hit
            });
        }
    }
    if p.roots.is_empty() {
        walk(&p.dir, &mut wanted, &mut found);
    }
    for src in source_dirs(&p.dir) {
        for r in &p.roots {
            let r = r.replace('.', "/");
            walk(&src.join(format!("{r}.lean")), &mut wanted, &mut found);
            walk(&src.join(&r), &mut wanted, &mut found);
        }
    }
    open.retain(|o| !found.contains(&o.4) && !base(&o.4).is_some_and(|b| found.contains(&b)));
    open.into_iter()
        .map(|(f, line, label, what, r)| {
            let msg = if what == "root" {
                format!("root {r} is not declared in a records file, a local .lean file or the last dump")
            } else {
                format!(
                    "{label}: {what} {r} is not declared in a records file, a local .lean file \
                     or the last dump"
                )
            };
            (f, line, msg)
        })
        .collect()
}

/// A path given relative to the project directory, as printed (without a leading `./`).
fn shown(dir: &Path, rel: &Path) -> String {
    if dir == Path::new(".") || rel.is_absolute() {
        rel.display().to_string()
    } else {
        dir.join(rel).display().to_string()
    }
}

fn read_dump(path: &Path) -> Result<Dump> {
    let text = fs::read_to_string(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not read {}", path.display()))?;
    serde_json::from_str(&text)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not parse {}", path.display()))
}

/// Load project and dump and run the checks. Modules default to the dump's when neither the
/// manifest nor `lakefile.toml` names any.
fn checked(
    dir: &Path,
    dump: &Path,
    trust: Option<&Path>,
    strict_trust: bool,
) -> Result<check::Outcome> {
    let mut p = Project::load(dir)?;
    let dump = read_dump(&dir.join(dump))?;
    if p.modules.is_empty() {
        p.modules = dump.modules.clone();
        p.set_roots();
    }
    let mut o = check::run(&p, &dump);
    trust::run(dir, trust, strict_trust, &mut o)?;
    Ok(o)
}

/// Print the outcome; fail on errors. Returns the SQL text when there are none.
fn report(o: &check::Outcome) -> Result<String> {
    for e in &o.errors {
        println!("error: {e}");
    }
    for w in &o.warnings {
        println!("warning: {w}");
    }
    for l in &o.lines {
        println!("{l}");
    }
    if !o.errors.is_empty() {
        bail!("project check failed: {} error(s)", o.errors.len());
    }
    let text = sql::text(&o.db)?;
    println!("sql sha256: {}", hash::Digests::of(text.as_bytes()).sha256);
    Ok(text)
}

fn lean_str(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// The dump driver: import the project's modules and run `#silmaril_dump`.
pub fn driver(modules: &[String], out: &Path) -> String {
    let mut s = String::from("import Silmaril.Project.Defs\n");
    for m in modules {
        s += &format!("import {m}\n");
    }
    s += &format!(
        "\n#silmaril_dump {}\n",
        lean_str(&out.display().to_string())
    );
    s
}

fn run_lake(dir: &Path, lake: &[String], args: &[&str]) -> Result<()> {
    let (prog, pre) = lake
        .split_first()
        .ok_or_else(|| miette!("empty lake command"))?;
    let out = Proc::new(prog)
        .args(pre)
        .args(args)
        .current_dir(dir)
        .output()
        .into_diagnostic()
        .wrap_err_with(|| format!("could not run {prog}"))?;
    if !out.status.success() {
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        // Lake's output as is (not inside the error box), without its noise.
        eprint!("{}", lake_messages(&text));
        bail!(
            "`{prog} {}` failed (its messages are above)",
            args.join(" ")
        );
    }
    Ok(())
}

/// The messages of a failed Lake run, for people: without `trace:` lines (the command line
/// and `LEAN_PATH`) and Lake's closing summary, with errors that only follow from another
/// failure ("depends on `sorryAx`") after the others.
fn lake_messages(text: &str) -> String {
    let starts = |l: &str| {
        [
            "error:",
            "warning:",
            "info:",
            "trace:",
            "Some required targets",
        ]
        .iter()
        .any(|p| l.starts_with(p))
            || l.starts_with(['✖', '⚠', '✔', 'ℹ'])
    };
    let mut blocks: Vec<String> = Vec::new();
    for l in text.lines() {
        match blocks.last_mut() {
            Some(b) if !starts(l) => {
                b.push('\n');
                b.push_str(l);
            }
            _ => blocks.push(l.to_string()),
        }
    }
    blocks.retain(|b| {
        !b.starts_with("trace:")
            && !b.starts_with("Some required targets")
            && b != "error: build failed"
    });
    let follow_on = |b: &String| b.contains("depends on `sorryAx`");
    let (later, mut out): (Vec<String>, Vec<String>) = blocks.into_iter().partition(follow_on);
    out.extend(later);
    out.iter().map(|b| format!("{b}\n")).collect()
}

pub fn run(command: Command) -> Result<()> {
    match command {
        Command::Init {
            dir: DirArg { dir },
        } => init(&dir),
        Command::Artifacts(ArtifactsCommand::Add {
            path,
            name,
            package,
            dir: DirArg { dir },
        }) => {
            let p = Project::load(&dir)?;
            let reg_path = p.registry_path(&p.name);
            let mut reg = if p.registry_exists(&p.name) {
                p.registry(&p.name).map_err(|e| miette!("{e}"))?.1
            } else {
                Artifacts {
                    schema: ARTIFACTS_SCHEMA.into(),
                    ..Default::default()
                }
            };
            // Validate everything before writing: a failed `add` leaves the registry as it was.
            if !relative_path_ok(&path) {
                bail!(
                    "{path:?}: give a path relative to the package root, without '..' or '.' \
                     (e.g. data/hello.txt)"
                );
            }
            if let Some(n) = &name
                && let Some(why) = check::name_error(n)
            {
                bail!("--name {n:?}: {why}");
            }
            let pkg = package.clone().unwrap_or_else(|| p.name.clone());
            if p.package_dir(&pkg).is_none() {
                bail!("--package {pkg}: not a package of lake-manifest.json");
            }
            if let Err(e) = p.read_package_file(&pkg, &path) {
                bail!("{e}; nothing was added to {reg_path}");
            }
            if reg
                .artifacts
                .iter()
                .any(|e| e.package == package && e.paths.contains(&path))
            {
                bail!("{path} is already in {reg_path}");
            }
            reg.artifacts.push(ArtifactEntry {
                r#type: schema::blob(),
                name,
                package,
                paths: vec![path],
                ..Default::default()
            });
            let (text, lines) = locked(&p, reg)?;
            write_atomic(&dir.join(&reg_path), &text)?;
            for l in lines {
                println!("{l}");
            }
            Ok(())
        }
        Command::Lint {
            dir: DirArg { dir },
            paths,
        } => lint_project(&dir, &paths),
        Command::Findings { db, class } => {
            print_query(&db, query::Query::Findings(class.as_deref()))
        }
        Command::Errors { db } => print_query(&db, query::Query::Errors),
        Command::Gaps { db } => print_query(&db, query::Query::Gaps),
        Command::Deprecated { db, problems } => {
            print_query(&db, query::Query::Deprecated(problems))
        }
        Command::Schema { out } => {
            let text = format!(
                "{}\n",
                serde_json::to_string_pretty(&records::json_schema()).into_diagnostic()?
            );
            match out {
                Some(path) => fs::write(&path, text).into_diagnostic()?,
                None => print!("{text}"),
            }
            Ok(())
        }
        Command::Lock {
            dir: DirArg { dir },
        } => {
            for l in lock(&Project::load(&dir)?)? {
                println!("{l}");
            }
            Ok(())
        }
        Command::Dump {
            dir: DirArg { dir },
            out,
            lake,
            no_build,
        } => {
            let p = Project::load(&dir)?;
            if p.modules.is_empty() {
                bail!(
                    "no modules: set `modules` in silmaril.toml or a [[lean_lib]] in lakefile.toml"
                );
            }
            let lake: Vec<String> = lake
                .or_else(|| std::env::var("SIL_LAKE").ok())
                .unwrap_or_else(|| "lake".into())
                .split_whitespace()
                .map(String::from)
                .collect();
            let abs_dir = fs::canonicalize(&dir).into_diagnostic()?;
            let shown = shown(&dir, &out);
            let out = abs_dir.join(out);
            if let Some(parent) = out.parent() {
                fs::create_dir_all(parent).into_diagnostic()?;
            }
            let driver_path = abs_dir.join(".lake/silmaril/Dump.lean");
            fs::create_dir_all(driver_path.parent().unwrap()).into_diagnostic()?;
            fs::write(&driver_path, driver(&p.modules, &out)).into_diagnostic()?;
            if !no_build {
                let mut args = vec!["build", "--wfail"];
                args.extend(p.modules.iter().map(String::as_str));
                eprintln!(
                    "building {} with `{} {}` (the first build of the dependencies can take \
                     long; `--no-build` skips this step)…",
                    p.modules.join(", "),
                    lake.join(" "),
                    args.join(" ")
                );
                run_lake(&abs_dir, &lake, &args)?;
            }
            let driver_arg = driver_path.display().to_string();
            eprintln!("elaborating the dump driver (`#silmaril_dump`)…");
            run_lake(&abs_dir, &lake, &["env", "lean", &driver_arg])?;
            let d = read_dump(&out)?;
            eprintln!(
                "wrote {shown} ({} records, {} problems, {} solutions)",
                d.records.len(),
                d.problems.len(),
                d.solutions.len()
            );
            Ok(())
        }
        Command::TrustDump {
            dir: DirArg { dir },
            modules,
            roots,
            out,
            lake,
            no_build,
            exclude,
        } => {
            let modules = if modules.is_empty() {
                Project::load(&dir)?.modules
            } else {
                modules
            };
            if modules.is_empty() {
                bail!("no modules: pass --module or set `modules` in silmaril.toml");
            }
            let roots = if roots.is_empty() {
                vec!["Silmaril".to_string()]
            } else {
                roots
            };
            let lake: Vec<String> = lake
                .or_else(|| std::env::var("SIL_LAKE").ok())
                .unwrap_or_else(|| "lake".into())
                .split_whitespace()
                .map(String::from)
                .collect();
            let abs_dir = fs::canonicalize(&dir).into_diagnostic()?;
            let gen_dir = abs_dir.join(".lake/silmaril");
            fs::create_dir_all(&gen_dir).into_diagnostic()?;
            let raw = gen_dir.join("trust.raw.jsonl");
            let core_raw = gen_dir.join("trust.core.jsonl");
            if trust::core_has_hooks(&abs_dir) == Some(false) {
                bail!(
                    "the core trust framework here has no stable dump hooks (moduleLine, auditLine): \
                     trust-dump needs #125 at ba1b5f84 or later"
                );
            }
            let excluded: Vec<(String, String)> = exclude
                .iter()
                .map(|e| {
                    e.split_once('=')
                        .map(|(m, r)| (m.trim().to_string(), r.trim().to_string()))
                        .filter(|(m, r)| !m.is_empty() && !r.is_empty())
                        .ok_or_else(|| miette!("--exclude {e:?}: give MODULE=REASON"))
                })
                .collect::<Result<_>>()?;
            let _ = fs::remove_file(&core_raw);
            let driver_path = gen_dir.join("TrustDump.lean");
            fs::write(
                &driver_path,
                trust::driver(&modules, &roots, &raw, &core_raw),
            )
            .into_diagnostic()?;
            if !no_build {
                let mut args = vec!["build", "--wfail"];
                args.extend(modules.iter().map(String::as_str));
                eprintln!("building {} …", modules.join(", "));
                run_lake(&abs_dir, &lake, &args)?;
            }
            eprintln!("elaborating the trust driver…");
            run_lake(
                &abs_dir,
                &lake,
                &["env", "lean", &driver_path.display().to_string()],
            )?;
            let text = fs::read_to_string(&raw).into_diagnostic()?;
            let core = fs::read_to_string(&core_raw).into_diagnostic()?;
            let producer = format!(
                "silmaril-project {} trust-dump (core stable hooks)",
                env!("CARGO_PKG_VERSION")
            );
            let lines = trust::complete(
                &text,
                &core,
                &abs_dir,
                &trust::Completion {
                    roots: &roots,
                    producer: &producer,
                    inputs: &["lean-toolchain", "lake-manifest.json", "policy.toml"],
                    excluded: &excluded,
                },
            )
            .map_err(|e| miette!("{e}"))?;
            let shown = shown(&dir, &out);
            let out = abs_dir.join(out);
            if let Some(p) = out.parent() {
                fs::create_dir_all(p).into_diagnostic()?;
            }
            fs::write(&out, &lines).into_diagnostic()?;
            eprintln!("wrote {shown} ({} lines)", lines.lines().count());
            Ok(())
        }
        Command::Check {
            dir: DirArg { dir },
            dump,
            trust,
            strict_trust,
        } => report(&checked(&dir, &dump, trust.as_deref(), strict_trust)?).map(|_| ()),
        Command::Sqlite {
            dir: DirArg { dir },
            dump,
            trust,
            strict_trust,
            sql: sql_path,
            db,
            httpvfs,
            page_size,
        } => {
            let text = report(&checked(&dir, &dump, trust.as_deref(), strict_trust)?)?;
            let sql_path = dir.join(sql_path);
            if let Some(parent) = sql_path.parent() {
                fs::create_dir_all(parent).into_diagnostic()?;
            }
            fs::write(&sql_path, &text).into_diagnostic()?;
            sql::write_db(&text, &dir.join(db), httpvfs.then_some(page_size))?;
            Ok(())
        }
        Command::Explore {
            dir: DirArg { dir },
            db,
            out,
        } => {
            let p = Project::load(&dir)?;
            let out_dir = out.parent().unwrap_or(Path::new(""));
            // Over http(s) the page tries `?db=`, then `--db` (relative to the page), then a
            // `project.sqlite` next to it.
            let mut urls: Vec<String> = explore::relative_url(out_dir, &db).into_iter().collect();
            if !urls.iter().any(|u| u == "project.sqlite") {
                urls.push("project.sqlite".into());
            }
            let page = explore::page(&format!("{} · silmaril project", p.name), &urls);
            let shown = shown(&dir, &out);
            let out = dir.join(out);
            if let Some(parent) = out.parent() {
                fs::create_dir_all(parent).into_diagnostic()?;
            }
            fs::write(&out, page).into_diagnostic()?;
            eprintln!("wrote {shown}; it opens {}", urls.join(", then "));
            if !dir.join(&db).exists() {
                eprintln!(
                    "note: {} does not exist yet; run `sil project sqlite`",
                    db.display()
                );
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::schema::*;
    use super::*;

    #[test]
    fn write_atomic_writes_through_symlinks() {
        let dir = std::env::temp_dir().join(format!("silmaril-project-wa-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let real = dir.join("real.toml");
        fs::write(&real, "old").unwrap();
        let link = dir.join("link.toml");
        std::os::unix::fs::symlink(&real, &link).unwrap();
        write_atomic(&link, "new").unwrap();
        assert!(link.is_symlink(), "the link must survive");
        assert_eq!(fs::read_to_string(&real).unwrap(), "new");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn records_reject_unknown_kinds_and_keys() {
        let ok: Record =
            serde_json::from_str(r#"{"kind":"model","name":"a.m","module":"A","decl":"A.m"}"#)
                .unwrap();
        assert_eq!((ok.kind(), ok.key(), ok.module()), ("model", "a.m", "A"));
        assert_eq!(object_kind("format_default"), Some("family"));
        assert!(
            serde_json::from_str::<Record>(
                r#"{"kind":"model","name":"a.m","module":"A","decl":"A.m","extra":1}"#
            )
            .is_err()
        );
        assert!(
            serde_json::from_str::<Record>(r#"{"kind":"widget","name":"a","module":"A"}"#).is_err()
        );
        // v0 kinds and keys are gone.
        for old in [
            r#"{"kind":"task","name":"a","module":"A"}"#,
            r#"{"kind":"model","id":"a","module":"A","decl":"A.m"}"#,
        ] {
            assert!(serde_json::from_str::<Record>(old).is_err(), "{old}");
        }
        // `origin` is computed by the checker, never read; `sid` is the override.
        assert!(
            serde_json::from_str::<Record>(
                r#"{"kind":"model","name":"a.m","module":"A","decl":"A.m","origin":"local"}"#
            )
            .is_err()
        );
        let r: Record = serde_json::from_str(
            r#"{"kind":"model","name":"a.m","module":"A","decl":"A.m","sid":"00"}"#,
        )
        .unwrap();
        let Record::Model(m) = r else { panic!() };
        assert_eq!(
            (m.sid.as_str(), m.sid_override.as_deref()),
            ("", Some("00"))
        );
    }

    #[test]
    fn ddl_and_literals() {
        assert_eq!(sql::literal(&Sql::Text("it's".into())), "'it''s'");
        assert_eq!(sql::literal(&Sql::Null), "NULL");
        assert_eq!(sql::literal(&Sql::Int(-3)), "-3");
        let d = sql::ddl(&info::<ArtifactPath>());
        assert!(d.contains("PRIMARY KEY(package, path)"), "{d}");
        let d = sql::ddl(&info::<Object>());
        assert!(d.contains("sid TEXT NOT NULL PRIMARY KEY"), "{d}");
        assert!(d.contains("UNIQUE(kind, name)"), "{d}");
        let d = sql::ddl(&info::<Value>());
        assert!(!d.contains("sources") && !d.contains("sid_override"), "{d}");
        let d = sql::ddl(&info::<Room>());
        assert!(d.contains("mod TEXT NOT NULL"), "{d}");
    }

    #[test]
    fn indexes_name_columns_of_their_tables() {
        let mut names = std::collections::HashSet::new();
        for (name, table, cols) in schema::INDEXES {
            assert!(names.insert(*name), "duplicate index {name}");
            assert!(
                name.starts_with(&format!("{table}_")),
                "{name} is not named after {table}"
            );
            let t = tables()
                .into_iter()
                .find(|t| t.name == *table)
                .expect(table);
            for c in *cols {
                assert!(
                    t.columns.iter().any(|(k, _)| schema::column(k) == *c),
                    "{table}.{c}"
                );
            }
            assert!(
                !t.key.starts_with(cols),
                "{name} repeats the primary key of {table}"
            );
        }
    }

    #[test]
    fn empty_database_round_trips() {
        let mut db = Database::default();
        for t in tables() {
            db.tables.push((t, Vec::new()));
        }
        let text = sql::text(&db).unwrap();
        let dir = tempfile::tempdir().unwrap();
        sql::write_db(&text, &dir.path().join("x.sqlite"), None).unwrap();
        // Tuned for httpvfs: same logical dump and indexes (checked by `write_db`), page size.
        let tuned = dir.path().join("y.sqlite");
        sql::write_db(&text, &tuned, Some(1024)).unwrap();
        let conn = rusqlite::Connection::open(&tuned).unwrap();
        let ps: i64 = conn
            .query_row("PRAGMA page_size", [], |r| r.get(0))
            .unwrap();
        assert_eq!(ps, 1024);
        assert!(sql::write_db(&text, &tuned, Some(1000)).is_err());
    }

    #[test]
    fn registry_text_round_trips() {
        let reg = Artifacts {
            schema: ARTIFACTS_SCHEMA.into(),
            artifacts: vec![ArtifactEntry {
                cid: Some("bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi".into()),
                r#type: "blob".into(),
                name: Some("a.b".into()),
                paths: vec!["x \"q\".bin".into()],
                size: Some(0),
                derivation: Some("a.build".into()),
                meta: Some(
                    toml::from_str("origin = { file = \"a/artifact.toml\", n = [1, 2] }").unwrap(),
                ),
                ..Default::default()
            }],
            derivations: vec![Derivation {
                name: "a.build".into(),
                op: "compile".into(),
                status: "reproduced".into(),
                recipe: Some(Recipe {
                    path: "build.sh".into(),
                    args: vec!["-O2".into()],
                    cid: None,
                }),
                toolchain: vec![Tool {
                    name: "gcc".into(),
                    version: "13.3.0".into(),
                }],
                flags: vec!["-static".into()],
                environment: Some(Environment {
                    os: Some("ubuntu-24.04".into()),
                    arch: None,
                    vars: [("LC_ALL".to_string(), "C".to_string())].into(),
                }),
                receipt: Some(FileRef {
                    path: "RECEIPTS.sha256".into(),
                    cid: None,
                }),
                doc: Some("d".into()),
                meta: Some(toml::from_str("lean = { module = \"M\" }").unwrap()),
                inputs: vec![
                    DerivationInput {
                        role: "source".into(),
                        url: Some("https://example.org/x.tar.gz".into()),
                        sha256: Some("0".repeat(64)),
                        ..Default::default()
                    },
                    DerivationInput {
                        role: "source".into(),
                        git: Some(GitRev {
                            repo: "https://example.org/x".into(),
                            rev: "1".repeat(40),
                        }),
                        ..Default::default()
                    },
                ],
            }],
        };
        let text = registry_text(&reg);
        let back: Artifacts = toml::from_str(&text).unwrap();
        assert_eq!(back.artifacts, reg.artifacts);
        assert_eq!(back.derivations, reg.derivations);
        assert_eq!(registry_text(&back), text);
    }

    /// Every subcommand and argument of `sil project` has a description.
    #[test]
    fn help_describes_everything() {
        use clap::{CommandFactory, Parser};
        #[derive(Parser)]
        struct Cli {
            #[command(subcommand)]
            command: Command,
        }
        fn walk(c: &clap::Command, path: &str, missing: &mut Vec<String>) {
            for a in c.get_arguments() {
                if a.get_help().is_none() && !matches!(a.get_id().as_str(), "help" | "version") {
                    missing.push(format!("{path} {}", a.get_id()));
                }
            }
            for sc in c.get_subcommands() {
                let p = format!("{path} {}", sc.get_name());
                if sc.get_about().is_none() {
                    missing.push(p.clone());
                }
                walk(sc, &p, missing);
            }
        }
        let mut missing = Vec::new();
        walk(&Cli::command(), "sil project", &mut missing);
        assert!(missing.is_empty(), "no description: {missing:?}");
    }

    #[test]
    fn lake_messages_drop_noise() {
        let text = "\
✖ [2800/2802] Building Tiny (1.3s)
trace: .> LEAN_PATH=/a/b:/c/d /x/bin/lean /p/Tiny.lean -o /p/.lake/build/lib/lean/Tiny.olean --json
error: Tiny.lean:7:0: @[solves \"t.port\"]: t.port.sol depends on `sorryAx`; a solution must be complete
error: Tiny.lean:8:8: Tactic `decide` proved that the proposition
  1 = 2
is false
Some required targets logged failures:
- Tiny
error: build failed
";
        assert_eq!(
            lake_messages(text),
            "\
✖ [2800/2802] Building Tiny (1.3s)
error: Tiny.lean:8:8: Tactic `decide` proved that the proposition
  1 = 2
is false
error: Tiny.lean:7:0: @[solves \"t.port\"]: t.port.sol depends on `sorryAx`; a solution must be complete
"
        );
    }

    #[test]
    fn driver_quotes_paths() {
        let d = driver(&["Demo".into()], Path::new("/x/\"q\"/dump.json"));
        assert!(d.contains("import Demo\n"));
        assert!(d.contains(r#"#silmaril_dump "/x/\"q\"/dump.json""#));
    }
}
