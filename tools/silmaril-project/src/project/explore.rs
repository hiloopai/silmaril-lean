//! `sil project explore`: one static HTML page over the project database.
//!
//! The page (`explore.html`, next to this file) holds no data: it opens a separate SQLite file
//! in the browser, with pinned scripts from cdnjs/jsdelivr. Over http(s) it tries `?db=<url>`,
//! then the `db_urls` written here (relative to the page). It reads the file lazily with
//! sql.js-httpvfs (HTTP Range requests for page-aligned blocks) when the server supports
//! Range, and downloads it whole into sql.js otherwise. Over `file://`, where browsers block
//! `fetch`, the file is chosen with a file picker or dropped onto the page.
//!
//! The page's script is bundled from [`SCRIPTS`] (files in `explore/`), in order, into one
//! `<script>`: the shared shell (loading, routing, components) first, then one file per group of
//! views, each registering its views with `registerView`, then `main.js`, which starts the page.
//! A new view is a new file in `explore/views/` and one line in [`SCRIPTS`] (before `main.js`).
//! The Lean source layer (`explore/lean/`: tokens, the text-search locator, HTML lines) comes
//! before `provenance.js`, which uses it; its files are DOM-free and load in Node's tests too.

use std::path::{Component, Path};

const TEMPLATE: &str = include_str!("explore.html");
const SHELL_STYLE: &str = include_str!("explore/shell.css");

/// One file of the page's script, by its path in `explore/`.
macro_rules! script {
    ($path:literal) => {
        ($path, include_str!(concat!("explore/", $path)))
    };
}

/// The page's script, in order: name (for messages and tests) and text.
pub const SCRIPTS: &[(&str, &str)] = &[
    script!("core.js"),
    script!("status.js"),
    script!("schema.js"),
    script!("axioms.js"),
    script!("ui.js"),
    script!("lean/tokenize.js"),
    script!("lean/locate.js"),
    script!("lean/render.js"),
    script!("provenance.js"),
    script!("table.js"),
    script!("vfs-transport.js"),
    script!("vfs.js"),
    script!("db.js"),
    script!("data.js"),
    script!("view-registry.js"),
    script!("navigation.js"),
    script!("router.js"),
    script!("graphs.js"),
    script!("vendor/marked.js"),
    script!("docs.js"),
    script!("views/docs.js"),
    script!("views/summary.js"),
    script!("views/progress.js"),
    script!("views/corpus.js"),
    script!("views/compiler.js"),
    script!("views/ir.js"),
    script!("views/graph.js"),
    script!("views/lists.js"),
    script!("views/browse.js"),
    script!("views/details.js"),
    script!("views/artifact.js"),
    script!("views/machine.js"),
    script!("views/wasm.js"),
    script!("views/component-tests.js"),
    script!("views/acceptors.js"),
    script!("elf_regions.js"),
    script!("views/elf.js"),
    script!("views/compiler-artifact.js"),
    script!("views/languages.js"),
    script!("views/systems.js"),
    script!("views/containers.js"),
    script!("views/logic.js"),
    script!("views/formal.js"),
    script!("views/named-logic.js"),
    script!("views/sql.js"),
    script!("views/source.js"),
    script!("main.js"),
];

/// The bundled script: every file of [`SCRIPTS`], each after a comment naming it.
fn script() -> String {
    let mut out = format!(
        "const LEAN_STANDARD_AXIOMS = {};\n",
        script_json(&serde_json::json!(crate::project::schema::STANDARD_AXIOMS))
    );
    for (name, text) in SCRIPTS {
        out.push_str(&format!("// ===== explore/{name} =====\n"));
        out.push_str(text);
        if !text.ends_with('\n') {
            out.push('\n');
        }
    }
    out
}

/// The service worker written next to the page (`explore-sw.js`): it keeps the database pages
/// read lazily across reloads, keyed by the version tag in their URLs.
pub const SERVICE_WORKER: &str = include_str!("explore-sw.js");

/// The service worker's file name, next to the page.
pub const SERVICE_WORKER_NAME: &str = "explore-sw.js";

/// The local pinned Mermaid 11.17.2 runtime written next to the page (`explore-mermaid.js`),
/// loaded on demand by the inline documentation view with no external CDN request.
pub const MERMAID_BUNDLE: &[u8] = include_bytes!("explore/vendor/mermaid.min.js");

/// The local Mermaid bundle's file name, next to the page.
pub const MERMAID_BUNDLE_NAME: &str = "explore-mermaid.js";

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// JSON that is safe inside a `<script type="application/json">` element.
fn script_json(v: &serde_json::Value) -> String {
    serde_json::to_string(v)
        .expect("JSON value serializes")
        .replace('<', "\\u003c")
        .replace('>', "\\u003e")
        .replace('&', "\\u0026")
        .replace('\u{2028}', "\\u2028")
        .replace('\u{2029}', "\\u2029")
}

/// What the page knows about its default database when it is generated: the size and SHA-256
/// of the file's bytes. The page compares them with what the server serves (a page and a
/// database from different deploys are reported, not mixed) and verifies whole downloads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DbMeta {
    pub size: u64,
    pub sha256: String,
}

/// Where the project's Lean sources are published, for links from problems and answers to the
/// declarations' modules: a GitHub repository, a commit (links are pinned to it), and the file of
/// each module of the database that exists under the project's source directories.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceMeta {
    pub repo: String,
    pub rev: String,
    pub modules: std::collections::BTreeMap<String, String>,
}

/// Optional project metadata read from `silmaril.toml` at `explore` generation time: the
/// description (shown on the front page when the database row lacks one), optional
/// project-specific help (inline text or a relative `.md` path packaged under `_docs/`),
/// and the packaged documentation directory inventory.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProjectMeta {
    pub name: Option<String>,
    pub description: Option<String>,
    pub help: Option<String>,
    pub help_doc: Option<String>,
    pub docs_index: Option<String>,
    pub docs_dirs: Vec<String>,
}

/// Whether `repo` is a GitHub repository URL the page may link to and read raw files from.
pub fn source_repo_ok(repo: &str) -> bool {
    let Some(rest) = repo.strip_prefix("https://github.com/") else {
        return false;
    };
    let seg = |s: &str| {
        !s.is_empty()
            && s != "."
            && s != ".."
            && s.chars()
                .all(|c| c.is_ascii_alphanumeric() || "-_.".contains(c))
    };
    matches!(rest.split('/').collect::<Vec<_>>()[..], [o, r] if seg(o) && seg(r))
}

/// Whether `rev` is a commit id (7 to 40 hex digits): links are pinned to one commit.
pub fn source_rev_ok(rev: &str) -> bool {
    (7..=40).contains(&rev.len()) && rev.chars().all(|c| c.is_ascii_hexdigit())
}

/// The page titled `title`, which tries `db_urls` (relative to the page) in order; `meta`
/// describes the first of them, when it was readable at generation time; `source`, when given,
/// lets the page link declarations to their Lean sources; `project`, when given, supplies optional
/// manifest description, help and packaged documentation entry points.
pub fn page(
    title: &str,
    db_urls: &[String],
    meta: Option<&DbMeta>,
    source: Option<&SourceMeta>,
    project: Option<&ProjectMeta>,
) -> String {
    let source = source.map_or(
        serde_json::Value::Null,
        |s| serde_json::json!({ "repo": s.repo, "rev": s.rev, "modules": s.modules }),
    );
    let meta = meta.map_or(
        serde_json::Value::Null,
        |m| serde_json::json!({ "url": db_urls.first(), "size": m.size, "sha256": m.sha256 }),
    );
    let project = project.map_or(serde_json::Value::Null, |p| {
        serde_json::json!({
            "name": p.name,
            "description": p.description,
            "help": p.help,
            "helpDoc": p.help_doc,
            "docsIndex": p.docs_index,
            "docsDirs": p.docs_dirs,
        })
    });
    // The script goes in last, so that no placeholder text inside it is replaced.
    TEMPLATE
        .replace("__TITLE__", &html_escape(title))
        .replace("__DB_URLS__", &script_json(&serde_json::json!(db_urls)))
        .replace("__DB_META__", &script_json(&meta))
        .replace("__SOURCE_META__", &script_json(&source))
        .replace("__PROJECT_META__", &script_json(&project))
        .replace("__EXPLORE_SHELL_STYLE__", SHELL_STYLE)
        .replace("__EXPLORE_SCRIPT__", &script())
}

/// `target` relative to the directory `from`, when both are relative paths without `..`.
pub fn relative_url(from: &Path, target: &Path) -> Option<String> {
    let plain = |p: &Path| {
        p.components()
            .filter(|c| !matches!(c, Component::CurDir))
            .map(|c| match c {
                Component::Normal(s) => s.to_str().map(String::from),
                _ => None,
            })
            .collect::<Option<Vec<String>>>()
    };
    let (from, target) = (plain(from)?, plain(target)?);
    let common = from.iter().zip(&target).take_while(|(a, b)| a == b).count();
    let mut parts = vec!["..".to_string(); from.len() - common];
    parts.extend(target[common..].iter().cloned());
    Some(parts.join("/"))
}

/// Write `bytes` to `path` after verifying that neither `path` nor any existing parent component
/// inside `base_dir` is a symlink.
pub fn write_regular_file_bounded(
    base_dir: &Path,
    path: &Path,
    bytes: &[u8],
) -> std::io::Result<()> {
    let rel = path.strip_prefix(base_dir).map_err(|_| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("{} is not under {}", path.display(), base_dir.display()),
        )
    })?;
    let mut cur = base_dir.to_path_buf();
    if let Ok(meta) = std::fs::symlink_metadata(&cur)
        && meta.file_type().is_symlink()
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("refusing to write through symlink {}", cur.display()),
        ));
    }
    let comps: Vec<_> = rel.components().collect();
    for (i, comp) in comps.iter().enumerate() {
        let Component::Normal(seg) = comp else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("invalid path component in {}", path.display()),
            ));
        };
        cur.push(seg);
        let is_last = i + 1 == comps.len();
        match std::fs::symlink_metadata(&cur) {
            Ok(meta) => {
                if meta.file_type().is_symlink() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        format!(
                            "refusing to overwrite or traverse symlink {}",
                            cur.display()
                        ),
                    ));
                }
                if is_last && meta.is_dir() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::IsADirectory,
                        format!("{} is a directory", cur.display()),
                    ));
                }
                if !is_last && !meta.is_dir() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::AlreadyExists,
                        format!("{} is not a directory", cur.display()),
                    ));
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                if !is_last {
                    std::fs::create_dir(&cur)?;
                }
            }
            Err(e) => return Err(e),
        }
    }
    std::fs::write(&cur, bytes)
}

const DOCS_STAGE_MARKER: &str = ".silmaril-explore-docs";

/// Clean a previous `<out_dir>/_docs` directory only if it carries our staging marker (and has
/// no symlink root), preventing stale files across rebuilds without touching user-owned trees.
fn clean_staged_docs_dir(out_docs: &Path) -> std::io::Result<()> {
    let meta = match std::fs::symlink_metadata(out_docs) {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };
    if meta.file_type().is_symlink() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "refusing to use symlinked docs output {}",
                out_docs.display()
            ),
        ));
    }
    if !meta.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            format!("{} exists and is not a directory", out_docs.display()),
        ));
    }
    let marker = out_docs.join(DOCS_STAGE_MARKER);
    if std::fs::symlink_metadata(&marker).is_ok_and(|m| m.is_file() && !m.file_type().is_symlink())
    {
        std::fs::remove_dir_all(out_docs)?;
    }
    Ok(())
}

/// Enumerate Git-tracked files under `docs/` when `project_dir` is a Git worktree, returning
/// `None` when Git is unavailable or `project_dir` is not tracked by Git.
fn git_tracked_docs(project_dir: &Path) -> Option<Vec<std::path::PathBuf>> {
    let out = std::process::Command::new("git")
        .args(["-C"])
        .arg(project_dir)
        .args(["ls-files", "-z", "--", "docs"])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let raw = String::from_utf8(out.stdout).ok()?;
    let files: Vec<std::path::PathBuf> = raw
        .split('\0')
        .filter(|s| !s.is_empty())
        .map(|s| project_dir.join(s))
        .collect();
    (!files.is_empty()).then_some(files)
}

/// Package the project's Markdown guides and raster image assets from `docs/` into
/// `<out_dir>/_docs/`, returning `(docs_index, help_doc, docs_dirs)` relative to `<out_dir>/_docs/`.
///
/// Publication boundary:
/// - Only files inside `docs/` with constrained relative paths (no `.` or `..`, no hidden dot
///   segments, no symlinks anywhere along the path) and allowed extensions (`.md`, `.png`, `.jpg`,
///   `.jpeg`, `.gif`, `.webp`) are packaged.
/// - Raw `.svg` files are not packaged as standalone same-origin documents; inline Mermaid
///   diagrams render directly inside the explorer page.
/// - In a Git checkout, only Git-tracked files under `docs/` (plus an explicit `help = "docs/…"`
///   path in `silmaril.toml` if present inside `docs/`) are included, so untracked/ignored local
///   drafts are never published. Outside Git, `docs/` is walked directly under the same symlink
///   and dotfile guards.
/// - Output is staged into `<out_dir>/_docs/` (isolated from the source `docs/` directory even
///   when `--out` is in the project root).
pub fn package_project_docs(
    project_dir: &Path,
    out_dir: &Path,
    extra_doc: Option<&str>,
) -> std::io::Result<(Option<String>, Option<String>, Vec<String>)> {
    let Ok(canon_root) = std::fs::canonicalize(project_dir) else {
        return Ok((None, None, Vec::new()));
    };
    let docs_root = project_dir.join("docs");
    let Ok(docs_meta) = std::fs::symlink_metadata(&docs_root) else {
        return Ok((None, None, Vec::new()));
    };
    if docs_meta.file_type().is_symlink() || !docs_meta.is_dir() {
        return Ok((None, None, Vec::new()));
    }
    let Ok(canon_docs) = std::fs::canonicalize(&docs_root) else {
        return Ok((None, None, Vec::new()));
    };
    if !canon_docs.starts_with(&canon_root) {
        return Ok((None, None, Vec::new()));
    }

    let allowed_ext = |p: &Path| {
        p.extension().and_then(|x| x.to_str()).is_some_and(|ext| {
            matches!(
                ext.to_ascii_lowercase().as_str(),
                "md" | "png" | "jpg" | "jpeg" | "gif" | "webp"
            )
        })
    };

    // Validate that `rel` under `docs_root` has no hidden segments, no symlinks along any
    // component, is a regular file with an allowed extension, and canonicalizes inside `canon_docs`.
    let valid_docs_file = |rel: &Path| -> Option<std::path::PathBuf> {
        let mut cur = docs_root.clone();
        let comps: Vec<_> = rel.components().collect();
        if comps.is_empty() {
            return None;
        }
        for (i, comp) in comps.iter().enumerate() {
            let Component::Normal(seg) = comp else {
                return None;
            };
            let s = seg.to_str()?;
            if s.is_empty() || s.starts_with('.') {
                return None;
            }
            cur.push(seg);
            let meta = std::fs::symlink_metadata(&cur).ok()?;
            if meta.file_type().is_symlink() {
                return None;
            }
            let is_last = i + 1 == comps.len();
            if is_last {
                if !meta.is_file() || !allowed_ext(&cur) {
                    return None;
                }
            } else if !meta.is_dir() {
                return None;
            }
        }
        let canon = std::fs::canonicalize(&cur).ok()?;
        canon.starts_with(&canon_docs).then_some(cur)
    };

    let mut to_copy: std::collections::BTreeSet<std::path::PathBuf> =
        std::collections::BTreeSet::new();

    if let Some(tracked) = git_tracked_docs(project_dir) {
        for p in tracked {
            if let Ok(rel) = p.strip_prefix(&docs_root)
                && let Some(valid) = valid_docs_file(rel)
            {
                to_copy.insert(valid);
            }
        }
    } else {
        fn walk_docs(
            dir: &Path,
            docs_root: &Path,
            valid_docs_file: &dyn Fn(&Path) -> Option<std::path::PathBuf>,
            out: &mut std::collections::BTreeSet<std::path::PathBuf>,
        ) {
            let Ok(rd) = std::fs::read_dir(dir) else {
                return;
            };
            for e in rd.flatten() {
                if e.file_name().to_string_lossy().starts_with('.') {
                    continue;
                }
                let p = e.path();
                let Ok(meta) = std::fs::symlink_metadata(&p) else {
                    continue;
                };
                if meta.file_type().is_symlink() {
                    continue;
                }
                if meta.is_dir() {
                    walk_docs(&p, docs_root, valid_docs_file, out);
                } else if meta.is_file()
                    && let Ok(rel) = p.strip_prefix(docs_root)
                    && let Some(valid) = valid_docs_file(rel)
                {
                    out.insert(valid);
                }
            }
        }
        walk_docs(&docs_root, &docs_root, &valid_docs_file, &mut to_copy);
    }

    let mut help_doc_rel: Option<String> = None;
    if let Some(h) = extra_doc {
        let trimmed = h.trim();
        let rel_under_docs = trimmed.strip_prefix("docs/").unwrap_or(trimmed);
        if Path::new(rel_under_docs)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("md"))
            && let Some(valid) = valid_docs_file(Path::new(rel_under_docs))
            && let Ok(rel) = valid.strip_prefix(&docs_root)
        {
            let norm = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/");
            to_copy.insert(valid);
            help_doc_rel = Some(norm);
        }
    }

    if to_copy.is_empty() {
        return Ok((None, None, Vec::new()));
    }

    let out_docs = out_dir.join("_docs");
    if let Ok(canon_out) = std::fs::canonicalize(&out_docs)
        && canon_out == canon_docs
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "packaged docs output directory must not alias source docs/",
        ));
    }
    clean_staged_docs_dir(&out_docs)?;
    if !out_docs.exists() {
        std::fs::create_dir(&out_docs)?;
    }
    write_regular_file_bounded(
        &out_docs,
        &out_docs.join(DOCS_STAGE_MARKER),
        b"silmaril-explore-docs\n",
    )?;

    let mut packaged_rel: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut readme_dirs: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for src in &to_copy {
        let Ok(rel) = src.strip_prefix(&docs_root) else {
            continue;
        };
        let rel_str = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let bytes = std::fs::read(src)?;
        let dst = out_docs.join(rel);
        write_regular_file_bounded(&out_docs, &dst, &bytes)?;
        if rel.file_name().is_some_and(|n| n == "README.md")
            && let Some(parent) = rel.parent()
        {
            let dir_str = parent
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/");
            readme_dirs.insert(dir_str);
        }
        packaged_rel.insert(rel_str);
    }

    let index_rel = if packaged_rel.contains("projects/README.md") {
        Some("projects/README.md".to_string())
    } else if packaged_rel.contains("README.md") {
        Some("README.md".to_string())
    } else {
        None
    };

    Ok((index_rel, help_doc_rel, readme_dirs.into_iter().collect()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relative_urls() {
        let r = |a: &str, b: &str| relative_url(Path::new(a), Path::new(b));
        assert_eq!(
            r("silmaril", ".lake/silmaril/project.sqlite").as_deref(),
            Some("../.lake/silmaril/project.sqlite")
        );
        assert_eq!(r("", "x/y.sqlite").as_deref(), Some("x/y.sqlite"));
        assert_eq!(r("a/b", "a/c").as_deref(), Some("../c"));
        assert_eq!(r("/abs", "x"), None);
    }

    /// Every table and view the database has is documented on the page's Schema tab.
    #[test]
    fn every_table_has_a_note() {
        let all = script();
        let start = all.find("const TABLE_DOCS = {").expect("TABLE_DOCS");
        let docs = &all[start..start + all[start..].find("\n};").expect("end")];
        let mut names: Vec<&str> = crate::project::schema::tables()
            .iter()
            .map(|t| t.name)
            .collect();
        for v in crate::project::schema::VIEWS {
            let v = v.trim_start_matches("CREATE VIEW ");
            names.push(&v[..v.find(' ').unwrap_or(v.len())]);
        }
        for n in names {
            assert!(
                docs.contains(&format!("\n  {n}: ")),
                "no TABLE_DOCS entry for {n}"
            );
        }
    }

    /// The bundled script can sit in one `<script>` element: no file closes it or holds a
    /// placeholder, `main.js` comes last, and every view id is registered once.
    #[test]
    fn script_bundles() {
        for (name, text) in SCRIPTS {
            let lower = text.to_ascii_lowercase();
            assert!(!lower.contains("</script"), "{name} contains </script");
            assert!(!lower.contains("<!--"), "{name} contains <!--");
            for p in [
                "__TITLE__",
                "__DB_URLS__",
                "__DB_META__",
                "__SOURCE_META__",
                "__PROJECT_META__",
                "__EXPLORE_SHELL_STYLE__",
                "__EXPLORE_SCRIPT__",
            ] {
                assert!(!text.contains(p), "{name} contains {p}");
            }
        }
        assert_eq!(SCRIPTS.last().map(|s| s.0), Some("main.js"));
        let all = script();
        let mut ids: Vec<&str> = all
            .match_indices("registerView({ id: \"")
            .map(|(i, m)| {
                let rest = &all[i + m.len()..];
                &rest[..rest.find('"').expect("id ends")]
            })
            .collect();
        let n = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), n, "a view id is registered twice");
        assert!(ids.contains(&"summary"), "the default view");
        let p = page("t", &["project.sqlite".into()], None, None, None);
        assert!(p.contains("// ===== explore/main.js ====="));
        assert!(!p.contains("__EXPLORE_SCRIPT__"));
    }

    /// The service worker and the VFS use the same strong validator and cache tag.
    #[test]
    fn one_version_contract() {
        let def = |text: &str, name: &str| {
            let start = text.find(&format!("function {name}(")).expect("function");
            text[start..start + text[start..].find("\n}").expect("end")].to_string()
        };
        let transport = include_str!("explore/vfs-transport.js");
        for name in ["strongETag", "versionOf"] {
            assert_eq!(def(transport, name), def(SERVICE_WORKER, name));
        }
    }

    #[test]
    fn source_meta() {
        assert!(source_repo_ok("https://github.com/hiloopai/silmaril-lean"));
        for bad in [
            "http://github.com/a/b",
            "https://github.com/a",
            "https://github.com/a/b/c",
            "https://github.com/../b",
            "https://github.com/a/b\"",
            "https://example.com/a/b",
        ] {
            assert!(!source_repo_ok(bad), "{bad}");
        }
        assert!(source_rev_ok("dc6b6e6a"));
        assert!(!source_rev_ok("main") && !source_rev_ok("abc"));
        let s = SourceMeta {
            repo: "https://github.com/a/b".into(),
            rev: "0123456789abcdef".into(),
            modules: [("M.N".to_string(), "x/</script>.lean".to_string())].into(),
        };
        let p = page("t", &[], None, Some(&s), None);
        assert!(p.contains(r#""rev":"0123456789abcdef""#));
        assert!(!p.contains("x/</script>") && !p.contains("__SOURCE_META__"));
    }

    #[test]
    fn page_escapes_title_and_urls() {
        let p = page(
            "a<b",
            &["../x/</script>.sqlite".into(), "project.sqlite".into()],
            Some(&DbMeta {
                size: 3,
                sha256: "ab".into(),
            }),
            None,
            None,
        );
        assert!(p.contains(r#""size":3"#));
        assert!(p.contains("<title>a&lt;b</title>"));
        assert!(!p.contains("x/</script>"));
        assert!(p.contains(r#"["../x/\u003c/script\u003e.sqlite","project.sqlite"]"#));
        assert!(
            !p.contains("__DB_URLS__")
                && !p.contains("__TITLE__")
                && !p.contains("__PROJECT_META__")
        );
    }

    #[test]
    fn package_project_docs_copies_markdown_and_blocks_escapes() {
        let proj = tempfile::tempdir().unwrap();
        let out = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(proj.path().join("docs/projects/rvsdg")).unwrap();
        std::fs::write(
            proj.path().join("docs/projects/README.md"),
            "# Index\n[RVSDG](rvsdg/overview.md)\n[Root](../../README.md)\n[Escape](../../../secret.md)\n",
        )
        .unwrap();
        std::fs::write(
            proj.path().join("docs/projects/rvsdg/overview.md"),
            "# RVSDG\n",
        )
        .unwrap();
        std::fs::write(
            proj.path().join("docs/projects/arch.png"),
            b"\x89PNG\r\n\x1a\n",
        )
        .unwrap();
        std::fs::write(
            proj.path().join("docs/projects/raw.svg"),
            "<svg xmlns=\"http://www.w3.org/2000/svg\"></svg>",
        )
        .unwrap();
        std::fs::write(proj.path().join("README.md"), "# Repo root\n").unwrap();
        std::fs::write(proj.path().join("docs/help.md"), "# Custom help\n").unwrap();
        std::fs::write(proj.path().join("docs/.hidden.md"), "# Hidden\n").unwrap();

        let (idx, help, dirs) =
            package_project_docs(proj.path(), out.path(), Some("docs/help.md")).unwrap();
        assert_eq!(idx.as_deref(), Some("projects/README.md"));
        assert_eq!(help.as_deref(), Some("help.md"));
        assert_eq!(dirs, vec!["projects".to_string()]);
        assert!(out.path().join("_docs/projects/README.md").is_file());
        assert!(
            out.path()
                .join("_docs/projects/rvsdg/overview.md")
                .is_file()
        );
        assert!(out.path().join("_docs/projects/arch.png").is_file());
        assert!(
            !out.path().join("_docs/projects/raw.svg").exists(),
            "raw SVG must not be packaged as a standalone document"
        );
        assert!(
            !out.path().join("_docs/.hidden.md").exists(),
            "hidden files must not be packaged"
        );
        assert!(
            !out.path().join("_docs/_repo").exists(),
            "files outside docs/ must not be crawled into _docs/"
        );
        assert!(out.path().join("_docs/help.md").is_file());

        // Stale files in _docs/ are removed on the next run, while source docs/ is untouched when
        // out_dir is the project root itself.
        std::fs::write(out.path().join("_docs/projects/stale.md"), "# Stale\n").unwrap();
        let (_, _, _) = package_project_docs(proj.path(), out.path(), None).unwrap();
        assert!(!out.path().join("_docs/projects/stale.md").exists());

        // Root output (`--out explore.html` inside `proj`) isolates `_docs/` from `docs/`.
        let (root_idx, _, _) = package_project_docs(proj.path(), proj.path(), None).unwrap();
        assert_eq!(root_idx.as_deref(), Some("projects/README.md"));
        assert!(proj.path().join("docs/projects/README.md").is_file());
        assert!(proj.path().join("_docs/projects/README.md").is_file());

        // Symlinked output files and symlinked directories are refused.
        let target = proj.path().join("victim.txt");
        std::fs::write(&target, "keep").unwrap();
        let sym_out = out.path().join("sym-explore.html");
        std::os::unix::fs::symlink(&target, &sym_out).unwrap();
        assert!(
            write_regular_file_bounded(out.path(), &sym_out, b"overwrite").is_err(),
            "symlinked --out must be refused"
        );
        assert_eq!(std::fs::read_to_string(&target).unwrap(), "keep");
    }
}
