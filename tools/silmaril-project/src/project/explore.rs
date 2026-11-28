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
/// description (shown on the front page when the database row lacks one) and optional
/// project-specific help (inline text or a relative `.md` path packaged under `docs/`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProjectMeta {
    pub name: Option<String>,
    pub description: Option<String>,
    pub help: Option<String>,
    pub help_doc: Option<String>,
    pub docs_index: Option<String>,
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

/// Package the project's Markdown guides (`docs/` and any local `.md` files or doc assets they
/// link to inside the project directory) into `<out_dir>/docs/`, returning `(docs_index, help_doc)`
/// relative to `<out_dir>/docs/`.
///
/// Only constrained relative `.md` files and safe image assets (`.svg`, `.png`, `.jpg`, `.jpeg`,
/// `.gif`, `.webp`) inside `project_dir` are copied; symlinks, dotfiles, and other files are never
/// copied.
pub fn package_project_docs(
    project_dir: &Path,
    out_dir: &Path,
    extra_doc: Option<&str>,
) -> std::io::Result<(Option<String>, Option<String>)> {
    let Ok(canon_root) = std::fs::canonicalize(project_dir) else {
        return Ok((None, None));
    };
    let docs_root = project_dir.join("docs");
    let projects_readme = docs_root.join("projects/README.md");
    let docs_readme = docs_root.join("README.md");
    let mut seeds: Vec<std::path::PathBuf> = Vec::new();
    let index_rel = if projects_readme.is_file() {
        Some("projects/README.md".to_string())
    } else if docs_readme.is_file() {
        Some("README.md".to_string())
    } else {
        None
    };

    fn walk_md(dir: &Path, canon_root: &Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for e in rd.flatten() {
            let name = e.file_name();
            if name.to_string_lossy().starts_with('.') {
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
                walk_md(&p, canon_root, out);
            } else if meta.is_file()
                && p.extension().is_some_and(|x| x == "md")
                && std::fs::canonicalize(&p).is_ok_and(|c| c.starts_with(canon_root))
            {
                out.push(p);
            }
        }
    }

    if docs_root.is_dir() {
        walk_md(&docs_root, &canon_root, &mut seeds);
    }

    let mut help_doc_rel: Option<String> = None;
    if let Some(h) = extra_doc {
        let trimmed = h.trim();
        if trimmed.ends_with(".md")
            && !trimmed.contains("..")
            && !trimmed.starts_with('/')
            && !trimmed.contains('\\')
        {
            let candidate = project_dir.join(trimmed);
            if candidate.is_file()
                && std::fs::symlink_metadata(&candidate).is_ok_and(|m| !m.file_type().is_symlink())
                && std::fs::canonicalize(&candidate).is_ok_and(|c| c.starts_with(&canon_root))
            {
                seeds.push(candidate);
                let rel = if let Some(rest) = trimmed.strip_prefix("docs/") {
                    rest.to_string()
                } else {
                    format!("_repo/{trimmed}")
                };
                help_doc_rel = Some(rel);
            }
        }
    }

    if seeds.is_empty() {
        return Ok((None, None));
    }

    let allowed_ext = |p: &Path| {
        p.extension().and_then(|x| x.to_str()).is_some_and(|ext| {
            matches!(
                ext.to_ascii_lowercase().as_str(),
                "md" | "svg" | "png" | "jpg" | "jpeg" | "gif" | "webp"
            )
        })
    };

    let mut to_copy: std::collections::BTreeSet<std::path::PathBuf> = seeds.into_iter().collect();
    let mut queue: Vec<std::path::PathBuf> = to_copy.iter().cloned().collect();
    while let Some(file) = queue.pop() {
        if !file.extension().is_some_and(|x| x == "md") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&file) else {
            continue;
        };
        let Some(parent) = file.parent() else {
            continue;
        };
        for target in markdown_local_links(&text) {
            let Some(joined) = normalize_rel_path(parent, &target) else {
                continue;
            };
            if !joined.starts_with(project_dir) || !allowed_ext(&joined) {
                continue;
            }
            let Ok(meta) = std::fs::symlink_metadata(&joined) else {
                continue;
            };
            if meta.file_type().is_symlink() || !meta.is_file() {
                continue;
            }
            if std::fs::canonicalize(&joined).is_ok_and(|c| c.starts_with(&canon_root))
                && to_copy.insert(joined.clone())
            {
                queue.push(joined);
            }
        }
    }

    let out_docs = out_dir.join("docs");
    for src in &to_copy {
        let Ok(rel_to_proj) = src.strip_prefix(project_dir) else {
            continue;
        };
        let dst = if let Ok(under_docs) = rel_to_proj.strip_prefix("docs") {
            out_docs.join(under_docs)
        } else {
            out_docs.join("_repo").join(rel_to_proj)
        };
        if let Some(p) = dst.parent() {
            std::fs::create_dir_all(p)?;
        }
        std::fs::copy(src, dst)?;
    }

    Ok((index_rel, help_doc_rel))
}

fn markdown_local_links(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b']' && i + 1 < bytes.len() && bytes[i + 1] == b'(' {
            let start = i + 2;
            let mut end = start;
            while end < bytes.len() && bytes[end] != b')' && bytes[end] != b'\n' {
                end += 1;
            }
            if end < bytes.len() && bytes[end] == b')' {
                let raw = text[start..end].trim();
                let path = raw.split(['#', '?']).next().unwrap_or("").trim();
                if !path.is_empty()
                    && !path.starts_with("http://")
                    && !path.starts_with("https://")
                    && !path.starts_with("mailto:")
                    && !path.starts_with('/')
                {
                    out.push(path.to_string());
                }
                i = end + 1;
                continue;
            }
        }
        i += 1;
    }
    out
}

fn normalize_rel_path(base: &Path, rel: &str) -> Option<std::path::PathBuf> {
    let mut out = base.to_path_buf();
    for comp in Path::new(rel).components() {
        match comp {
            Component::CurDir => {}
            Component::ParentDir => {
                if !out.pop() {
                    return None;
                }
            }
            Component::Normal(s) => {
                if s.to_string_lossy().starts_with('.') {
                    return None;
                }
                out.push(s);
            }
            _ => return None,
        }
    }
    Some(out)
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
        std::fs::write(proj.path().join("README.md"), "# Repo root\n").unwrap();
        std::fs::write(proj.path().join("docs/help.md"), "# Custom help\n").unwrap();

        let (idx, help) =
            package_project_docs(proj.path(), out.path(), Some("docs/help.md")).unwrap();
        assert_eq!(idx.as_deref(), Some("projects/README.md"));
        assert_eq!(help.as_deref(), Some("help.md"));
        assert!(out.path().join("docs/projects/README.md").is_file());
        assert!(out.path().join("docs/projects/rvsdg/overview.md").is_file());
        assert!(out.path().join("docs/_repo/README.md").is_file());
        assert!(out.path().join("docs/help.md").is_file());
    }
}
