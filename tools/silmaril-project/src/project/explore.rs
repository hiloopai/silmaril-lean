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
    script!("ui.js"),
    script!("lean/tokenize.js"),
    script!("lean/locate.js"),
    script!("lean/render.js"),
    script!("provenance.js"),
    script!("table.js"),
    script!("vfs-transport.js"),
    script!("vfs.js"),
    script!("db.js"),
    script!("router.js"),
    script!("graphs.js"),
    script!("views/summary.js"),
    script!("views/progress.js"),
    script!("views/corpus.js"),
    script!("views/compiler.js"),
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
    script!("views/sql.js"),
    script!("views/source.js"),
    script!("main.js"),
];

/// The bundled script: every file of [`SCRIPTS`], each after a comment naming it.
fn script() -> String {
    let mut out = String::new();
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
/// lets the page link declarations to their Lean sources.
pub fn page(
    title: &str,
    db_urls: &[String],
    meta: Option<&DbMeta>,
    source: Option<&SourceMeta>,
) -> String {
    let source = source.map_or(
        serde_json::Value::Null,
        |s| serde_json::json!({ "repo": s.repo, "rev": s.rev, "modules": s.modules }),
    );
    let meta = meta.map_or(
        serde_json::Value::Null,
        |m| serde_json::json!({ "url": db_urls.first(), "size": m.size, "sha256": m.sha256 }),
    );
    // The script goes in last, so that no placeholder text inside it is replaced.
    TEMPLATE
        .replace("__TITLE__", &html_escape(title))
        .replace("__DB_URLS__", &script_json(&serde_json::json!(db_urls)))
        .replace("__DB_META__", &script_json(&meta))
        .replace("__SOURCE_META__", &script_json(&source))
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
        let p = page("t", &["project.sqlite".into()], None, None);
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
        let p = page("t", &[], None, Some(&s));
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
        );
        assert!(p.contains(r#""size":3"#));
        assert!(p.contains("<title>a&lt;b</title>"));
        assert!(!p.contains("x/</script>"));
        assert!(p.contains(r#"["../x/\u003c/script\u003e.sqlite","project.sqlite"]"#));
        assert!(!p.contains("__DB_URLS__") && !p.contains("__TITLE__"));
    }
}
