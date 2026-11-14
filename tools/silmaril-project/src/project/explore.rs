//! `sil project explore`: one static HTML page over the project database.
//!
//! The page (`explore.html`, next to this file) holds no data: it opens a separate SQLite file
//! in the browser, with pinned scripts from cdnjs/jsdelivr. Over http(s) it tries `?db=<url>`,
//! then the `db_urls` written here (relative to the page). It reads the file lazily with
//! sql.js-httpvfs (HTTP Range requests, one SQLite page at a time) when the server supports
//! Range, and downloads it whole into sql.js otherwise. Over `file://`, where browsers block
//! `fetch`, the file is chosen with a file picker or dropped onto the page.

use std::path::{Component, Path};

const TEMPLATE: &str = include_str!("explore.html");

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

/// The page titled `title`, which tries `db_urls` (relative to the page) in order; `meta`
/// describes the first of them, when it was readable at generation time.
pub fn page(title: &str, db_urls: &[String], meta: Option<&DbMeta>) -> String {
    let meta = meta.map_or(
        serde_json::Value::Null,
        |m| serde_json::json!({ "url": db_urls.first(), "size": m.size, "sha256": m.sha256 }),
    );
    TEMPLATE
        .replace("__TITLE__", &html_escape(title))
        .replace("__DB_URLS__", &script_json(&serde_json::json!(db_urls)))
        .replace("__DB_META__", &script_json(&meta))
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
        let start = TEMPLATE.find("const TABLE_DOCS = {").expect("TABLE_DOCS");
        let docs = &TEMPLATE[start..start + TEMPLATE[start..].find("\n};").expect("end")];
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

    #[test]
    fn page_escapes_title_and_urls() {
        let p = page(
            "a<b",
            &["../x/</script>.sqlite".into(), "project.sqlite".into()],
            Some(&DbMeta {
                size: 3,
                sha256: "ab".into(),
            }),
        );
        assert!(p.contains(r#""size":3"#));
        assert!(p.contains("<title>a&lt;b</title>"));
        assert!(!p.contains("x/</script>"));
        assert!(p.contains(r#"["../x/\u003c/script\u003e.sqlite","project.sqlite"]"#));
        assert!(!p.contains("__DB_URLS__") && !p.contains("__TITLE__"));
    }
}
