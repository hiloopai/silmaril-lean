//! `sil project findings | errors | gaps | deprecated`: the markings of a project database
//! (`sil project sqlite`), one tab-separated row per line, `-` for an empty field. Each command
//! is one query over the marking views ([`super::schema::markings::MARKING_VIEWS`]); the guide
//! lists them, so the same answers are one `sqlite3` call away.

use miette::{IntoDiagnostic, Result, WrapErr, bail};
use std::path::Path;

/// What to list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Query<'a> {
    /// Every finding, or those of one classification; `unclassified` lists the failing problems
    /// that are neither deprecated nor classified.
    Findings(Option<&'a str>),
    /// The genuine errors (`error` findings), with versions and disclosure.
    Errors,
    /// The model gaps, one line per missing instruction or feature.
    Gaps,
    /// The deprecations with their replacements; with `true`, every deprecated problem and why.
    Deprecated(bool),
}

/// The header and the SQL of a query.
pub fn sql(q: Query) -> (&'static str, String) {
    match q {
        Query::Findings(Some("unclassified")) => (
            "problem\tsummary",
            "SELECT problem, summary FROM unclassified_failures ORDER BY problem".into(),
        ),
        Query::Findings(class) => (
            "classification\tproblem\tsummary\tpointer\tnote",
            format!(
                "SELECT f.classification, f.problem, s.summary, f.pointer, f.note FROM findings f \
                 LEFT JOIN summary s ON s.problem = f.problem{} ORDER BY CASE f.classification \
                 WHEN 'error' THEN 0 WHEN 'spec_bug' THEN 1 WHEN 'model_gap' THEN 2 ELSE 3 END, \
                 f.pointer, f.problem",
                class.map_or(String::new(), |c| format!(
                    " WHERE f.classification = '{}'",
                    c.replace('\'', "''")
                ))
            ),
        ),
        Query::Errors => (
            "problem\tsummary\taffected_versions\tfixed_in\tdisclosure_status\tpointer\tnote",
            "SELECT problem, summary, affected_versions, fixed_in, disclosure_status, pointer, \
             note FROM genuine_errors ORDER BY problem"
                .into(),
        ),
        Query::Gaps => (
            "pointer\tproblems\tnames",
            "SELECT pointer, count(*), group_concat(problem, ',') FROM \
             (SELECT pointer, problem FROM model_gaps ORDER BY pointer, problem) \
             GROUP BY pointer ORDER BY count(*) DESC, pointer"
                .into(),
        ),
        Query::Deprecated(false) => (
            "kind\tname\tsuperseded_by\treason",
            "SELECT kind, name, superseded_by, reason FROM deprecated_with_replacements \
             ORDER BY kind, name"
                .into(),
        ),
        Query::Deprecated(true) => (
            "problem\tvia_kind\tvia",
            "SELECT problem, via_kind, via FROM deprecated_problems ORDER BY problem".into(),
        ),
    }
}

/// Run a query over the database: the header line, then one line per row.
pub fn run(db: &Path, q: Query) -> Result<Vec<String>> {
    if !db.exists() {
        bail!(
            "{} does not exist; run `sil project sqlite` first",
            db.display()
        );
    }
    let conn =
        rusqlite::Connection::open_with_flags(db, rusqlite::OpenFlags::SQLITE_OPEN_READ_ONLY)
            .into_diagnostic()
            .wrap_err_with(|| format!("could not open {}", db.display()))?;
    let has_markings: bool = conn
        .query_row(
            "SELECT count(*) FROM sqlite_master WHERE type = 'view' AND name = 'genuine_errors'",
            [],
            |r| r.get::<_, i64>(0),
        )
        .into_diagnostic()?
        > 0;
    if !has_markings {
        bail!(
            "{} has no marking tables (an older `sil project`); run `sil project sqlite` again",
            db.display()
        );
    }
    let (header, text) = sql(q);
    let mut stmt = conn.prepare(&text).into_diagnostic()?;
    let n = stmt.column_count();
    let rows = stmt
        .query_map([], |r| {
            (0..n)
                .map(|i| {
                    Ok(match r.get_ref(i)? {
                        rusqlite::types::ValueRef::Null => "-".to_string(),
                        rusqlite::types::ValueRef::Integer(v) => v.to_string(),
                        v => v.as_str().unwrap_or_default().replace(['\t', '\n'], " "),
                    })
                })
                .collect::<rusqlite::Result<Vec<String>>>()
        })
        .into_diagnostic()?
        .collect::<rusqlite::Result<Vec<_>>>()
        .into_diagnostic()?;
    let mut out = vec![header.to_string()];
    out.extend(rows.into_iter().map(|r| r.join("\t")));
    Ok(out)
}
