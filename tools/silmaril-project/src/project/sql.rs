//! The canonical SQL text of a project database and loading it with `rusqlite`.
//!
//! The text is the reviewable artifact: a version line, the DDL in [`schema::tables`] order,
//! the views, then one `INSERT` per row with rows sorted by primary key. No timestamps, host
//! names or absolute paths. The `.sqlite` file is built by executing that text; reading the
//! database back with [`logical_dump`] must give the same text, which `write_db` checks.

use super::schema::{self, DB_SCHEMA, Database, Sql, TableInfo, column};
use miette::{IntoDiagnostic, Result, WrapErr, bail};
use std::{fs, path::Path};

pub fn literal(v: &Sql) -> String {
    match v {
        Sql::Null => "NULL".into(),
        Sql::Int(i) => i.to_string(),
        Sql::Text(s) => format!("'{}'", s.replace('\'', "''")),
    }
}

pub fn ddl(t: &TableInfo) -> String {
    let mut cols: Vec<String> = t
        .columns
        .iter()
        .map(|(c, ty)| {
            let c = column(c);
            if t.key == [c] {
                format!("{c} {ty} PRIMARY KEY")
            } else {
                format!("{c} {ty}")
            }
        })
        .collect();
    if t.key.len() > 1 {
        cols.push(format!("PRIMARY KEY({})", t.key.join(", ")));
    }
    if !t.unique.is_empty() {
        cols.push(format!("UNIQUE({})", t.unique.join(", ")));
    }
    format!("CREATE TABLE {}(\n  {}\n);", t.name, cols.join(",\n  "))
}

fn key_positions(t: &TableInfo) -> Vec<usize> {
    t.key
        .iter()
        .map(|k| {
            t.columns
                .iter()
                .position(|(c, _)| column(c) == *k)
                .expect("key is a column")
        })
        .collect()
}

fn render(tables: &[(TableInfo, Vec<Vec<Sql>>)]) -> String {
    let mut out = format!("-- {DB_SCHEMA}\n");
    for (t, _) in tables {
        out += &ddl(t);
        out.push('\n');
    }
    for v in schema::VIEWS {
        out += v;
        out.push('\n');
    }
    for (name, table, cols) in schema::INDEXES {
        out += &format!("CREATE INDEX {name} ON {table}({});\n", cols.join(", "));
    }
    for (t, rows) in tables {
        let cols: Vec<&str> = t.columns.iter().map(|(c, _)| column(c)).collect();
        for row in rows {
            let vals: Vec<String> = row.iter().map(literal).collect();
            out += &format!(
                "INSERT INTO {}({}) VALUES({});\n",
                t.name,
                cols.join(", "),
                vals.join(", ")
            );
        }
    }
    out
}

/// The canonical SQL text: rows sorted by primary key. Duplicate keys are a bug in `check`.
pub fn text(db: &Database) -> Result<String> {
    let expected: Vec<&str> = schema::tables().iter().map(|t| t.name).collect();
    let got: Vec<&str> = db.tables.iter().map(|(t, _)| t.name).collect();
    if expected != got {
        bail!("internal: table order {got:?} is not {expected:?}");
    }
    let mut tables = db.tables.clone();
    for (t, rows) in &mut tables {
        let key = key_positions(t);
        let k = |r: &Vec<Sql>| key.iter().map(|&i| r[i].clone()).collect::<Vec<_>>();
        rows.sort_by_key(&k);
        if let Some(w) = rows.windows(2).find(|w| k(&w[0]) == k(&w[1])) {
            bail!("internal: duplicate key {:?} in table {}", k(&w[0]), t.name);
        }
    }
    Ok(render(&tables))
}

/// Read every table back in primary-key order and render it as [`text`] would.
pub fn logical_dump(conn: &rusqlite::Connection) -> Result<String> {
    let mut tables = Vec::new();
    for t in schema::tables() {
        let cols: Vec<&str> = t.columns.iter().map(|(c, _)| column(c)).collect();
        let q = format!(
            "SELECT {} FROM {} ORDER BY {}",
            cols.join(", "),
            t.name,
            t.key.join(", ")
        );
        let mut stmt = conn.prepare(&q).into_diagnostic()?;
        let rows = stmt
            .query_map([], |r| {
                (0..cols.len())
                    .map(|i| {
                        Ok(match r.get_ref(i)? {
                            rusqlite::types::ValueRef::Null => Sql::Null,
                            rusqlite::types::ValueRef::Integer(n) => Sql::Int(n),
                            v => Sql::Text(v.as_str()?.to_string()),
                        })
                    })
                    .collect::<rusqlite::Result<Vec<Sql>>>()
            })
            .into_diagnostic()?
            .collect::<rusqlite::Result<Vec<_>>>()
            .into_diagnostic()?;
        tables.push((t, rows));
    }
    Ok(render(&tables))
}

/// Build `db` from the SQL text (replacing any old file), `VACUUM` it, and check that its
/// logical dump is the text and that it has exactly the indexes of [`schema::INDEXES`]. With
/// `httpvfs = Some(page_size)`, also set the page size (one HTTP Range request reads at least a
/// page) and `journal_mode = DELETE`, for lazy reads; the content is the same.
pub fn write_db(sql: &str, db: &Path, httpvfs: Option<u32>) -> Result<()> {
    if let Some(dir) = db.parent() {
        fs::create_dir_all(dir).into_diagnostic()?;
    }
    if db.exists() {
        fs::remove_file(db).into_diagnostic()?;
    }
    let conn = rusqlite::Connection::open(db)
        .into_diagnostic()
        .wrap_err_with(|| format!("could not create {}", db.display()))?;
    let mut tail = String::new();
    if let Some(page_size) = httpvfs {
        if !(512..=65536).contains(&page_size) || !page_size.is_power_of_two() {
            bail!("the page size must be a power of two from 512 to 65536, not {page_size}");
        }
        tail += &format!("PRAGMA journal_mode = DELETE;\nPRAGMA page_size = {page_size};\n");
    }
    conn.execute_batch(&format!("BEGIN;\n{sql}COMMIT;\n{tail}VACUUM;"))
        .into_diagnostic()
        .wrap_err("could not load the SQL text")?;
    let back = logical_dump(&conn)?;
    if back != sql {
        bail!("internal: the database's logical dump differs from the SQL text");
    }
    let mut stmt = conn
        .prepare(
            "SELECT name FROM sqlite_master WHERE type = 'index' AND sql IS NOT NULL ORDER BY name",
        )
        .into_diagnostic()?;
    let got = stmt
        .query_map([], |r| r.get::<_, String>(0))
        .into_diagnostic()?
        .collect::<rusqlite::Result<Vec<_>>>()
        .into_diagnostic()?;
    let mut want: Vec<&str> = schema::INDEXES.iter().map(|(n, _, _)| *n).collect();
    want.sort_unstable();
    if got != want {
        bail!("internal: the database's indexes {got:?} are not {want:?}");
    }
    Ok(())
}
