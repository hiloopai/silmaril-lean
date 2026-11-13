//! Golden tests for `sil project`.
//!
//! Each directory under `tests/project/` is a case: a project directory with a hand-written
//! `dump.json`, an optional `trust.json` (passed as `--trust`, with `--strict-trust` when a file
//! `strict-trust` exists) and optional `silmaril.toml`, `silmaril/artifacts.toml`, `lakefile.toml`,
//! `lake-manifest.json` and files. The test runs `sil project sqlite` and compares its stdout
//! with `check.txt` and, when the check passes, its SQL text with `project.sql`. `SIL_BLESS=1`
//! rewrites the expected files (`tests/project/regen.sh`); review is `git diff`. The end-to-end
//! run over a real Lean dump is `examples/project/selftest.sh`.

use std::{fs, path::Path, process::Command};

fn compare(path: &Path, got: &str, bless: bool, failures: &mut Vec<String>) {
    if bless {
        fs::write(path, got).unwrap();
        return;
    }
    let want = fs::read_to_string(path).unwrap_or_default();
    if want != got {
        failures.push(format!(
            "{} differs; run tests/project/regen.sh\n--- want\n{want}--- got\n{got}",
            path.display()
        ));
    }
}

/// The `trust_violations` view (a recursive query) finds exactly the violations `sil project`
/// reported as warnings, and the transitive views agree with the import edges.
fn check_trust_views(db: &Path, stdout: &str, failures: &mut Vec<String>) {
    let conn = rusqlite::Connection::open(db).unwrap();
    let mut stmt = conn
        .prepare(
            "SELECT DISTINCT module, via, decl, reason FROM trust_violations ORDER BY 1, 2, 3, 4",
        )
        .unwrap();
    let mut from_view: Vec<String> = stmt
        .query_map([], |r| {
            let (m, via, decl, why): (String, String, String, String) =
                (r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?);
            let route = if m == via {
                String::new()
            } else {
                format!(" (through {via})")
            };
            Ok(format!("trust {m}: {why}: {decl} uses{route}"))
        })
        .unwrap()
        .collect::<rusqlite::Result<_>>()
        .unwrap();
    from_view.sort();
    // The warning is `trust M: WHY: DECL uses GRANT[ (through VIA)]`; drop the grant.
    let mut from_tool: Vec<String> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("warning: "))
        .filter(|l| l.starts_with("trust "))
        .map(|l| {
            let (head, rest) = l.split_once(" uses ").unwrap();
            let route = rest.find(" (through ").map_or("", |i| &rest[i..]);
            format!("{head} uses{route}")
        })
        .collect();
    from_tool.sort();
    from_tool.dedup();
    if from_view != from_tool {
        failures.push(format!(
            "{}: trust_violations {from_view:?} != reported {from_tool:?}",
            db.display()
        ));
    }
    let closure: i64 = conn
        .query_row(
            "SELECT count(*) FROM trust_module_deps d WHERE NOT EXISTS (SELECT 1 FROM trust_imports i WHERE i.module = d.module AND i.import = d.dep) \
             AND NOT EXISTS (SELECT 1 FROM trust_module_deps e JOIN trust_imports i ON i.module = e.dep AND i.import = d.dep WHERE e.module = d.module)",
            [],
            |r| r.get(0),
        )
        .unwrap();
    if closure != 0 {
        failures.push(format!(
            "{}: trust_module_deps has {closure} rows not derived from imports",
            db.display()
        ));
    }
}

#[test]
fn golden_cases() {
    let bless = std::env::var_os("SIL_BLESS").is_some();
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/project");
    let mut cases: Vec<_> = fs::read_dir(&base)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.join("dump.json").is_file())
        .collect();
    cases.sort();
    assert!(
        cases.len() >= 8,
        "missing golden cases in {}",
        base.display()
    );
    let mut failures = Vec::new();
    for case in &cases {
        let dir = case.clone();
        let tmp = tempfile::tempdir().unwrap();
        let sql = tmp.path().join("project.sql");
        let trust = dir.join("trust.json").is_file();
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_silmaril-project"));
        cmd.args(["sqlite", "--dump", "dump.json", "--sql"])
            .arg(&sql)
            .arg("--db")
            .arg(tmp.path().join("project.sqlite"));
        if trust {
            cmd.args(["--trust", "trust.json"]);
        }
        if dir.join("strict-trust").is_file() {
            cmd.arg("--strict-trust");
        }
        let out = cmd.current_dir(&dir).output().unwrap();
        let stdout = String::from_utf8(out.stdout).unwrap();
        let text = format!(
            "{stdout}exit: {}\n",
            if out.status.success() { "ok" } else { "failed" }
        );
        compare(&case.join("check.txt"), &text, bless, &mut failures);
        let expected_sql = case.join("project.sql");
        if out.status.success() && trust {
            check_trust_views(&tmp.path().join("project.sqlite"), &stdout, &mut failures);
        }
        if out.status.success() {
            compare(
                &expected_sql,
                &fs::read_to_string(&sql).unwrap(),
                bless,
                &mut failures,
            );
        } else if expected_sql.exists() {
            if bless {
                fs::remove_file(&expected_sql).unwrap();
            } else {
                failures.push(format!(
                    "{} exists but the check failed",
                    expected_sql.display()
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn sil(dir: &Path, args: &[&str]) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_silmaril-project"))
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap()
    );
    (out.status.success(), text)
}

/// `init`, `artifacts add`, `lock`: the registry workflow.
#[test]
fn init_add_lock() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path();
    fs::write(d.join("lakefile.toml"), "name = \"w\"\n").unwrap();
    let (ok, out) = sil(d, &["init"]);
    assert!(ok, "{out}");
    let m = fs::read_to_string(d.join("silmaril.toml")).unwrap();
    assert!(
        m.starts_with("schema = \"silmaril.project.v0.1\"\nsid = \""),
        "{m}"
    );
    assert!(m.contains("name = \"w\""), "{m}");
    assert!(!sil(d, &["init"]).0, "init must not overwrite");

    fs::create_dir(d.join("data")).unwrap();
    fs::write(d.join("data/empty"), "").unwrap();
    let (ok, out) = sil(d, &["artifacts", "add", "data/empty", "--name", "w.empty"]);
    assert!(ok, "{out}");
    assert!(
        out.contains(
            "w.empty: (none) -> bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi"
        ),
        "{out}"
    );
    let reg = fs::read_to_string(d.join("silmaril/artifacts.toml")).unwrap();
    assert!(reg.contains("\n[[artifact]]\ncid = \"bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi\"\ntype = \"blob\"\nname = \"w.empty\"\npaths = [\"data/empty\"]\nsize = 0\nsha256 = \"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\"\ngit_sha1 = \"e69de29bb2d1d6434b8b29ae775ad8c2e48c5391\"\n"), "{reg}");
    assert!(
        !sil(d, &["artifacts", "add", "data/empty"]).0,
        "duplicate path"
    );

    // Unchanged files: lock is a no-op and prints no move.
    let (ok, out) = sil(d, &["lock"]);
    assert!(ok && !out.contains("->"), "{out}");
    assert_eq!(
        fs::read_to_string(d.join("silmaril/artifacts.toml")).unwrap(),
        reg
    );

    // A changed file is a new artifact: its name moves to the new CID.
    fs::write(d.join("data/empty"), "hello\n").unwrap();
    let (ok, out) = sil(d, &["lock"]);
    assert!(ok, "{out}");
    assert!(
        out.contains(
            "w.empty: bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi -> bafkr4i"
        ),
        "{out}"
    );
    let reg2 = fs::read_to_string(d.join("silmaril/artifacts.toml")).unwrap();
    assert!(
        reg2.contains(
            "sha256 = \"5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03\""
        ),
        "{reg2}"
    );

    // Missing files and escaping paths fail.
    assert!(
        sil(d, &["artifacts", "add", "data/nope"])
            .1
            .contains("does not exist")
    );
}

/// A failed `artifacts add` leaves the registry as it was (or absent): a missing file, an
/// absolute or escaping path, and a bad name are refused before anything is written.
#[test]
fn add_validates_before_writing() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path();
    fs::write(d.join("lakefile.toml"), "name = \"w\"\n").unwrap();
    assert!(sil(d, &["init"]).0);
    fs::create_dir(d.join("data")).unwrap();
    fs::write(d.join("data/a"), "a").unwrap();
    let abs = d.join("data/a").display().to_string();
    let reg = d.join("silmaril/artifacts.toml");
    let before = fs::read_to_string(&reg).ok();
    for (args, want) in [
        (vec!["data/nope.json"], "does not exist"),
        (vec![abs.as_str()], "relative to the package root"),
        (vec!["../a"], "relative to the package root"),
        (vec!["data/a", "--name", "Bad_Name"], "--name \"Bad_Name\""),
        (vec!["data/a", "--package", "nope"], "--package nope"),
    ] {
        let mut a = vec!["artifacts", "add"];
        a.extend(args.iter().copied());
        let (ok, out) = sil(d, &a);
        assert!(!ok && out.contains(want), "{args:?}: {out}");
        assert_eq!(
            fs::read_to_string(&reg).ok(),
            before,
            "{args:?} wrote the registry"
        );
    }
    let (ok, out) = sil(d, &["artifacts", "add", "data/a", "--name", "w.a"]);
    assert!(ok, "{out}");
    let after = fs::read_to_string(&reg).unwrap();
    assert!(!sil(d, &["artifacts", "add", "data/nope"]).0);
    assert_eq!(fs::read_to_string(&reg).unwrap(), after);
    assert!(sil(d, &["lock"]).0, "lock still works after a refused add");
}

/// `lint` refuses what is not a project, warns about an empty one, checks the registry and
/// references between records, and suggests names for typos.
#[test]
fn lint_checks_the_project() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path();
    let (ok, out) = sil(d, &["lint", "--dir", "/nonexistent/x"]);
    assert!(!ok && out.contains("no such directory"), "{out}");
    let (ok, out) = sil(d, &["lint"]);
    assert!(!ok && out.contains("no silmaril.toml"), "{out}");
    fs::write(d.join("lakefile.toml"), "name = \"w\"\n").unwrap();
    assert!(sil(d, &["init"]).0);
    let (ok, out) = sil(d, &["lint"]);
    assert!(ok && !out.contains("warning"), "{out}");
    fs::remove_file(d.join("silmaril/records.toml")).unwrap();
    let (ok, out) = sil(d, &["lint"]);
    assert!(ok && out.contains("warning: no records files"), "{out}");

    fs::write(
        d.join("W.lean"),
        "silmaril problem w.lean_problem about w.v : fun _ => True\n",
    )
    .unwrap();
    fs::write(
        d.join("silmaril/dag.toml"),
        "schema = \"silmaril.records.v0.2\"\nroot = \"w.all\"\n\n[[group]]\nname = \"w.all\"\n\
         children = [\"w.lean_problem\", \"w.v.parses\", \"w.nope\"]\n\n[[value]]\nname = \"w.v\"\n\
         format = \"json\"\nsource = \"data/a\"\n",
    )
    .unwrap();
    let (ok, out) = sil(d, &["lint"]);
    assert!(ok, "{out}");
    assert!(
        out.contains("silmaril/dag.toml:4: warning: group w.all: child w.nope is not declared"),
        "{out}"
    );
    assert!(
        !out.contains("w.lean_problem is") && !out.contains("w.v.parses is"),
        "{out}"
    );

    // the registry: stale digests are an error
    fs::create_dir(d.join("data")).unwrap();
    fs::write(d.join("data/a"), "{}").unwrap();
    assert!(sil(d, &["artifacts", "add", "data/a"]).0);
    let (ok, out) = sil(d, &["lint"]);
    assert!(
        ok && out.contains("silmaril/artifacts.toml: 1 artifact(s), locked"),
        "{out}"
    );
    fs::write(d.join("data/a"), "[]").unwrap();
    let (ok, out) = sil(d, &["lint"]);
    assert!(!ok && out.contains("run `sil project lock`"), "{out}");
    assert!(sil(d, &["lock"]).0);

    // typos
    fs::write(
        d.join("silmaril/typo.toml"),
        "schema = \"silmaril.records.v0.2\"\n[[grup]]\nname = \"w.g\"\n",
    )
    .unwrap();
    let (ok, out) = sil(d, &["lint"]);
    assert!(
        !ok && out.contains("`grup` (did you mean `group`?)"),
        "{out}"
    );
}

/// `lint` finds names declared in Lean under a library's `srcDir`.
#[test]
fn lint_reads_lean_under_src_dirs() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path();
    fs::write(
        d.join("lakefile.toml"),
        "name = \"w\"\n\n[[lean_lib]]\nname = \"W\"\nsrcDir = \"lean\"\n",
    )
    .unwrap();
    assert!(sil(d, &["init"]).0);
    fs::create_dir(d.join("lean")).unwrap();
    fs::write(
        d.join("lean/W.lean"),
        "@[problem \"w.p\"] def p : Prop := True\n",
    )
    .unwrap();
    fs::write(
        d.join("silmaril/dag.toml"),
        "schema = \"silmaril.records.v0.2\"\nroot = \"w.all\"\n\n[[group]]\nname = \"w.all\"\n\
         children = [\"w.p\", \"w.q\"]\n",
    )
    .unwrap();
    let (ok, out) = sil(d, &["lint"]);
    assert!(ok, "{out}");
    assert!(out.contains("child w.q is not declared"), "{out}");
    assert!(!out.contains("child w.p is"), "{out}");
}

/// `init` without a lakefile names the project after its directory, and scaffolds the
/// registry and a records file: `lock` and `lint` work right after it.
#[test]
fn init_scaffolds() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path().join("My Proj");
    fs::create_dir(&d).unwrap();
    let (ok, out) = sil(&d, &["init"]);
    assert!(ok, "{out}");
    assert!(out.contains("warning: no lakefile.toml"), "{out}");
    let m = fs::read_to_string(d.join("silmaril.toml")).unwrap();
    assert!(m.contains("name = \"My Proj\""), "{m}");
    assert!(out.contains("wrote silmaril/artifacts.toml"), "{out}");
    let rec = fs::read_to_string(d.join("silmaril/records.toml")).unwrap();
    assert!(rec.contains("# name = \"my_proj.hello\""), "{rec}");
    let (ok, out) = sil(&d, &["lock"]);
    assert!(ok && out.contains("(0 artifacts)"), "{out}");
    let (ok, out) = sil(&d, &["lint"]);
    assert!(ok && !out.contains("warning"), "{out}");
    // the commented examples are valid once uncommented
    let un: String = rec
        .lines()
        .map(|l| match l.strip_prefix("# ") {
            Some(x) if x.contains(" = ") || x.starts_with("[[") => x,
            _ => l,
        })
        .map(|l| format!("{l}\n"))
        .collect();
    fs::write(d.join("silmaril/records.toml"), un).unwrap();
    let (ok, out) = sil(&d, &["lint"]);
    assert!(ok && out.contains("2 table(s)"), "{out}");
}

/// Bad arguments fail before the check runs (no dump is needed to see them).
#[test]
fn arguments_are_checked_first() {
    let tmp = tempfile::tempdir().unwrap();
    let (ok, out) = sil(tmp.path(), &["sqlite", "--httpvfs", "--page-size", "1000"]);
    assert!(
        !ok && out.contains("a power of two from 512 to 65536"),
        "{out}"
    );
    assert!(!out.contains("dump"), "{out}");
}

#[test]
fn sql_text_is_stable_across_runs() {
    let case = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/project/ok");
    let run = || {
        let tmp = tempfile::tempdir().unwrap();
        let sql = tmp.path().join("p.sql");
        let st = Command::new(env!("CARGO_BIN_EXE_silmaril-project"))
            .args(["sqlite", "--dump", "dump.json", "--sql"])
            .arg(&sql)
            .arg("--db")
            .arg(tmp.path().join("p.sqlite"))
            .current_dir(&case)
            .output()
            .unwrap();
        assert!(st.status.success());
        fs::read(&sql).unwrap()
    };
    assert_eq!(run(), run());
}
