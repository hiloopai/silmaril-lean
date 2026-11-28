//! Golden tests for `sil project`.
//!
//! Each directory under `tests/project/` is a case: a project directory with a hand-written
//! `dump.json` and optional `silmaril.toml`, `silmaril/artifacts.toml`, `lakefile.toml`,
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
        let out = Command::new(env!("CARGO_BIN_EXE_silmaril-project"))
            .args(["sqlite", "--dump", "dump.json", "--sql"])
            .arg(&sql)
            .arg("--db")
            .arg(tmp.path().join("project.sqlite"))
            .current_dir(&dir)
            .output()
            .unwrap();
        let stdout = String::from_utf8(out.stdout).unwrap();
        let text = format!(
            "{stdout}exit: {}\n",
            if out.status.success() { "ok" } else { "failed" }
        );
        compare(&case.join("check.txt"), &text, bless, &mut failures);
        let expected_sql = case.join("project.sql");
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

#[test]
fn ir_registry_exports_models_and_checks_references() {
    use serde_json::json;

    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    fs::write(dir.join("lakefile.toml"), "name = \"ir_demo\"\n").unwrap();
    let (ok, output) = sil(dir, &["init"]);
    assert!(ok, "{output}");

    let dependency = dir.join("dependency");
    fs::create_dir(&dependency).unwrap();
    fs::write(
        dependency.join("lakefile.toml"),
        "name = \"dependency\"\n[[lean_lib]]\nname = \"Imported\"\n",
    )
    .unwrap();
    let (ok, output) = sil(&dependency, &["init"]);
    assert!(ok, "{output}");
    fs::write(
        dir.join("lake-manifest.json"),
        r#"{"packages":[{"name":"dependency","type":"path","dir":"dependency"}]}"#,
    )
    .unwrap();

    let records = vec![
        json!({"kind": "ir_family", "name": "demo.family", "title": "Family", "module": "Demo"}),
        json!({"kind": "ir_syntax_kind", "name": "demo.extension", "title": "New kind", "module": "Imported"}),
        json!({"kind": "ir_subset", "name": "demo.subset", "title": "Subset", "module": "Demo",
               "family": "demo.family", "syntax_kind": "demo.extension", "decl": "Demo.Program"}),
        json!({"kind": "ir_model", "name": "demo.eval", "title": "Evaluator", "module": "Demo",
               "subset": "demo.subset", "semantics": "operational", "decl": "Demo.eval"}),
        json!({"kind": "ir_model", "name": "demo.denote", "title": "Denotation", "module": "Demo",
               "subset": "demo.subset", "semantics": "denotational", "decl": "Demo.denote",
               "institution": "demo.logic"}),
        json!({"kind": "institution", "name": "demo.logic", "module": "Imported",
               "decl": "Imported.logic", "arity": 0, "type": "Inst", "levels": ""}),
    ];
    let write_dump = |records| {
        let dump = json!({
            "schema": "silmaril.project-dump.v0.2",
            "toolchain": "4.37.0",
            "modules": ["Demo"],
            "records": records,
            "problems": [], "solutions": []
        });
        fs::write(dir.join("dump.json"), dump.to_string()).unwrap();
    };
    write_dump(records.clone());
    let (ok, output) = sil(
        dir,
        &["sqlite", "--dump", "dump.json", "--db", "project.sqlite"],
    );
    assert!(ok, "{output}");

    let db = rusqlite::Connection::open(dir.join("project.sqlite")).unwrap();
    let scalar = |sql| db.query_row(sql, [], |row| row.get::<_, i64>(0)).unwrap();
    assert_eq!(
        scalar(
            "SELECT count(DISTINCT sid) FROM objects
             WHERE kind IN ('ir_family', 'ir_syntax_kind', 'ir_subset', 'ir_model')"
        ),
        5
    );
    assert_eq!(
        scalar(
            "SELECT count(*) FROM ir_models m
             JOIN ir_subsets s ON m.subset = s.name
             JOIN ir_families f ON s.family = f.name
             JOIN ir_syntax_kinds k ON s.syntax_kind = k.name
             JOIN logic_nodes n ON m.institution = n.name AND n.kind = 'institution'
             JOIN institutions i ON i.name = n.name
             WHERE f.name = 'demo.family' AND k.name = 'demo.extension'
               AND s.name = 'demo.subset' AND m.name = 'demo.denote'
               AND m.semantics = 'denotational' AND n.name = 'demo.logic'
               AND k.origin = 'imported' AND i.origin = 'imported'"
        ),
        1
    );
    assert_eq!(
        scalar(
            "SELECT count(*) FROM ir_models
             WHERE name = 'demo.eval' AND semantics = 'operational' AND institution IS NULL"
        ),
        1
    );

    for (record, field, value, diagnostic) in [
        (
            2,
            "family",
            "missing.family",
            "family: no ir_family missing.family",
        ),
        (
            2,
            "syntax_kind",
            "missing.kind",
            "syntax_kind: no ir_syntax_kind missing.kind",
        ),
        (
            4,
            "subset",
            "missing.subset",
            "subset: no ir_subset missing.subset",
        ),
        (
            4,
            "institution",
            "demo.family",
            "institution: no institution demo.family",
        ),
        (4, "semantics", "unknown", "unknown variant"),
    ] {
        let mut invalid = records.clone();
        invalid[record][field] = json!(value);
        write_dump(invalid);
        let (ok, output) = sil(dir, &["check", "--dump", "dump.json"]);
        assert!(!ok && output.contains(diagnostic), "{output}");
    }
    let mut duplicate = records.clone();
    duplicate.push(records[3].clone());
    write_dump(duplicate);
    let (ok, output) = sil(dir, &["check", "--dump", "dump.json"]);
    assert!(
        !ok && output.contains("ir_model demo.eval: declared twice"),
        "{output}"
    );

    let mut reused_sid = records;
    let sid = "a".repeat(64);
    reused_sid[3]["sid"] = json!(sid);
    reused_sid[4]["sid"] = json!(sid);
    write_dump(reused_sid);
    let (ok, output) = sil(dir, &["check", "--dump", "dump.json"]);
    assert!(
        !ok && output.contains("shared by ir_model demo.eval and ir_model demo.denote"),
        "{output}"
    );
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

/// The marking queries over the `markings` case's database, against `markings/queries.txt`.
#[test]
fn marking_queries() {
    let bless = std::env::var_os("SIL_BLESS").is_some();
    let case = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/project/markings");
    let tmp = tempfile::tempdir().unwrap();
    let db = tmp.path().join("project.sqlite");
    let db_arg = db.to_str().unwrap();
    let (ok, out) = sil(
        &case,
        &[
            "sqlite",
            "--dump",
            "dump.json",
            "--sql",
            tmp.path().join("project.sql").to_str().unwrap(),
            "--db",
            db_arg,
        ],
    );
    assert!(ok, "{out}");
    let mut text = String::new();
    for args in [
        &["findings"][..],
        &["findings", "--class", "spec_bug"],
        &["findings", "--class", "unclassified"],
        &["errors"],
        &["gaps"],
        &["deprecated"],
        &["deprecated", "--problems"],
    ] {
        let mut a = args.to_vec();
        a.extend(["--db", db_arg]);
        let (ok, out) = sil(&case, &a);
        assert!(ok, "{args:?}: {out}");
        text += &format!("$ sil project {}\n{out}", args.join(" "));
    }
    let mut failures = Vec::new();
    compare(&case.join("queries.txt"), &text, bless, &mut failures);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // a database without the marking tables is reported, not misread
    let (ok, out) = sil(&case, &["errors", "--db", "no-such.sqlite"]);
    assert!(
        !ok && out.contains("run `sil project sqlite` first"),
        "{out}"
    );
}

#[test]
fn explore_root_output_isolates_docs_and_refuses_symlinks() {
    let tmp = tempfile::tempdir().unwrap();
    let d = tmp.path();
    fs::write(d.join("lakefile.toml"), "name = \"root_out\"\n").unwrap();
    assert!(sil(d, &["init"]).0);
    fs::create_dir_all(d.join("docs/projects/sub")).unwrap();
    fs::write(
        d.join("docs/projects/README.md"),
        "# Root docs\n[Sub](sub/guide.md)\n[Root README](../../README.md)\n",
    )
    .unwrap();
    fs::write(d.join("docs/projects/sub/guide.md"), "# Sub guide\n").unwrap();
    fs::write(d.join("docs/projects/diagram.png"), b"\x89PNG\r\n\x1a\n").unwrap();
    fs::write(d.join("docs/projects/raw.svg"), "<svg></svg>").unwrap();
    fs::write(d.join("docs/.draft.md"), "# Draft\n").unwrap();
    fs::write(d.join("README.md"), "# Repo README\n").unwrap();

    // Symlinked directory inside docs/ must not be followed
    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("secret.md"), "# Secret\n").unwrap();
    std::os::unix::fs::symlink(outside.path(), d.join("docs/projects/escaped_dir")).unwrap();

    // Normal root CLI output: `sil project explore --out explore.html` inside the project root
    let (ok, out) = sil(d, &["explore", "--out", "explore.html"]);
    assert!(ok, "{out}");
    assert!(d.join("explore.html").is_file());
    assert!(d.join("explore-sw.js").is_file());
    assert!(d.join("explore-mermaid.js").is_file());
    // Source docs/ is preserved intact and staged docs live under _docs/
    assert_eq!(
        fs::read_to_string(d.join("docs/projects/README.md")).unwrap(),
        "# Root docs\n[Sub](sub/guide.md)\n[Root README](../../README.md)\n"
    );
    assert!(d.join("_docs/projects/README.md").is_file());
    assert!(d.join("_docs/projects/sub/guide.md").is_file());
    assert!(d.join("_docs/projects/diagram.png").is_file());
    assert!(!d.join("_docs/projects/raw.svg").exists());
    assert!(!d.join("_docs/.draft.md").exists());
    assert!(!d.join("_docs/projects/escaped_dir").exists());
    assert!(!d.join("_docs/_repo").exists());

    // Symlinked --out target is refused and its target is not modified
    let victim = d.join("victim.txt");
    fs::write(&victim, "untouched").unwrap();
    std::os::unix::fs::symlink(&victim, d.join("symlink-out.html")).unwrap();
    let (ok_sym, out_sym) = sil(d, &["explore", "--out", "symlink-out.html"]);
    assert!(!ok_sym, "expected symlinked --out to fail: {out_sym}");
    assert_eq!(fs::read_to_string(&victim).unwrap(), "untouched");
}
