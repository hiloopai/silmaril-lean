//! `check-sources`: the vendored `.spectec` sources, when present, against the manifest.

use crate::json;
use crate::sha256;

/// Line ranges of vendored sources emitted as Lean string literals: (Lean name, manifest
/// source path, first line, last line), 1-based and inclusive.
pub const RANGES: &[(&str, &str, usize, usize)] = &[
    (
        "wasm30_vars_line5",
        "specification/wasm-3.0/0.1-aux.vars.spectec",
        5,
        5,
    ),
    (
        "wasm30_vars_lines5_8",
        "specification/wasm-3.0/0.1-aux.vars.spectec",
        5,
        8,
    ),
    (
        "wasm30_binary_values_line31",
        "specification/wasm-3.0/5.1-binary.values.spectec",
        31,
        31,
    ),
    (
        "wasm30_binary_values_line49",
        "specification/wasm-3.0/5.1-binary.values.spectec",
        49,
        49,
    ),
    (
        "wasm30_binary_values_line63",
        "specification/wasm-3.0/5.1-binary.values.spectec",
        63,
        63,
    ),
];

/// The manifest's source SHA-256s, by source path.
pub fn manifest_sources(manifest: &json::Json) -> Result<Vec<(String, String)>, String> {
    let mut out = Vec::new();
    for s in manifest
        .get("specs")
        .and_then(json::Json::as_arr)
        .ok_or("manifest: no specs")?
    {
        for src in s
            .get("sources")
            .and_then(json::Json::as_arr)
            .ok_or("manifest: spec without sources")?
        {
            let path = src
                .get("path")
                .and_then(json::Json::as_str)
                .ok_or("source without path")?;
            let sha = src
                .get("sha256")
                .and_then(json::Json::as_str)
                .ok_or("source without sha256")?;
            out.push((path.to_string(), sha.to_string()));
        }
    }
    Ok(out)
}

/// The body of `Sources.lean`: one `def` per entry of `RANGES` whose source file is vendored
/// under `root` and matches the manifest.  `None` when no such file is vendored.
pub fn emit(root: &str, known: &[(String, String)]) -> Result<Option<String>, String> {
    let mut body = String::new();
    for (name, path, lo, hi) in RANGES {
        let local = format!("{root}/{path}");
        let Ok(bytes) = std::fs::read(&local) else {
            continue;
        };
        let sha = sha256::hex(&bytes);
        let want = known
            .iter()
            .find(|(p, _)| p == path)
            .map(|(_, s)| s.as_str())
            .ok_or(format!("{path} is not a manifest source"))?;
        if sha != want {
            return Err(format!("{local}: SHA-256 {sha}, manifest says {want}"));
        }
        let text = String::from_utf8(bytes).map_err(|e| format!("{local}: {e}"))?;
        let lines: Vec<&str> = text.split('\n').collect();
        if *hi > lines.len() || lo > hi || *lo == 0 {
            return Err(format!("{local}: no lines {lo}-{hi}"));
        }
        let slice = lines[lo - 1..*hi].join("\n");
        body.push_str(&format!(
            "/-- `{path}`, lines {lo}–{hi} (file SHA-256 `{sha}`), joined by newlines, no\n\
             trailing newline. -/\ndef {name} : String :=\n  {}\n\n",
            crate::emit::lean_str(&slice)
        ));
    }
    Ok((!body.is_empty()).then_some(body))
}

/// Verify every source file the manifest lists that is present under its source root
/// (`srcRoot`, by default `specs/spectec/src`), and every `references` entry, which must be present.
pub fn check(manifest_path: &str) -> Result<(), String> {
    let text = std::fs::read_to_string(manifest_path).map_err(|e| e.to_string())?;
    let manifest = json::parse(&text)?;
    let root = manifest
        .get("srcRoot")
        .and_then(json::Json::as_str)
        .unwrap_or("specs/spectec/src")
        .to_string();
    let mut refs = 0;
    for r in manifest
        .get("references")
        .and_then(json::Json::as_arr)
        .unwrap_or(&[])
    {
        let path = r
            .get("path")
            .and_then(json::Json::as_str)
            .ok_or("reference without path")?;
        let want = r
            .get("sha256")
            .and_then(json::Json::as_str)
            .ok_or("reference without sha256")?;
        let local = format!("{root}/{path}");
        let got = sha256::hex(&std::fs::read(&local).map_err(|e| format!("{local}: {e}"))?);
        if got != want {
            return Err(format!("{local}: SHA-256 {got}, manifest says {want}"));
        }
        refs += 1;
    }
    let mut present = 0;
    let mut listed = 0;
    for s in manifest
        .get("specs")
        .and_then(json::Json::as_arr)
        .ok_or("manifest: no specs")?
    {
        for src in s
            .get("sources")
            .and_then(json::Json::as_arr)
            .ok_or("manifest: spec without sources")?
        {
            listed += 1;
            let path = src
                .get("path")
                .and_then(json::Json::as_str)
                .ok_or("source without path")?;
            let want = src
                .get("sha256")
                .and_then(json::Json::as_str)
                .ok_or("source without sha256")?;
            let local = format!("{root}/{path}");
            match std::fs::read(&local) {
                Ok(bytes) => {
                    let got = sha256::hex(&bytes);
                    if got != want {
                        return Err(format!("{local}: SHA-256 {got}, manifest says {want}"));
                    }
                    present += 1;
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => return Err(format!("{local}: {e}")),
            }
        }
    }
    println!("{manifest_path}: {present} of {listed} sources vendored under {root}/; all match");
    if refs > 0 {
        println!("{manifest_path}: {refs} reference files under {root}/; all match");
    }
    Ok(())
}
