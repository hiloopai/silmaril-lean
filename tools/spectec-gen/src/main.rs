//! `spectec-gen`: emit the pinned SpecTec `--ast` streams, and the scripts their errata
//! produce, as explicit Lean `IL.Def` data under `Silmaril/Raw/Wasm/SpecTec/Scripts/`.
//!
//! Run from the repository root:
//!
//! * `generate` — write every output file;
//! * `check` — regenerate in memory and compare byte for byte (nonzero exit on a difference);
//! * `check-sources` — verify each vendored `specs/spectec/src/**` file present against the
//!   SHA-256 that `specs/spectec/manifest.json` records (passes when none are vendored);
//! * `errata-status` — classify every erratum against the later streams of `MAIN_MANIFEST`;
//! * `theory-diff [--list]` — compare scripts as theories of the SpecTec specification
//!   institution: versions, errata variants and later upstream revisions (`src/theory.rs`).
//! * `version …` — vendor, generate and report on a new `WebAssembly/spec` revision
//!   (`src/version.rs`).

mod emit;
mod errata;
mod json;
mod sexp;
mod sha256;
mod sources;
mod theory;
mod version;

use std::collections::BTreeMap;
use std::path::Path;
use std::process::ExitCode;

const GENERATOR: &str = concat!("spectec-gen ", env!("CARGO_PKG_VERSION"));
const MANIFEST: &str = "specs/spectec/manifest.json";
/// Further manifests, each pinning streams of a different source repository. Their streams get
/// an `Original` script only (no errata, no slices, no `Sources` excerpts).
const EXTRA_MANIFESTS: &[&str] = &[];
/// The streams of a later `WebAssembly/spec` main revision, vendored next to the pinned ones.
const MAIN_MANIFEST: &str = "specs/spectec/e7a9df7c/manifest.json";
/// The sub-namespace (and directory) of the scripts generated from `MAIN_MANIFEST`.
const MAIN_CHANNEL: &str = "Main";
/// The errata files and the stream module each one patches.
const ERRATA_FILES: &[(&str, &str)] = &[
    ("Binary51.lean", "Wasm30"),
    ("Text6x.lean", "Wasm30"),
    ("Wasm10.lean", "Wasm10"),
    ("Wasm20.lean", "Wasm20"),
];
const ERRATA_DIR: &str = "Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata";
const OUT_DIR: &str = "Silmaril/Raw/Wasm/SpecTec/Scripts";
const MODULE_ROOT: &str = "Silmaril.Raw.Wasm.SpecTec.Scripts";
const NAMESPACE_ROOT: &str = "Silmaril.Wasm.SpecTec.Scripts";
const REGEN: &str = "cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- generate";
/// Target size of one generated part file.
const PART_BYTES: usize = 150_000;
/// Column at which emitted terms are wrapped.
const WRAP: usize = 96;

/// One pinned stream.
struct Spec {
    /// `wasm-3.0`.
    name: String,
    /// `Wasm30`.
    module: String,
    path: String,
    sha256: String,
    definitions: usize,
    /// `WebAssembly/spec`, or the manifest's `repository`.
    repository: String,
    revision: String,
    defs: Vec<sexp::SExp>,
}

/// A corrected variant of a stream: a name and the errata files whose commands produce it.
struct Variant {
    spec: &'static str,
    name: &'static str,
    /// The directory of `errata_files`.
    errata_dir: &'static str,
    errata_files: &'static [&'static str],
    doc: &'static str,
}

const VARIANTS: &[Variant] = &[
    Variant {
        spec: "Wasm10",
        name: "Fixed",
        errata_dir: ERRATA_DIR,
        errata_files: &["Wasm10.lean"],
        doc: "The wasm-1.0 script with the errata of `Errata/Wasm10.lean`",
    },
    Variant {
        spec: "Wasm20",
        name: "Fixed",
        errata_dir: ERRATA_DIR,
        errata_files: &["Wasm20.lean"],
        doc: "The wasm-2.0 script with the errata of `Errata/Wasm20.lean`",
    },
    Variant {
        spec: "Wasm30",
        name: "Binary51",
        errata_dir: ERRATA_DIR,
        errata_files: &["Binary51.lean"],
        doc: "The wasm-3.0 script with the binary §5.1 errata of `Errata/Binary51.lean`",
    },
    Variant {
        spec: "Wasm30",
        name: "Text6x",
        errata_dir: ERRATA_DIR,
        errata_files: &["Text6x.lean"],
        doc: "The wasm-3.0 script with the text §6.x errata of `Errata/Text6x.lean`",
    },
    Variant {
        spec: "Wasm30",
        name: "Fixed",
        errata_dir: ERRATA_DIR,
        errata_files: &["Binary51.lean", "Text6x.lean"],
        doc: "The wasm-3.0 script with the errata of `Errata/Binary51.lean` then `Errata/Text6x.lean`",
    },
];

fn read(path: &str) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))
}

fn module_of(spec: &str) -> String {
    // "wasm-3.0" -> "Wasm30"
    let digits: String = spec.chars().filter(|c| c.is_ascii_digit()).collect();
    format!("Wasm{digits}")
}

fn load_specs() -> Result<Vec<Spec>, String> {
    load_specs_from(MANIFEST)
}

/// The streams of the extra manifests, in order.
fn load_extra_specs() -> Result<Vec<Spec>, String> {
    let mut out = Vec::new();
    for m in EXTRA_MANIFESTS {
        out.extend(load_specs_from(m)?);
    }
    Ok(out)
}

fn load_specs_from(manifest_path: &str) -> Result<Vec<Spec>, String> {
    let manifest = json::parse(&read(manifest_path)?)?;
    let repository = manifest
        .get("repository")
        .and_then(json::Json::as_str)
        .unwrap_or("WebAssembly/spec")
        .to_string();
    let revision = manifest
        .get("revision")
        .and_then(json::Json::as_str)
        .ok_or("manifest: no revision")?
        .to_string();
    let width = manifest
        .get("astWidth")
        .and_then(json::Json::as_usize)
        .ok_or("manifest: no astWidth")?;
    let mut out = Vec::new();
    for s in manifest
        .get("specs")
        .and_then(json::Json::as_arr)
        .ok_or("manifest: no specs")?
    {
        let field = |k: &str| {
            s.get(k)
                .and_then(json::Json::as_str)
                .map(str::to_string)
                .ok_or(format!("manifest: spec without {k}"))
        };
        let name = field("name")?;
        let path = field("path")?;
        let sha256 = field("sha256")?;
        let definitions = s
            .get("definitions")
            .and_then(json::Json::as_usize)
            .ok_or("manifest: spec without definitions")?;
        let bytes = std::fs::read(&path).map_err(|e| format!("{path}: {e}"))?;
        let actual = sha256::hex(&bytes);
        if actual != sha256 {
            return Err(format!("{path}: SHA-256 {actual}, manifest says {sha256}"));
        }
        let text = String::from_utf8(bytes).map_err(|e| format!("{path}: {e}"))?;
        let defs = sexp::parse_stream(&text).map_err(|e| format!("{path}: {e}"))?;
        if defs.len() != definitions {
            return Err(format!(
                "{path}: {} definitions, manifest says {definitions}",
                defs.len()
            ));
        }
        if sexp::ast_file(width, &defs) != text {
            return Err(format!("{path}: the printer does not reproduce the stream"));
        }
        let module = s
            .get("module")
            .and_then(json::Json::as_str)
            .map_or_else(|| module_of(&name), str::to_string);
        out.push(Spec {
            module,
            name,
            path,
            sha256,
            definitions,
            repository: repository.clone(),
            revision: revision.clone(),
            defs,
        });
    }
    Ok(out)
}

/// The provenance comment at the top of every generated file.
fn provenance(spec: &Spec, errata: &[(String, String)]) -> String {
    let mut s = format!(
        "/-\nGenerated by {GENERATOR} (tools/spectec-gen); do not edit.\n\
         Input: {} = {} (SHA-256 {}), {} definitions,\n\
         from {}@{}.\n",
        spec.name, spec.path, spec.sha256, spec.definitions, spec.repository, spec.revision
    );
    for (path, sha) in errata {
        s.push_str(&format!("Errata: {path} (SHA-256 {sha}).\n"));
    }
    s.push_str(&format!("Regenerate: {REGEN}\n-/\n"));
    s
}

/// A short description of a definition for its docstring.
fn describe(d: &sexp::SExp) -> String {
    match emit::decl_kind(d) {
        Some((k, n)) => format!("`{k} {n}`"),
        None => match d {
            sexp::SExp::Node(_, ks) => {
                let names: Vec<String> = ks
                    .iter()
                    .filter_map(emit::decl_kind)
                    .map(|(k, n)| format!("{k} {n}"))
                    .collect();
                format!("`rec` group of {}", names.join(", "))
            }
            _ => "definition".into(),
        },
    }
}

/// Emit `def d{i}` for the given definitions, split into parts; returns the part files.
fn emit_parts(
    out: &mut BTreeMap<String, String>,
    dir: &str,
    namespace: &str,
    header: &str,
    defs: &[(usize, &sexp::SExp)],
) -> Result<Vec<String>, String> {
    let mut parts: Vec<String> = Vec::new();
    let mut body = String::new();
    let flush = |body: &mut String, parts: &mut Vec<String>, out: &mut BTreeMap<String, String>| {
        if body.is_empty() {
            return;
        }
        let k = parts.len();
        let file = format!(
            "module\n\npublic import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast\n\n{header}\n\
             @[expose] public section\n\nnamespace {namespace}\n\nopen Silmaril.SpecTec.IL\n\n\
             set_option maxRecDepth 100000\n\n{body}end {namespace}\n"
        );
        out.insert(format!("{dir}/Part{k}.lean"), file);
        parts.push(format!("Part{k}"));
        body.clear();
    };
    for (i, d) in defs {
        let term = emit::def(d).map_err(|e| format!("{namespace} definition {i}: {e}"))?;
        body.push_str(&format!(
            "/-- Definition {i}: {}. -/\nnoncomputable def d{i} : Def :=\n{}\n\n",
            describe(d),
            emit::wrap(&term, "  ", WRAP)
        ));
        if body.len() >= PART_BYTES {
            flush(&mut body, &mut parts, out);
        }
    }
    flush(&mut body, &mut parts, out);
    Ok(parts)
}

fn script_list(names: &[String]) -> String {
    let mut out = String::from("  ");
    let mut col = 2;
    for (i, n) in names.iter().enumerate() {
        let piece = format!("{n} ::");
        if i > 0 {
            if col + 1 + piece.len() > WRAP {
                out.push_str("\n  ");
                col = 2;
            } else {
                out.push(' ');
                col += 1;
            }
        }
        out.push_str(&piece);
        col += piece.len();
    }
    out.push_str(" []");
    out
}

/// `Wasm30` for the pinned streams, `Main/Wasm30` (resp. `Main.Wasm30`) for a channel.
fn channel_path(channel: &str, module: &str, sep: char) -> String {
    if channel.is_empty() {
        module.to_string()
    } else {
        format!("{channel}{sep}{module}")
    }
}

fn emit_original(
    out: &mut BTreeMap<String, String>,
    spec: &Spec,
    channel: &str,
) -> Result<(), String> {
    let dir = format!(
        "{OUT_DIR}/{}/Original",
        channel_path(channel, &spec.module, '/')
    );
    let module = channel_path(channel, &spec.module, '.');
    let namespace = format!("{NAMESPACE_ROOT}.{module}.Original");
    let header = provenance(spec, &[]);
    let defs: Vec<(usize, &sexp::SExp)> = spec.defs.iter().enumerate().collect();
    let parts = emit_parts(out, &dir, &namespace, &header, &defs)?;
    let imports: String = parts
        .iter()
        .map(|p| format!("public import {MODULE_ROOT}.{module}.Original.{p}\n"))
        .collect();
    let names: Vec<String> = (0..spec.defs.len()).map(|i| format!("d{i}")).collect();
    let file = format!(
        "module\n\n{imports}\n{header}\n\
         @[expose] public section\n\nnamespace {namespace}\n\nopen Silmaril.SpecTec.IL\n\n\
         set_option maxRecDepth 100000\n\n\
         /-- The pinned `{}` revision the stream was produced from. -/\n\
         def sourceRevision : String := {}\n\n\
         /-- The SHA-256 of `{}`. -/\ndef sourceSha256 : String := {}\n\n\
         /-- The number of top-level definitions. -/\ndef definitionCount : Nat := {}\n\n\
         /-- `{}`, definition by definition. -/\nnoncomputable def script : Script :=\n{}\n\n\
         end {namespace}\n",
        spec.repository,
        emit::lean_str(&spec.revision),
        spec.path,
        emit::lean_str(&spec.sha256),
        spec.definitions,
        spec.path,
        script_list(&names)
    );
    out.insert(format!("{dir}.lean"), file);
    Ok(())
}

/// The errata of a variant, the receipts of their files, and the script they produce.
type VariantScript = (Vec<errata::Erratum>, Vec<(String, String)>, Vec<sexp::SExp>);

fn variant_defs(spec: &Spec, v: &Variant) -> Result<VariantScript, String> {
    let mut errata = Vec::new();
    let mut receipts = Vec::new();
    for f in v.errata_files {
        let path = format!("{}/{f}", v.errata_dir);
        let src = read(&path)?;
        receipts.push((path.clone(), sha256::hex(src.as_bytes())));
        let es = errata::extract(&src).map_err(|e| format!("{path}: {e}"))?;
        let want = format!("Specs.{}", spec.module.to_lowercase());
        for e in &es {
            if e.script != want {
                return Err(format!(
                    "{path}: erratum {} is on {}, expected {want}",
                    e.issue, e.script
                ));
            }
        }
        errata.extend(es);
    }
    let fixed = errata::apply_all(&errata, &spec.defs)?;
    Ok((errata, receipts, fixed))
}

fn emit_variant(
    out: &mut BTreeMap<String, String>,
    spec: &Spec,
    v: &Variant,
) -> Result<Vec<usize>, String> {
    let (errata, receipts, fixed) = variant_defs(spec, v)?;
    let changed: Vec<usize> = (0..fixed.len())
        .filter(|&i| fixed[i] != spec.defs[i])
        .collect();
    let dir = format!("{OUT_DIR}/{}/{}", spec.module, v.name);
    let namespace = format!("{NAMESPACE_ROOT}.{}.{}", spec.module, v.name);
    let header = provenance(spec, &receipts);
    let defs: Vec<(usize, &sexp::SExp)> = changed.iter().map(|&i| (i, &fixed[i])).collect();
    let parts = emit_parts(out, &dir, &namespace, &header, &defs)?;
    let mut imports = format!("public import {MODULE_ROOT}.{}.Original\n", spec.module);
    for p in &parts {
        imports.push_str(&format!(
            "public import {MODULE_ROOT}.{}.{}.{p}\n",
            spec.module, v.name
        ));
    }
    let names: Vec<String> = (0..fixed.len())
        .map(|i| {
            if changed.contains(&i) {
                format!("d{i}")
            } else {
                format!("Original.d{i}")
            }
        })
        .collect();
    let changed_list = changed
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let issues = errata
        .iter()
        .map(|e| e.issue.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let file = format!(
        "module\n\n{imports}\n{header}\n\
         @[expose] public section\n\nnamespace {namespace}\n\nopen Silmaril.SpecTec.IL\n\n\
         set_option maxRecDepth 100000\n\n\
         /-- The top-level indices whose definitions the errata change. -/\n\
         def changedIndices : List Nat := [{changed_list}]\n\n\
         /-- The issue numbers of the errata applied, in order. -/\n\
         def issues : List Nat := [{issues}]\n\n\
         /-- {}: the changed definitions above, every other one shared with `Original`. -/\n\
         noncomputable def script : Script :=\n{}\n\n\
         end {namespace}\n",
        v.doc,
        script_list(&names)
    );
    out.insert(format!("{dir}.lean"), file);
    Ok(changed)
}

/// Literal slices of the wasm-3.0 stream, for kernel-checked reading certificates.
fn emit_slices(out: &mut BTreeMap<String, String>, spec: &Spec) -> Result<(), String> {
    let text = read(&spec.path)?;
    // Definitions are separated by the printer's newline after each top-level form.
    let mut starts = Vec::new();
    let mut ends = Vec::new();
    let mut offset = 0;
    let mut depth = 0i64;
    let mut in_str = false;
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if in_str {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_str = false;
            }
        } else {
            match c {
                b'"' => in_str = true,
                b'(' => {
                    if depth == 0 {
                        starts.push(i);
                    }
                    depth += 1;
                }
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        ends.push(i + 1);
                    }
                }
                _ => {}
            }
        }
        i += 1;
        offset = i;
    }
    let _ = offset;
    if starts.len() != spec.defs.len() || ends.len() != spec.defs.len() {
        return Err("slices: definition boundaries do not match the parse".into());
    }
    let line_of = |pos: usize| text[..pos].matches('\n').count() + 1;
    let slice = |from: usize, to: usize| {
        // Each top-level form is followed by exactly one newline in the stream.
        let s = &text[starts[from]..ends[to] + 1];
        (s.to_string(), line_of(starts[from]), line_of(ends[to]))
    };
    let (prefix5, p_lo, p_hi) = slice(0, 4);
    if starts[0] != 0 {
        return Err("slices: the stream does not start with a definition".into());
    }
    let bi32 = spec
        .defs
        .iter()
        .position(|d| emit::decl_kind(d).is_some_and(|(k, n)| k == "gram" && n == "Bi32"))
        .ok_or("slices: no gram Bi32")?;
    let (bi32_text, b_lo, b_hi) = slice(bi32, bi32);
    let header = provenance(spec, &[]);
    let namespace = format!("{NAMESPACE_ROOT}.{}.AstSlices", spec.module);
    let file = format!(
        "module\n\npublic import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast\n\n{header}\n\
         @[expose] public section\n\nnamespace {namespace}\n\n\
         /-- Lines {p_lo}–{p_hi} of `{path}`, verbatim with the trailing newline: definitions 0–4\n\
         (`N`, `K`, `n`, `m`, `min`). SHA-256 of the slice: `{p_sha}`. -/\n\
         def prefix5 : String :=\n  {p_lit}\n\n\
         /-- Lines {b_lo}–{b_hi} of `{path}`, verbatim with the trailing newline: definition {bi32}\n\
         (`gram Bi32`). SHA-256 of the slice: `{b_sha}`. -/\n\
         def bi32 : String :=\n  {b_lit}\n\n\
         /-- The index of `gram Bi32` in the stream. -/\n\
         def bi32Index : Nat := {bi32}\n\n\
         end {namespace}\n",
        path = spec.path,
        p_sha = sha256::hex(prefix5.as_bytes()),
        p_lit = emit::lean_str(&prefix5),
        b_sha = sha256::hex(bi32_text.as_bytes()),
        b_lit = emit::lean_str(&bi32_text),
    );
    out.insert(format!("{OUT_DIR}/{}/AstSlices.lean", spec.module), file);
    Ok(())
}

/// Everything `generate` writes, by path.
fn outputs() -> Result<BTreeMap<String, String>, String> {
    let specs = load_specs()?;
    let mut out = BTreeMap::new();
    let mut umbrella = String::from("module\n\n");
    for spec in &specs {
        emit_original(&mut out, spec, "")?;
        umbrella.push_str(&format!(
            "public import {MODULE_ROOT}.{}.Original\n",
            spec.module
        ));
        for v in VARIANTS.iter().filter(|v| v.spec == spec.module) {
            emit_variant(&mut out, spec, v)?;
            umbrella.push_str(&format!(
                "public import {MODULE_ROOT}.{}.{}\n",
                spec.module, v.name
            ));
        }
        if spec.module == "Wasm30" {
            emit_slices(&mut out, spec)?;
            umbrella.push_str(&format!(
                "public import {MODULE_ROOT}.{}.AstSlices\n",
                spec.module
            ));
        }
    }
    let main_specs = load_specs_from(MAIN_MANIFEST)?;
    for spec in &main_specs {
        emit_original(&mut out, spec, MAIN_CHANNEL)?;
        umbrella.push_str(&format!(
            "public import {MODULE_ROOT}.{MAIN_CHANNEL}.{}.Original\n",
            spec.module
        ));
    }
    let status = errata_status(&specs, &main_specs)?;
    out.insert(
        format!("{OUT_DIR}/{MAIN_CHANNEL}/ErrataStatus.lean"),
        emit_errata_status(&status, &main_specs[0].revision),
    );
    umbrella.push_str(&format!(
        "public import {MODULE_ROOT}.{MAIN_CHANNEL}.ErrataStatus\n"
    ));
    // Extra manifests (other source repositories) are not Wasm specs: their modules are
    // imported directly by the topics that use them, not through the umbrella, so adding one
    // does not rebuild every module that imports the Wasm scripts.
    for spec in &load_extra_specs()? {
        emit_original(&mut out, spec, "")?;
        for v in VARIANTS.iter().filter(|v| v.spec == spec.module) {
            emit_variant(&mut out, spec, v)?;
        }
    }
    let manifest = json::parse(&read(MANIFEST)?)?;
    let known = sources::manifest_sources(&manifest)?;
    if let Some(body) = sources::emit("specs/spectec/src", &known)? {
        let namespace = format!("{NAMESPACE_ROOT}.Sources");
        let file = format!(
            "module\n\n/-\nGenerated by {GENERATOR} (tools/spectec-gen); do not edit.\n\
             Inputs: line ranges of the vendored sources under specs/spectec/src/, each checked \
             against the\nSHA-256 in {MANIFEST}, from WebAssembly/spec@{}.\n\
             Regenerate: {REGEN}\n-/\n\n@[expose] public section\n\nnamespace {namespace}\n\n\
             {body}end {namespace}\n",
            specs[0].revision
        );
        out.insert(format!("{OUT_DIR}/Sources.lean"), file);
        umbrella.push_str(&format!("public import {MODULE_ROOT}.Sources\n"));
    }
    umbrella.push_str(&format!(
        "\n/-!\n# Generated SpecTec scripts\n\nEvery module under `{MODULE_ROOT}` is written by \
         `tools/spectec-gen`; regenerate with\n`{REGEN}`.\n-/\n"
    ));
    out.insert(format!("{OUT_DIR}.lean"), umbrella);
    Ok(out)
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !Path::new(MANIFEST).exists() {
        return Err(format!(
            "{MANIFEST} not found; run from the repository root"
        ));
    }
    match args.first().map(String::as_str) {
        Some("generate") => {
            let out = outputs()?;
            for (path, text) in &out {
                if let Some(dir) = Path::new(path).parent() {
                    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
                }
                std::fs::write(path, text).map_err(|e| format!("{path}: {e}"))?;
            }
            let stale = stale_files(&out)?;
            for f in &stale {
                std::fs::remove_file(f).map_err(|e| format!("{f}: {e}"))?;
            }
            println!("wrote {} files, removed {}", out.len(), stale.len());
            Ok(())
        }
        Some("check") => {
            let out = outputs()?;
            let mut bad = Vec::new();
            for (path, text) in &out {
                if std::fs::read_to_string(path).ok().as_deref() != Some(text.as_str()) {
                    bad.push(path.clone());
                }
            }
            bad.extend(stale_files(&out)?);
            if bad.is_empty() {
                println!("{} generated files are up to date", out.len());
                Ok(())
            } else {
                Err(format!("out of date (run `{REGEN}`): {}", bad.join(", ")))
            }
        }
        Some("check-sources") => {
            sources::check(MANIFEST)?;
            for m in EXTRA_MANIFESTS {
                sources::check(m)?;
            }
            Ok(())
        }
        Some("errata-status") => {
            let status = errata_status(&load_specs()?, &load_specs_from(MAIN_MANIFEST)?)?;
            for r in &status {
                println!(
                    "#{:<4} {:<14} {:<20} {:<18} {}",
                    r.issue,
                    r.file,
                    r.target,
                    r.status.tag(),
                    r.status.describe()
                );
            }
            Ok(())
        }
        Some("theory-diff") => {
            let list = args.iter().any(|a| a == "--list");
            for (label, a, b) in theory_pairs()? {
                let (ta, tb) = (theory::theory(&a), theory::theory(&b));
                let d = theory::diff(&ta, &tb);
                println!("{}", theory::summary(&label, &ta, &d));
                if list {
                    for (r, n) in &d.rules_dropped {
                        println!("    dropped {r}/{n}");
                    }
                    for r in &d.rels_redeclared {
                        println!("    redeclared {r}");
                    }
                }
            }
            Ok(())
        }
        Some("version") => version::run(&args[1..]),
        _ => Err(
            "usage: spectec-gen generate | check | check-sources | errata-status | \
                  theory-diff [--list] | version …"
                .into(),
        ),
    }
}

/// What became of one erratum's target on the later revision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Status {
    /// The target is unchanged: the patch applies verbatim and the defect is still there.
    Unchanged,
    /// The target now equals the erratum's corrected definition.
    FixedAsErratum,
    /// The target changed, but the patch still applies to it (the fragment is still there).
    ChangedStillApplies,
    /// The target changed and the patch no longer applies: read the new definition.
    ChangedReview,
    /// No definition of that name (or more than one) on the later revision.
    TargetGone,
}

impl Status {
    fn tag(self) -> &'static str {
        match self {
            Status::Unchanged => "unchanged",
            Status::FixedAsErratum => "fixedAsErratum",
            Status::ChangedStillApplies => "changedStillApplies",
            Status::ChangedReview => "changedReview",
            Status::TargetGone => "targetGone",
        }
    }

    fn describe(self) -> &'static str {
        match self {
            Status::Unchanged => "target unchanged; the patch applies verbatim (still needed)",
            Status::FixedAsErratum => "target equals the erratum's correction (fixed upstream)",
            Status::ChangedStillApplies => "target changed; the patch still applies",
            Status::ChangedReview => "target changed; the patch no longer applies (review)",
            Status::TargetGone => "target not declared exactly once on the later revision",
        }
    }
}

/// One row of the errata status table.
struct StatusRow {
    issue: u32,
    file: &'static str,
    target: String,
    status: Status,
}

/// The script pairs `theory-diff` compares: consecutive versions, every errata variant against
/// its original, and every pinned stream against the later main revision.
/// A labelled pair of scripts, earlier first.
type ScriptPair = (String, Vec<sexp::SExp>, Vec<sexp::SExp>);

fn theory_pairs() -> Result<Vec<ScriptPair>, String> {
    let pinned = load_specs()?;
    let extra = load_extra_specs()?;
    let main = load_specs_from(MAIN_MANIFEST)?;
    let mut out = Vec::new();
    for w in pinned.windows(2) {
        out.push((
            format!("{} -> {}", w[0].name, w[1].name),
            w[0].defs.clone(),
            w[1].defs.clone(),
        ));
    }
    for v in VARIANTS {
        let spec = pinned
            .iter()
            .chain(extra.iter())
            .find(|s| s.module == v.spec)
            .ok_or(format!("no stream {}", v.spec))?;
        let (_, _, fixed) = variant_defs(spec, v)?;
        out.push((
            format!("{} original -> {}", spec.name, v.name),
            spec.defs.clone(),
            fixed,
        ));
    }
    for s in &pinned {
        if let Some(m) = main.iter().find(|m| m.module == s.module) {
            out.push((
                format!(
                    "{} pinned -> main@{}",
                    s.name,
                    &m.revision[..8.min(m.revision.len())]
                ),
                s.defs.clone(),
                m.defs.clone(),
            ));
        }
    }
    Ok(out)
}

/// The unique definition (at any `rec` depth) declaring `name`.
fn unique_decl<'a>(defs: &'a [sexp::SExp], name: &str) -> Option<&'a sexp::SExp> {
    fn walk<'a>(defs: &'a [sexp::SExp], name: &str, hits: &mut Vec<&'a sexp::SExp>) {
        for d in defs {
            match d {
                sexp::SExp::Node(t, ks) if t == "rec" => walk(ks, name, hits),
                d if emit::decl_kind(d).is_some_and(|(_, n)| n == name) => hits.push(d),
                _ => {}
            }
        }
    }
    let mut hits = Vec::new();
    walk(defs, name, &mut hits);
    match hits.as_slice() {
        [d] => Some(d),
        _ => None,
    }
}

/// Classify every `spectec_erratum` command against the later revision's streams.
fn errata_status(pinned: &[Spec], later: &[Spec]) -> Result<Vec<StatusRow>, String> {
    let mut rows = Vec::new();
    for (file, module) in ERRATA_FILES {
        let path = format!("{ERRATA_DIR}/{file}");
        let es = errata::extract(&read(&path)?).map_err(|e| format!("{path}: {e}"))?;
        let base = pinned
            .iter()
            .find(|s| &s.module == module)
            .ok_or(format!("no pinned {module}"))?;
        let new = later
            .iter()
            .find(|s| &s.module == module)
            .ok_or(format!("no later {module}"))?;
        for e in es {
            let orig = unique_decl(&base.defs, &e.target)
                .ok_or(format!("erratum {}: no pinned {}", e.issue, e.target))?;
            let fixed = errata::corrected(&e, &base.defs)?;
            let status = match unique_decl(&new.defs, &e.target) {
                None => Status::TargetGone,
                Some(d) if d == orig => Status::Unchanged,
                Some(d) if *d == fixed => Status::FixedAsErratum,
                Some(_) if errata::corrected(&e, &new.defs).is_ok() => Status::ChangedStillApplies,
                Some(_) => Status::ChangedReview,
            };
            rows.push(StatusRow {
                issue: e.issue,
                file,
                target: e.target.clone(),
                status,
            });
        }
    }
    Ok(rows)
}

/// The errata status table as Lean data.
fn emit_errata_status(rows: &[StatusRow], revision: &str) -> String {
    let namespace = format!("{NAMESPACE_ROOT}.{MAIN_CHANNEL}.ErrataStatus");
    let mut body = String::new();
    for r in rows {
        body.push_str(&format!(
            "  ({}, {}, {}, .{}) ::\n",
            r.issue,
            emit::lean_str(r.file),
            emit::lean_str(&r.target),
            r.status.tag()
        ));
    }
    format!(
        "module\n\n/-\nGenerated by {GENERATOR} (tools/spectec-gen); do not edit.\n\
         Inputs: the spectec_erratum commands of {ERRATA_DIR}/*.lean, the pinned streams of \
         {MANIFEST}\nand the streams of {MAIN_MANIFEST} (WebAssembly/spec@{revision}).\n\
         Regenerate: {REGEN}\n-/\n\n@[expose] public section\n\nnamespace {namespace}\n\n\
         /-- What became of an erratum's target definition on the later revision.  Computed by \
         the\n(unverified) generator on the S-expressions, as `errata-status` prints it. -/\n\
         inductive Status where\n\
         \x20 /-- The target is unchanged: the patch applies verbatim (the defect is still there). -/\n\
         \x20 | unchanged\n\
         \x20 /-- The target equals the erratum's corrected definition (fixed upstream as proposed). -/\n\
         \x20 | fixedAsErratum\n\
         \x20 /-- The target changed, but the patch still applies to it. -/\n\
         \x20 | changedStillApplies\n\
         \x20 /-- The target changed and the patch no longer applies: read the new definition. -/\n\
         \x20 | changedReview\n\
         \x20 /-- The target is not declared exactly once on the later revision. -/\n\
         \x20 | targetGone\n\
         \x20 deriving DecidableEq, Repr\n\n\
         /-- `(issue, errata file, target, status)`, one row per `spectec_erratum` command. -/\n\
         def rows : List (Nat × String × String × Status) :=\n{body}  []\n\n\
         end {namespace}\n"
    )
}

/// Generated-tree `.lean` files that `generate` would no longer write.
fn stale_files(out: &BTreeMap<String, String>) -> Result<Vec<String>, String> {
    let mut found = Vec::new();
    fn walk(dir: &Path, found: &mut Vec<String>) -> Result<(), String> {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return Ok(());
        };
        for e in rd {
            let p = e.map_err(|e| e.to_string())?.path();
            if p.is_dir() {
                walk(&p, found)?;
            } else if p.extension().is_some_and(|x| x == "lean") {
                found.push(p.to_string_lossy().into_owned());
            }
        }
        Ok(())
    }
    walk(Path::new(OUT_DIR), &mut found)?;
    found.retain(|f| !out.contains_key(f));
    found.sort();
    Ok(found)
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("spectec-gen: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at_root() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        std::env::set_current_dir(root).unwrap();
    }

    #[test]
    fn streams_round_trip_and_errata_apply() {
        at_root();
        let specs = load_specs().unwrap();
        assert_eq!(
            specs.iter().map(|s| s.defs.len()).collect::<Vec<_>>(),
            [315, 467, 976]
        );
        let mut out = BTreeMap::new();
        let wasm30 = &specs[2];
        let v = VARIANTS.iter().find(|v| v.name == "Binary51").unwrap();
        let changed = emit_variant(&mut out, wasm30, v).unwrap();
        // Every changed top-level definition declares a target, and every target is declared by
        // a changed definition (`utf8` sits inside a `rec` group).
        let declared = |d: &sexp::SExp| -> Vec<String> {
            match d {
                sexp::SExp::Node(t, ks) if t == "rec" => ks
                    .iter()
                    .filter_map(emit::decl_kind)
                    .map(|(_, n)| n)
                    .collect(),
                d => emit::decl_kind(d).map(|(_, n)| n).into_iter().collect(),
            }
        };
        let targets = ["Bi32", "Bi64", "cont", "utf8"];
        assert_eq!(changed.len(), 4);
        for &i in &changed {
            assert!(
                declared(&wasm30.defs[i])
                    .iter()
                    .any(|n| targets.contains(&n.as_str()))
            );
        }
        for t in targets {
            assert!(
                changed
                    .iter()
                    .any(|&i| declared(&wasm30.defs[i]).iter().any(|n| n == t))
            );
        }
        let extra = load_extra_specs().unwrap();
        for v in VARIANTS {
            let spec = specs
                .iter()
                .chain(extra.iter())
                .find(|s| s.module == v.spec)
                .unwrap();
            emit_variant(&mut out, spec, v).unwrap();
        }
    }

    #[test]
    fn theory_diffs_of_the_pinned_streams() {
        at_root();
        let pairs = theory_pairs().unwrap();
        let get = |label: &str| {
            let (_, a, b) = pairs.iter().find(|p| p.0 == label).unwrap();
            theory::diff(&theory::theory(a), &theory::theory(b))
        };
        // The wasm-3.0 errata touch grammars and functions only.
        assert!(get("wasm-3.0 original -> Fixed").is_morphism());
        assert!(get("wasm-2.0 original -> Fixed").is_morphism());
        // Erratum 680 rewrites the one rule of `Module_ok`.
        let d = get("wasm-1.0 original -> Fixed");
        assert_eq!(d.rules_dropped, [("Module_ok".to_string(), String::new())]);
    }

    #[test]
    fn source_ranges() {
        let dir = std::env::temp_dir().join(format!("spectec-gen-test-{}", std::process::id()));
        let path = "specification/wasm-3.0/0.1-aux.vars.spectec";
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        let text = ";;\n;; x\n;;\n\nsyntax N hint(macro none) = nat\nsyntax K = nat\nb\nc\n";
        std::fs::write(&file, text).unwrap();
        let known = vec![(path.to_string(), sha256::hex(text.as_bytes()))];
        let body = sources::emit(dir.to_str().unwrap(), &known)
            .unwrap()
            .unwrap();
        assert!(
            body.contains(
                "def wasm30_vars_line5 : String :=\n  \"syntax N hint(macro none) = nat\""
            )
        );
        assert!(body.contains("\"syntax N hint(macro none) = nat\\nsyntax K = nat\\nb\\nc\""));
        let bad = vec![(path.to_string(), "00".to_string())];
        assert!(sources::emit(dir.to_str().unwrap(), &bad).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn main_streams_and_errata_status() {
        at_root();
        let main = load_specs_from(MAIN_MANIFEST).unwrap();
        assert_eq!(
            main.iter().map(|s| s.defs.len()).collect::<Vec<_>>(),
            [318, 470, 974]
        );
        let status = errata_status(&load_specs().unwrap(), &main).unwrap();
        // One row per `spectec_erratum` command: 4 + 9 + 8 + 4.
        assert_eq!(status.len(), 25);
        let of = |issue: u32, target: &str| {
            status
                .iter()
                .find(|r| r.issue == issue && r.target == target)
                .unwrap()
                .status
        };
        assert_eq!(of(654, "Bi32"), Status::FixedAsErratum);
        assert_eq!(of(655, "cont"), Status::FixedAsErratum);
        assert_eq!(of(661, "Tstringchar"), Status::FixedAsErratum);
        assert_eq!(of(663, "Talign_"), Status::FixedAsErratum);
        assert_eq!(of(684, "utf8"), Status::FixedAsErratum);
        assert_eq!(of(685, "utf8"), Status::ChangedReview);
        assert_eq!(of(673, "dataidx_instrs"), Status::Unchanged);
    }

    #[test]
    fn emission_is_stable() {
        at_root();
        assert_eq!(outputs().unwrap(), outputs().unwrap());
    }
}
