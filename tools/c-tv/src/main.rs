//! `c-tv`: from a C file, a pinned compiler and its flags to Lean goals relating the C code, its
//! Cerberus Core and the x86-64 bytes the compiler emitted (README.md).
//!
//! ```text
//! c-tv gen --src FILE.c --name NAME [--opt O0 --opt O2 …] [--flags "…"] [--image IMAGE]
//!          [--core-probe CMD | --core FILE] [--root DIR] [--base ADDR]
//! ```
//!
//! For each optimisation level the tool compiles `FILE.c` to a relocatable object inside the
//! pinned container `IMAGE` (`gcc -OPT -g -c FLAGS`, in the working directory `/src` with
//! `-fdebug-prefix-map=/src=.`, so that no host path reaches the object), records the
//! compiler's identity and the hashes (`RECEIPT.json`), reads `.text`, the symbols, the
//! relocations, the DWARF line table and the frame slots, decodes the code into the Lean
//! model's instructions (`lift-x86`, in `../x86-lift`), and computes the correspondence of
//! every function (`corr`). The C file's Core comes from the Lean port of Cerberus, run by
//! `--core-probe CMD` on a generated probe module (`{module}` and `{file}` in `CMD` are
//! substituted, `{file}` relative to `--root`; e.g. `lake env lean {file}`), or from a saved
//! probe output (`--core`). The tool writes, under `--root`:
//!
//! * `examples/compiles-to/NAME/OPT/NAME.o` and `RECEIPT.json` (the artifacts, committed);
//! * `examples/compiles-to/NAME/correspondence.{json,md}` (the compiler-explorer view);
//! * `examples/compiles-to/NAME/core-probe.txt` (the probe's output, for `--core`);
//! * the Lean header with every goal, its proof modules and its rows (README.md).
//!
//! Nothing it writes is trusted: Lean checks the bytes against the object, the listing against
//! the decoder and the Core fragments against the Core; the goals are open until proved.

mod corr;
mod emit;
mod obj;
mod sexp;

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};
use sha2::{Digest, Sha256};

const DEFAULT_IMAGE: &str =
    "gcc:13.3.0@sha256:1d71f0f3450214bef38fe09e6f610fb6cca90cf97b43f4ce845bfc32a4168818";
const DEFAULT_FLAGS: &str = "-std=c11 -ffreestanding -fno-builtin -fno-stack-protector \
-fcf-protection=none -mgeneral-regs-only -fno-pic -fno-pie -fno-asynchronous-unwind-tables \
-fno-unwind-tables -fno-ident";
/// The compiler's working directory in the container, where the source directory is mounted.
/// Every build maps it to `.` in the debug information (`-fdebug-prefix-map`).
const WORKDIR: &str = "/src";

struct Args {
    src: PathBuf,
    name: String,
    opts: Vec<String>,
    flags: Vec<String>,
    image: String,
    core_probe: Option<String>,
    core: Option<PathBuf>,
    root: PathBuf,
    base: u64,
}

fn parse_args() -> Result<Args> {
    let mut it = std::env::args().skip(1);
    match it.next().as_deref() {
        Some("gen") => {}
        Some("--help") | Some("-h") | None => {
            println!(
                "usage: c-tv gen --src FILE.c --name NAME [--opt O0]… [--flags \"…\"] [--image IMAGE] [--core-probe CMD | --core FILE] [--root DIR] [--base ADDR]"
            );
            std::process::exit(0);
        }
        Some(c) => bail!("unknown command {c}"),
    }
    let mut a = Args {
        src: PathBuf::new(),
        name: String::new(),
        opts: vec![],
        flags: DEFAULT_FLAGS.split_whitespace().map(String::from).collect(),
        image: DEFAULT_IMAGE.into(),
        core_probe: None,
        core: None,
        root: PathBuf::from("."),
        base: 0x401000,
    };
    while let Some(k) = it.next() {
        let mut v = || it.next().ok_or_else(|| anyhow!("{k} needs a value"));
        match k.as_str() {
            "--src" => a.src = v()?.into(),
            "--name" => a.name = v()?,
            "--opt" => a.opts.push(v()?),
            "--flags" => a.flags = v()?.split_whitespace().map(String::from).collect(),
            "--image" => a.image = v()?,
            "--core-probe" => a.core_probe = Some(v()?),
            "--core" => a.core = Some(v()?.into()),
            "--root" => a.root = v()?.into(),
            "--base" => {
                let s = v()?;
                a.base = u64::from_str_radix(s.trim_start_matches("0x"), 16)?;
            }
            _ => bail!("unknown option {k}"),
        }
    }
    if a.name.is_empty() || a.src.as_os_str().is_empty() {
        bail!("--src and --name are required");
    }
    if a.opts.is_empty() {
        a.opts = vec!["O0".into(), "O2".into()];
    }
    Ok(a)
}

fn sha256(b: &[u8]) -> String {
    let d = Sha256::digest(b);
    d.iter().map(|x| format!("{x:02x}")).collect()
}

fn run(cmd: &mut Command) -> Result<String> {
    let out = cmd.output().with_context(|| format!("run {cmd:?}"))?;
    if !out.status.success() {
        bail!(
            "{cmd:?} failed: {}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The flags of the build at `opt`: the level, `-g -c`, the debug prefix map and `--flags`.
fn build_flags(a: &Args, opt: &str) -> Vec<String> {
    let mut flags = vec![
        format!("-{opt}"),
        "-g".into(),
        "-c".into(),
        format!("-fdebug-prefix-map={WORKDIR}=."),
    ];
    flags.extend(a.flags.iter().cloned());
    flags
}

/// Compile in the pinned container; returns the receipt. The source directory is mounted at
/// [`WORKDIR`], the compiler's working directory: the object records `.` as its compilation
/// directory, and the receipt holds paths relative to the source directory and the tools'
/// paths in the image, never a host path.
fn compile(
    a: &Args,
    src_dir: &Path,
    file: &str,
    opt: &str,
    out_rel: &str,
) -> Result<serde_json::Value> {
    let command = format!("gcc {} {file} -o {out_rel}", build_flags(a, opt).join(" "));
    let script = format!(
        "set -e; {command}; gcc --version | head -1; as --version | head -1; \
         sha256sum \"$(gcc -print-prog-name=cc1)\" \"$(command -v as)\""
    );
    let dir = std::fs::canonicalize(src_dir)?;
    let out = run(Command::new("docker").args([
        "run",
        "--rm",
        "--network",
        "host",
        "--user",
        &format!("{}:{}", uid(), gid()),
        "-v",
        &format!("{}:{WORKDIR}", dir.display()),
        "-w",
        WORKDIR,
        &a.image,
        "sh",
        "-c",
        &script,
    ]))?;
    let lines: Vec<&str> = out.lines().collect();
    Ok(serde_json::json!({
        "image": a.image,
        "workdir": WORKDIR,
        "command": command,
        "gcc": lines.first().copied().unwrap_or(""),
        "as": lines.get(1).copied().unwrap_or(""),
        "tools_sha256": lines.iter().skip(2).collect::<Vec<_>>(),
    }))
}

fn uid() -> String {
    run(Command::new("id").arg("-u"))
        .map(|s| s.trim().to_string())
        .unwrap_or("0".into())
}
fn gid() -> String {
    run(Command::new("id").arg("-g"))
        .map(|s| s.trim().to_string())
        .unwrap_or("0".into())
}

/// The probe's result: the typed Ail and Core document texts, or why there are none.
type Probed = Result<(String, String), String>;

/// The probe's output: its result and the raw text.
fn probe(a: &Args, c_text: &str, cached: &Path) -> Result<(Probed, String)> {
    let raw = if let Some(path) = &a.core {
        std::fs::read_to_string(path)?
    } else if let Some(cmd) = &a.core_probe {
        let module = format!(
            "Silmaril.Project.CompilesTo.ProbeRun.{}",
            emit::camel(&a.name)
        );
        // Relative to `--root`, where the command runs.
        let rel = format!(
            "Silmaril/Project/CompilesTo/ProbeRun/{}.lean",
            emit::camel(&a.name)
        );
        let file = a.root.join(&rel);
        std::fs::create_dir_all(file.parent().unwrap())?;
        std::fs::write(
            &file,
            format!(
                "module\n\npublic meta import Silmaril.Project.CompilesTo.Probe.Defs\n\n\
                 open Lean Elab Command in\nrun_cmd logWarning m!\"{{Silmaril.Project.CompilesTo.Probe.docText {}}}\"\n",
                emit::lean_string(c_text)
            ),
        )?;
        let cmd = cmd.replace("{module}", &module).replace("{file}", &rel);
        let out = Command::new("sh")
            .arg("-c")
            .arg(&cmd)
            .current_dir(&a.root)
            .output()?;
        let _ = std::fs::remove_file(&file);
        let _ = std::fs::remove_dir(file.parent().unwrap());
        let mut s = String::from_utf8_lossy(&out.stdout).into_owned();
        s.push_str(&String::from_utf8_lossy(&out.stderr));
        // The command may print more than the probe's message (a build log, the message's
        // position); keep only the probe's part.
        let keep = extract(&s);
        if keep.is_empty() {
            bail!(
                "the probe printed no result; its output:\n{}",
                s.chars().take(4000).collect::<String>()
            );
        }
        keep
    } else {
        bail!("give --core-probe CMD or --core FILE");
    };
    std::fs::write(cached, &raw)?;
    let res = if let Some(e) = find_between(&raw, "FRONTEND-ERROR: ", "\n") {
        Err(format!("the Lean C frontend rejects the file: {e}"))
    } else {
        let ail = find_between(&raw, "BEGIN-TYPED-AIL\n", "\nEND-TYPED-AIL")
            .ok_or_else(|| anyhow!("no typed Ail in the probe output"))?;
        if let Some(e) = find_between(&raw, "CORE-ELAB-ERROR: ", "\n") {
            Err(format!(
                "the Lean Cerberus elaborator rejects the file: {e}"
            ))
        } else {
            let doc = find_between(&raw, "BEGIN-CORE-DOCUMENT\n", "END-CORE-DOCUMENT")
                .ok_or_else(|| anyhow!("no Core document in the probe output"))?;
            Ok((ail, doc))
        }
    };
    Ok((res, raw))
}

fn extract(s: &str) -> String {
    for (b, e) in [
        ("BEGIN-TYPED-AIL", "END-CORE-DOCUMENT"),
        ("FRONTEND-ERROR", "\n"),
    ] {
        if let Some(i) = s.find(b) {
            let rest = &s[i..];
            if let Some(j) = rest.find(e) {
                return rest[..j + e.len()].to_string();
            }
        }
    }
    if let Some(i) = s.find("BEGIN-TYPED-AIL")
        && let Some(j) = s[i..].find("CORE-ELAB-ERROR")
    {
        let rest = &s[i + j..];
        let k = rest.find('\n').unwrap_or(rest.len());
        return format!("{}{}", &s[i..i + j], &rest[..k]);
    }
    String::new()
}

fn find_between(s: &str, a: &str, b: &str) -> Option<String> {
    let i = s.find(a)? + a.len();
    // an end marker of "\n" also matches the end of the text
    let j = match s[i..].find(b) {
        Some(j) => j + i,
        None if b == "\n" => s.len(),
        None => return None,
    };
    Some(s[i..j].to_string())
}

fn main() -> Result<()> {
    let a = parse_args()?;
    let c_text =
        std::fs::read_to_string(&a.src).with_context(|| format!("read {}", a.src.display()))?;
    let ex_dir = a.root.join("examples/compiles-to").join(&a.name);
    std::fs::create_dir_all(&ex_dir)?;
    let src_name = a.src.file_name().unwrap().to_string_lossy().into_owned();
    let src_in_ex = ex_dir.join(&src_name);
    if std::fs::canonicalize(&a.src)? != std::fs::canonicalize(&src_in_ex).unwrap_or_default() {
        std::fs::copy(&a.src, &src_in_ex)?;
    }
    let (core, _raw) = probe(&a, &c_text, &ex_dir.join("core-probe.txt"))?;
    let (ail_text, core_doc, core_error) = match &core {
        Ok((ail, doc)) => (Some(ail.clone()), Some(doc.clone()), None),
        Err(e) => (None, None, Some(e.clone())),
    };
    let doc_sx = match &core_doc {
        Some(d) => Some(sexp::parse(d)?),
        None => None,
    };
    let stem = src_name.trim_end_matches(".c").to_string();
    let mut builds = Vec::new();
    let mut compiler = String::new();
    let mut report = serde_json::Map::new();
    for opt in &a.opts {
        let out_rel = format!("{opt}/{stem}.o");
        std::fs::create_dir_all(ex_dir.join(opt))?;
        let receipt = compile(&a, &ex_dir, &src_name, opt, &out_rel)?;
        compiler = receipt["gcc"].as_str().unwrap_or("").to_string();
        let obj_path = ex_dir.join(&out_rel);
        let bytes = std::fs::read(&obj_path)?;
        let hash = sha256(&bytes);
        let mut receipt = receipt;
        receipt["object"] =
            serde_json::json!({ "path": out_rel, "sha256": hash, "size": bytes.len() });
        receipt["source"] =
            serde_json::json!({ "path": src_name, "sha256": sha256(c_text.as_bytes()) });
        std::fs::write(
            ex_dir.join(opt).join("RECEIPT.json"),
            serde_json::to_string_pretty(&receipt)? + "\n",
        )?;
        let o = obj::read(&bytes)?;
        let mut fns = Vec::new();
        let mut listings = Vec::new();
        for f in &o.funcs {
            let code = &o.text[f.off as usize..(f.off + f.size) as usize];
            let (asm, listing, decode_error) = match lift_x86::lift(code, 0) {
                Ok(l) => (
                    l.iter()
                        .map(|x| (f.off + x.addr, x.asm.clone()))
                        .collect::<Vec<_>>(),
                    l.iter()
                        .map(|x| (x.addr, x.instr.lean(), x.len(), x.asm.clone()))
                        .collect::<Vec<_>>(),
                    None,
                ),
                Err(e) => (vec![], vec![], Some(format!("{e}"))),
            };
            let proc_ = match (&doc_sx, &core_error) {
                (Some(d), _) => sexp::procedure(d, &f.name).map_err(|e| e.to_string()),
                (None, Some(e)) => Err(e.clone()),
                _ => Err("no Core".into()),
            };
            let inp = corr::Input {
                obj: &o,
                name: &f.name,
                off: f.off,
                size: f.size,
                info: o.info.get(&f.name),
                asm,
                decode_error,
                core: proc_,
            };
            let c = corr::correspond(&inp);
            fns.push(c);
            listings.push(listing);
        }
        report.insert(opt.clone(), serde_json::to_value(&fns)?);
        builds.push(emit::Build {
            tag: opt.clone(),
            obj_path: format!("examples/compiles-to/{}/{out_rel}", a.name),
            obj_sha256: hash,
            obj_bytes: bytes,
            text: o.text.clone(),
            fns,
            listings,
            flags: build_flags(&a, opt),
        });
    }
    let module = format!("{}.{}", emit::LIB, emit::camel(&a.name));
    let h = emit::Header {
        module: module.clone(),
        c_path: format!("examples/compiles-to/{}/{src_name}", a.name),
        c_text: &c_text,
        ail_text,
        core_doc,
        core_error,
        compiler,
        image: a.image.clone(),
        base: a.base,
        builds,
        tool_rev: "c-tv 0.1.0".into(),
    };
    let lib_root = a.root.join(emit::LIB_DIR).join(emit::LIB);
    let lean_dir = lib_root.join(emit::camel(&a.name));
    std::fs::create_dir_all(&lean_dir)?;
    std::fs::write(lean_dir.join("Defs.lean"), emit::header(&h))?;
    let mut pf = emit::proofs(&h, &emit::camel(&a.name));
    for p in &pf {
        let path = lib_root.join(&p.rel);
        std::fs::create_dir_all(path.parent().unwrap())?;
        std::fs::write(&path, &p.content)?;
    }
    // Proof modules written by hand (or by a prover) next to the generated ones: collected too.
    pf.extend(emit::found_proofs(
        &lib_root,
        &format!("{}/Proofs", emit::camel(&a.name)),
        &pf.iter().map(|p| p.rel.clone()).collect::<Vec<_>>(),
    )?);
    std::fs::write(lean_dir.join("Thms.lean"), emit::thms(&h, &pf))?;
    // The rows: the records of this file, its Rows module, and the group over every file.
    let rec_dir = a.root.join("silmaril/compiles-to");
    std::fs::create_dir_all(&rec_dir)?;
    let rec_path = rec_dir.join(format!("{}.toml", a.name));
    match emit::records(&h, &a.name, &pf) {
        Some(t) => {
            std::fs::write(&rec_path, t)?;
            if let Some(m) = emit::rows_module(&h, &a.name, &pf) {
                std::fs::write(lean_dir.join("Rows.lean"), m)?;
            }
        }
        None => {
            let _ = std::fs::remove_file(&rec_path);
            let _ = std::fs::remove_file(lean_dir.join("Rows.lean"));
        }
    }
    let mut names: Vec<String> = std::fs::read_dir(&rec_dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter_map(|n| n.strip_suffix(".toml").map(str::to_string))
        .collect();
    names.sort();
    let (root_toml, root_lean) = emit::root(&names);
    std::fs::write(a.root.join("silmaril/compiles-to.toml"), root_toml)?;
    std::fs::write(
        a.root
            .join(emit::LIB_DIR)
            .join(format!("{}.lean", emit::LIB)),
        root_lean,
    )?;
    std::fs::write(ex_dir.join("correspondence.md"), emit::markdown(&h))?;
    std::fs::write(
        ex_dir.join("correspondence.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    println!(
        "wrote {} and examples/compiles-to/{}/",
        lean_dir.join("Defs.lean").display(),
        a.name
    );
    for b in &h.builds {
        for f in &b.fns {
            println!(
                "{} {}: {} granularity, {} point(s), {} unsupported range(s){}",
                b.tag,
                f.name,
                f.granularity,
                f.points.len(),
                f.unsupported.len(),
                f.function_unsupported
                    .as_ref()
                    .map(|u| format!(" (no goals: {u})"))
                    .unwrap_or_default()
            );
        }
    }
    Ok(())
}
