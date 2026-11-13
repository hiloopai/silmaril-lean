//! The C11 litmus programs (`examples/litmus-c`): compiling them with pinned
//! compilers, ingesting the thread functions of each object (`src/ingest.rs`), checking the
//! result under SC and x86-TSO, and writing
//!
//! - `export/c11.json`: the tests in the `silmaril-litmus-x86-export/1` format, so
//!   `tools/litmus-run --json export/c11.json` runs them on hardware. Each thread also has a
//!   `code_base`, the fixed address its (rip-relative) bytes were relocated for;
//! - `export/c11-meta.json` (`silmaril-litmus-c11-meta/1`): the sidecar for `c11cir` (`c11 cir`), with
//!   per test the compiler, object and source hashes, the data layout and relocations, every
//!   instruction (bytes, `objdump` text, lifted text), each C11 access with its mode and the
//!   x86 instructions it compiled to, and the expected C11 verdict; and a per-compiler table
//!   of the x86 forms each (access kind, mode) compiled to (the seq_cst mapping among them).
//!
//! `examples/litmus-c/index.txt` lists the program directories; `toolchains.txt` pins the
//! compilers by sha256 and gives the flags; `objects.sha256` pins every object.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::checker::{self, Final, Mm, Verdict};
use crate::cspec::{AKind, Spec, VARIANTS, Variant};
use crate::elf::Object;
use crate::export::{cond, hex_bytes, json_str, verdict};
use crate::ingest::{self, Ingested, ThreadMap};
use crate::litmus::Error;

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

fn io<T>(p: &Path, r: std::io::Result<T>) -> Result<T, Error> {
    r.map_err(|e| Error(format!("{}: {e}", p.display())))
}

/// A pinned compiler.
#[derive(Clone, Debug)]
pub struct Compiler {
    pub name: String,
    /// The executable that is run.
    pub driver: PathBuf,
    /// The expected first line of `driver --version`.
    pub version: String,
    /// Every pinned file: (role, path, sha256).
    pub pins: Vec<(String, PathBuf, String)>,
}

/// `toolchains.txt`.
#[derive(Clone, Debug)]
pub struct Toolchains {
    pub flags: Vec<String>,
    pub compilers: Vec<Compiler>,
}

fn expand(p: &str) -> PathBuf {
    match p.strip_prefix("~/") {
        Some(rest) => PathBuf::from(std::env::var("HOME").unwrap_or_default()).join(rest),
        None => PathBuf::from(p),
    }
}

/// Parse `toolchains.txt`: `flags | ...`, `<cc> | version | <text>`, `<cc> | driver |
/// <path> | <sha256>` and `<cc> | <role> | <path> | <sha256>` lines.
pub fn parse_toolchains(src: &str) -> Result<Toolchains, Error> {
    let mut t = Toolchains {
        flags: Vec::new(),
        compilers: Vec::new(),
    };
    for (n, line) in src.lines().enumerate() {
        let l = line.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let c: Vec<&str> = l.split('|').map(str::trim).collect();
        let bad = || Error(format!("toolchains line {}: bad line", n + 1));
        if c[0] == "flags" {
            t.flags = c
                .get(1)
                .ok_or_else(bad)?
                .split_whitespace()
                .map(String::from)
                .collect();
            continue;
        }
        let idx = match t.compilers.iter().position(|x| x.name == c[0]) {
            Some(i) => i,
            None => {
                t.compilers.push(Compiler {
                    name: c[0].to_string(),
                    driver: PathBuf::new(),
                    version: String::new(),
                    pins: Vec::new(),
                });
                t.compilers.len() - 1
            }
        };
        let cc = &mut t.compilers[idx];
        match c.as_slice() {
            [_, "version", v] => cc.version = v.to_string(),
            [_, role, path, sha] if sha.len() == 64 => {
                if *role == "driver" {
                    cc.driver = expand(path);
                }
                cc.pins
                    .push((role.to_string(), expand(path), sha.to_string()));
            }
            _ => return Err(bad()),
        }
    }
    for cc in &t.compilers {
        if cc.driver.as_os_str().is_empty() || cc.version.is_empty() {
            return err(format!("compiler {} needs a driver and a version", cc.name));
        }
    }
    if t.flags.is_empty() {
        return err("toolchains.txt has no flags line");
    }
    Ok(t)
}

/// The sha256 of a file (`sha256sum`).
pub fn sha256(p: &Path) -> Result<String, Error> {
    let out = io(p, Command::new("sha256sum").arg(p).output())?;
    if !out.status.success() {
        return err(format!("sha256sum {} failed", p.display()));
    }
    let s = String::from_utf8_lossy(&out.stdout);
    s.split_whitespace()
        .next()
        .filter(|h| h.len() == 64)
        .map(String::from)
        .ok_or_else(|| Error("bad sha256sum output".into()))
}

/// One program directory of the index.
pub struct Shape {
    pub dir: String,
    pub spec: Spec,
}

/// Read `index.txt` and every specification.
pub fn shapes(root: &Path) -> Result<Vec<Shape>, Error> {
    let ip = root.join("index.txt");
    let idx = io(&ip, std::fs::read_to_string(&ip))?;
    let mut out = Vec::new();
    for l in idx.lines() {
        let l = l.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let sp = root.join(l).join("litmus.txt");
        let src = io(&sp, std::fs::read_to_string(&sp))?;
        let spec = Spec::parse(&src).map_err(|e| Error(format!("{}: {}", sp.display(), e.0)))?;
        out.push(Shape {
            dir: l.to_string(),
            spec,
        });
    }
    Ok(out)
}

/// The object path of (shape, variant, compiler), relative to the root.
pub fn object_rel(dir: &str, v: Variant, cc: &str) -> String {
    format!("{dir}/obj/{}.{cc}.o", v.name())
}

/// Parse `objects.sha256` (`sha256sum` format, paths relative to the root).
fn read_manifest(root: &Path) -> Result<BTreeMap<String, String>, Error> {
    let p = root.join("objects.sha256");
    let s = io(&p, std::fs::read_to_string(&p))?;
    let mut m = BTreeMap::new();
    for l in s.lines().filter(|l| !l.trim().is_empty()) {
        let (h, f) = l
            .split_once("  ")
            .ok_or_else(|| Error(format!("bad manifest line `{l}`")))?;
        m.insert(f.to_string(), h.to_string());
    }
    Ok(m)
}

/// Refuse unless every pinned compiler file has its sha256 and every driver prints its
/// pinned version line.
pub fn verify_toolchains(tc: &Toolchains) -> Result<(), Error> {
    for cc in &tc.compilers {
        for (role, path, want) in &cc.pins {
            let got = sha256(path)?;
            if &got != want {
                return err(format!(
                    "{} {role} {}: sha256 {got}, pinned {want}",
                    cc.name,
                    path.display()
                ));
            }
        }
        let out = io(
            &cc.driver,
            Command::new(&cc.driver).arg("--version").output(),
        )?;
        let first = String::from_utf8_lossy(&out.stdout)
            .lines()
            .next()
            .unwrap_or("")
            .to_string();
        if first != cc.version {
            return err(format!(
                "{}: version `{first}`, pinned `{}`",
                cc.name, cc.version
            ));
        }
    }
    Ok(())
}

/// Compile every (program, variant, compiler) into `obj/` and write `objects.sha256`; with
/// `check`, compile into `tmp` and fail unless every object is byte-identical to the
/// committed one. Refuses to run unless every pinned compiler file has its sha256.
pub fn compile(root: &Path, check: bool, tmp: &Path) -> Result<usize, Error> {
    let tp = root.join("toolchains.txt");
    let tc = parse_toolchains(&io(&tp, std::fs::read_to_string(&tp))?)?;
    verify_toolchains(&tc)?;
    let mut manifest = String::new();
    let mut n = 0;
    for sh in shapes(root)? {
        let dir = root.join(&sh.dir);
        for v in VARIANTS {
            for cc in &tc.compilers {
                let rel = object_rel(&sh.dir, v, &cc.name);
                let dest = if check {
                    tmp.join(format!("{n}.o"))
                } else {
                    let p = root.join(&rel);
                    if let Some(d) = p.parent() {
                        io(d, std::fs::create_dir_all(d))?;
                    }
                    p
                };
                let dest_abs = if dest.is_absolute() {
                    dest.clone()
                } else {
                    io(&dest, std::env::current_dir())?.join(&dest)
                };
                let st = io(
                    &cc.driver,
                    Command::new(&cc.driver)
                        .current_dir(&dir)
                        .args(&tc.flags)
                        .arg(format!("-DMODE={}", v.macro_value()))
                        .arg("-c")
                        .arg(&sh.spec.source)
                        .arg("-o")
                        .arg(&dest_abs)
                        .status(),
                )?;
                if !st.success() {
                    return err(format!("{} failed on {rel}", cc.name));
                }
                if check {
                    let a = io(&dest_abs, std::fs::read(&dest_abs))?;
                    let bp = root.join(&rel);
                    let b = io(&bp, std::fs::read(&bp))?;
                    let _ = std::fs::remove_file(&dest_abs);
                    if a != b {
                        return err(format!("{rel}: recompiled object differs"));
                    }
                }
                let h = sha256(&root.join(&rel))?;
                let _ = writeln!(manifest, "{h}  {rel}");
                n += 1;
            }
        }
    }
    let mp = root.join("objects.sha256");
    if check {
        if io(&mp, std::fs::read_to_string(&mp))? != manifest {
            return err("objects.sha256 is out of date");
        }
    } else {
        io(&mp, std::fs::write(&mp, manifest))?;
    }
    Ok(n)
}

/// One ingested and checked test.
pub struct Test {
    pub name: String,
    pub shape: String,
    pub variant: Variant,
    pub compiler: String,
    pub object: String,
    pub object_sha: String,
    pub source: String,
    pub source_sha: String,
    pub ing: Ingested,
    pub maps: Vec<ThreadMap>,
    pub tso: checker::Outcome,
    pub sc: checker::Outcome,
    pub c11: Option<(String, String)>,
}

/// Ingest and check one object.
#[allow(clippy::too_many_arguments)]
pub fn ingest_one(
    obj_path: &Path,
    spec: &Spec,
    v: Variant,
    compiler: &str,
    shape: &str,
    rel_obj: &str,
    rel_src: &str,
    src_path: &Path,
    objdump: &Path,
    tmp: &Path,
) -> Result<Test, Error> {
    let bytes = io(obj_path, std::fs::read(obj_path))?;
    let obj = Object::parse(bytes).map_err(|e| Error(format!("{rel_obj}: {}", e.0)))?;
    let ctx = |e: Error| Error(format!("{rel_obj}: {}", e.0));
    let ing = ingest::ingest(&obj, spec, objdump, tmp).map_err(ctx)?;
    let maps = ingest::map_accesses(spec, v, &ing).map_err(ctx)?;
    let tso = checker::check(&ing.model, Mm::Tso)
        .map_err(|e| Error(format!("{rel_obj}: outside the checker's scope: {}", e.0)))?;
    let sc = checker::check(&ing.model, Mm::Sc)
        .map_err(|e| Error(format!("{rel_obj}: outside the checker's scope: {}", e.0)))?;
    if tso.verdict == Verdict::Forbidden && sc.verdict == Verdict::Allowed {
        return err(format!("{rel_obj}: SC allows what TSO forbids"));
    }
    let c11: Option<(String, String)> = spec
        .c11
        .iter()
        .find(|(w, _, _)| *w == v)
        .map(|(_, a, b)| (a.clone(), b.clone()));
    // Enforce, rather than only report, that the compiled code of an atomic
    // variant exhibits no witness the (hand-recorded) C11 verdict forbids.
    if let Some((w, _)) = &c11
        && w == "forbidden"
        && tso.verdict == Verdict::Allowed
    {
        return err(format!(
            "{rel_obj}: x86-TSO allows the witness that C11 forbids for `{}`",
            v.name()
        ));
    }
    Ok(Test {
        name: format!("{}+{}@{compiler}", spec.name, v.name()),
        shape: shape.to_string(),
        variant: v,
        compiler: compiler.to_string(),
        object: rel_obj.to_string(),
        object_sha: sha256(obj_path)?,
        source: rel_src.to_string(),
        source_sha: sha256(src_path)?,
        ing,
        maps,
        tso,
        sc,
        c11,
    })
}

/// Ingest every committed object (checking it against `objects.sha256`).
pub fn ingest_all(root: &Path, objdump: &Path, tmp: &Path) -> Result<Vec<Test>, Error> {
    let tp = root.join("toolchains.txt");
    let tc = parse_toolchains(&io(&tp, std::fs::read_to_string(&tp))?)?;
    let manifest = read_manifest(root)?;
    let mut out = Vec::new();
    for sh in shapes(root)? {
        for v in VARIANTS {
            for cc in &tc.compilers {
                let rel = object_rel(&sh.dir, v, &cc.name);
                let p = root.join(&rel);
                let want = manifest
                    .get(&rel)
                    .ok_or_else(|| Error(format!("{rel} is not in objects.sha256")))?;
                if &sha256(&p)? != want {
                    return err(format!("{rel}: sha256 differs from objects.sha256"));
                }
                let src = root.join(&sh.dir).join(&sh.spec.source);
                out.push(ingest_one(
                    &p,
                    &sh.spec,
                    v,
                    &cc.name,
                    &sh.dir,
                    &format!("examples/litmus-c/{rel}"),
                    &format!("examples/litmus-c/{}/{}", sh.dir, sh.spec.source),
                    &src,
                    objdump,
                    tmp,
                )?);
            }
        }
    }
    let mut names = BTreeSet::new();
    for t in &out {
        if !names.insert(t.name.clone()) {
            return err(format!("duplicate test name {}", t.name));
        }
    }
    Ok(out)
}

fn outcome(t: &Test, f: &Final) -> String {
    let regs = vec!["[]"; t.ing.threads.len()].join(",");
    let mem: Vec<String> = t
        .ing
        .layout
        .iter()
        .zip(&f.mem)
        .map(|((l, _, _), v)| format!("\"{}\"", hex_bytes(u128::from(*v), l.size)))
        .collect();
    format!("{{\"regs\":[{regs}],\"mem\":[{}]}}", mem.join(","))
}

fn outcome_set(t: &Test, s: &BTreeSet<Final>) -> Vec<String> {
    let v: BTreeSet<String> = s.iter().map(|f| outcome(t, f)).collect();
    v.into_iter().collect()
}

fn hex(b: &[u8]) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

/// Render `c11.json` (the export format read by `litmus-run`).
pub fn render_export(tests: &[Test], provenance: &[String]) -> String {
    let mut s = String::from("{\n\"format\": \"silmaril-litmus-x86-export/1\",\n");
    s.push_str("\"generated_by\": \"tools/litmus-x86 c11 ingest (do not edit)\",\n");
    s.push_str("\"allowed_source\": \"litmus-x86 checker (x86tso.cat transcription, tested not proved) on the IR lifted from objdump's reading of the compiled bytes; not herd7, not Lean\",\n");
    s.push_str("\"lean_module\": null,\n");
    let p: Vec<String> = provenance.iter().map(|p| json_str(p)).collect();
    let _ = writeln!(s, "\"provenance\": [{}],", p.join(", "));
    s.push_str("\"tests\": [");
    for (i, t) in tests.iter().enumerate() {
        s.push_str(if i == 0 { "\n" } else { ",\n" });
        let tso = Some(t.tso.verdict);
        let _ = writeln!(
            s,
            "  {{\"name\": {}, \"path\": {}, \"coverage\": \"tso\", \"quant\": \"exists\", \"tso\": {}, \"sc\": {}, \"xl\": {},",
            json_str(&t.name),
            json_str(&format!("{}#MODE={}", t.source, t.variant.macro_value())),
            verdict(tso),
            verdict(Some(t.sc.verdict)),
            verdict(tso)
        );
        let _ = writeln!(
            s,
            "   \"compiler\": {}, \"variant\": {}, \"object\": {},",
            json_str(&t.compiler),
            json_str(t.variant.name()),
            json_str(&t.object)
        );
        let locs: Vec<String> = t
            .ing
            .layout
            .iter()
            .map(|(l, _, _)| {
                format!(
                    "{{\"name\": {}, \"addr\": \"0x{:x}\", \"size\": {}, \"init\": \"{}\"}}",
                    json_str(&l.name),
                    l.addr,
                    l.size,
                    hex_bytes(l.init, l.size)
                )
            })
            .collect();
        let _ = writeln!(s, "   \"locs\": [{}],", locs.join(", "));
        s.push_str("   \"threads\": [");
        for (k, th) in t.ing.threads.iter().enumerate() {
            s.push_str(if k == 0 { "\n" } else { ",\n" });
            let cs: Vec<String> = th
                .insns
                .iter()
                .map(|mi| {
                    format!(
                        "{{\"asm\": {}, \"bytes\": \"{}\"}}",
                        json_str(&mi.asm),
                        hex(&mi.bytes)
                    )
                })
                .collect();
            let _ = write!(
                s,
                "    {{\"regs\": [], \"observe\": [], \"code_base\": \"0x{:x}\",\n     \"code\": [{}]}}",
                th.code_base,
                cs.join(", ")
            );
        }
        s.push_str("],\n");
        let _ = writeln!(s, "   \"witness\": {},", cond(&t.ing.model.witness()));
        let _ = write!(
            s,
            "   \"allowed\": {{\n    \"tso\": [\n      {}],\n    \"sc\": [\n      {}]}}}}",
            outcome_set(t, &t.tso.states).join(",\n      "),
            outcome_set(t, &t.sc.states).join(",\n      ")
        );
    }
    s.push_str("\n]\n}\n");
    s
}

fn opt_str(o: Option<&str>) -> String {
    o.map_or("null".into(), json_str)
}

/// The per-compiler table of x86 forms: (compiler, "kind.mode") -> forms.
pub fn mapping_table(tests: &[Test]) -> BTreeMap<(String, String), BTreeSet<String>> {
    let mut m: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    for t in tests {
        for tm in &t.maps {
            for a in &tm.accesses {
                if a.access.result {
                    continue;
                }
                let key = format!("{}.{}", a.access.kind.name(), a.access.mode.name());
                m.entry((t.compiler.clone(), key))
                    .or_default()
                    .insert(a.form.clone());
            }
        }
    }
    m
}

/// Render `c11-meta.json`, the sidecar for `c11cir`.
pub fn render_meta(tests: &[Test], tc: &Toolchains, provenance: &[String]) -> String {
    let mut s = String::from("{\n\"format\": \"silmaril-litmus-c11-meta/1\",\n");
    s.push_str("\"generated_by\": \"tools/litmus-x86 c11 ingest (do not edit)\",\n");
    let p: Vec<String> = provenance.iter().map(|p| json_str(p)).collect();
    let _ = writeln!(s, "\"provenance\": [{}],", p.join(", "));
    let fl: Vec<String> = tc.flags.iter().map(|f| json_str(f)).collect();
    let _ = writeln!(s, "\"flags\": [{}],", fl.join(", "));
    s.push_str("\"compilers\": [");
    for (i, cc) in tc.compilers.iter().enumerate() {
        let pins: Vec<String> = cc
            .pins
            .iter()
            .map(|(r, p, h)| {
                format!(
                    "{{\"role\": {}, \"file\": {}, \"sha256\": {}}}",
                    json_str(r),
                    json_str(&p.file_name().unwrap_or_default().to_string_lossy()),
                    json_str(h)
                )
            })
            .collect();
        let _ = write!(
            s,
            "{}\n  {{\"name\": {}, \"version\": {}, \"pins\": [{}]}}",
            if i == 0 { "" } else { "," },
            json_str(&cc.name),
            json_str(&cc.version),
            pins.join(", ")
        );
    }
    s.push_str("],\n");
    s.push_str("\"variants\": {");
    let vs: Vec<String> = VARIANTS
        .iter()
        .map(|v| {
            let [a, b, c] = ingest::variant_modes(*v);
            format!(
                "{}: {{\"MODE\": {}, \"st\": \"{a}\", \"ld\": \"{b}\", \"rmw\": \"{c}\", \"fence\": \"sc\"}}",
                json_str(v.name()),
                v.macro_value()
            )
        })
        .collect();
    let _ = writeln!(s, "{}}},", vs.join(", "));
    s.push_str("\"mapping\": [");
    let table = mapping_table(tests);
    for (i, ((cc, key), forms)) in table.iter().enumerate() {
        let f: Vec<String> = forms.iter().map(|x| json_str(x)).collect();
        let _ = write!(
            s,
            "{}\n  {{\"compiler\": {}, \"access\": {}, \"x86\": [{}]}}",
            if i == 0 { "" } else { "," },
            json_str(cc),
            json_str(key),
            f.join(", ")
        );
    }
    s.push_str("],\n\"tests\": [");
    for (i, t) in tests.iter().enumerate() {
        s.push_str(if i == 0 { "\n" } else { ",\n" });
        let _ = writeln!(
            s,
            "  {{\"name\": {}, \"shape\": {}, \"variant\": {}, \"compiler\": {},",
            json_str(&t.name),
            json_str(&t.shape),
            json_str(t.variant.name()),
            json_str(&t.compiler)
        );
        let _ = writeln!(
            s,
            "   \"source\": {{\"path\": {}, \"sha256\": {}, \"MODE\": {}}}, \"object\": {{\"path\": {}, \"sha256\": {}}},",
            json_str(&t.source),
            json_str(&t.source_sha),
            t.variant.macro_value(),
            json_str(&t.object),
            json_str(&t.object_sha)
        );
        let lay: Vec<String> = t
            .ing
            .layout
            .iter()
            .map(|(l, sec, role)| {
                format!(
                    "{{\"symbol\": {}, \"section\": {}, \"role\": \"{}\", \"addr\": \"0x{:x}\", \"size\": {}, \"init\": \"0x{:x}\"}}",
                    json_str(&l.name),
                    json_str(sec),
                    match role {
                        crate::cspec::Role::Shared => "shared",
                        crate::cspec::Role::Result => "result",
                    },
                    l.addr,
                    l.size,
                    l.init
                )
            })
            .collect();
        let _ = writeln!(s, "   \"layout\": [{}],", lay.join(", "));
        let stack: Vec<String> = t.ing.model.locs[t.ing.layout.len()..]
            .iter()
            .map(|l| format!("{{\"name\": {}, \"size\": {}}}", json_str(&l.name), l.size))
            .collect();
        let _ = writeln!(s, "   \"stack_slots\": [{}],", stack.join(", "));
        s.push_str("   \"threads\": [");
        for (k, (th, tm)) in t.ing.threads.iter().zip(&t.maps).enumerate() {
            s.push_str(if k == 0 { "\n" } else { ",\n" });
            let rel: Vec<String> = th
                .relocs
                .iter()
                .map(|(o, sym, ty, a, v)| {
                    format!(
                        "{{\"off\": {o}, \"symbol\": {}, \"type\": {ty}, \"addend\": {a}, \"value\": {v}}}",
                        json_str(sym)
                    )
                })
                .collect();
            let ins: Vec<String> = th
                .insns
                .iter()
                .map(|mi| {
                    format!(
                        "\n       {{\"off\": {}, \"bytes\": \"{}\", \"asm\": {}, \"lifted\": {}}}",
                        mi.off,
                        hex(&mi.bytes),
                        json_str(&mi.asm),
                        json_str(&mi.lifted)
                    )
                })
                .collect();
            let acc: Vec<String> = tm
                .accesses
                .iter()
                .map(|a| {
                    let x = &a.access;
                    let xs: Vec<String> = a.insns.iter().map(|i| i.to_string()).collect();
                    format!(
                        "\n       {{\"kind\": \"{}\", \"loc\": {}, \"mode\": \"{}\", \"value\": {}, \"value_of\": {}, \"op\": {}, \"result\": {}, \"x86\": [{}], \"form\": {}, \"in_order\": {}}}",
                        x.kind.name(),
                        opt_str(x.loc.as_deref()),
                        x.mode.name(),
                        x.value.map_or("null".into(), |v| v.to_string()),
                        opt_str(x.value_of.as_deref()),
                        opt_str(x.rmw_op),
                        x.result,
                        xs.join(","),
                        json_str(&a.form),
                        a.in_order
                    )
                })
                .collect();
            let ex: Vec<String> = tm.extra.iter().map(|i| i.to_string()).collect();
            let _ = write!(
                s,
                "    {{\"func\": {}, \"section\": {}, \"code_base\": \"0x{:x}\", \"size\": {}, \"ret_dropped\": true,\n     \"relocs\": [{}],\n     \"insns\": [{}],\n     \"c11\": [{}],\n     \"extra\": [{}]}}",
                json_str(&th.func),
                json_str(&th.section),
                th.code_base,
                th.size,
                rel.join(", "),
                ins.join(","),
                acc.join(","),
                ex.join(",")
            );
        }
        s.push_str("],\n");
        let _ = writeln!(
            s,
            "   \"x86\": {{\"tso\": {}, \"sc\": {}, \"tso_outcomes\": {}, \"sc_outcomes\": {}, \"tso_executions\": {}, \"sc_executions\": {}}},",
            verdict(Some(t.tso.verdict)),
            verdict(Some(t.sc.verdict)),
            outcome_set(t, &t.tso.states).len(),
            outcome_set(t, &t.sc.states).len(),
            t.tso.executions,
            t.sc.executions
        );
        match &t.c11 {
            Some((v, note)) => {
                let _ = write!(
                    s,
                    "   \"c11_expected\": {{\"verdict\": {}, \"note\": {}, \"basis\": \"literature, recorded by hand; not computed\"}}}}",
                    json_str(v),
                    json_str(note)
                );
            }
            None => s.push_str("   \"c11_expected\": null}"),
        }
    }
    s.push_str("\n]\n}\n");
    s
}

/// The x86 verdict table as Markdown (for the notes).
pub fn summary(tests: &[Test]) -> String {
    let mut s = String::from(
        "| test | x86-TSO | SC | TSO outcomes | C11 expected | sc/fence forms |\n|---|---|---|---|---|---|\n",
    );
    for t in tests {
        let forms: BTreeSet<String> = t
            .maps
            .iter()
            .flat_map(|m| m.accesses.iter())
            .filter(|a| !a.access.result && a.access.kind != AKind::Load)
            .map(|a| {
                format!(
                    "{}.{}: {}",
                    a.access.kind.name(),
                    a.access.mode.name(),
                    a.form
                )
            })
            .collect();
        let _ = writeln!(
            s,
            "| {} | {} | {} | {} | {} | {} |",
            t.name,
            t.tso.verdict.name(),
            t.sc.verdict.name(),
            outcome_set(t, &t.tso.states).len(),
            t.c11.as_ref().map_or("-", |(v, _)| v.as_str()),
            forms.into_iter().collect::<Vec<_>>().join("; ")
        );
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/litmus-c")
    }

    fn scratch(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("litmus-x86-{tag}-{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    /// The committed exports are what `c11 ingest` produces from the committed objects
    /// (needs GNU objdump).
    #[test]
    fn c11_exports_up_to_date() {
        let d = scratch("c11");
        let tests = ingest_all(&root(), Path::new("objdump"), &d).unwrap();
        let _ = std::fs::remove_dir_all(&d);
        assert_eq!(tests.len(), 64);
        let ex =
            std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("export/c11.json"))
                .unwrap();
        // The provenance lines are rendered by main.rs; compare the test bodies only.
        let body = |s: &str| s[s.find("\"tests\"").unwrap()..].to_string();
        assert_eq!(body(&render_export(&tests, &[])), body(&ex));
        // Spot checks: the seq_cst store mapping, gcc's reordering of plain LB, and verdicts.
        let get = |n: &str| tests.iter().find(|t| t.name == n).unwrap();
        for cc in ["gcc", "clang"] {
            let sb = get(&format!("SB+sc@{cc}"));
            assert_eq!(sb.maps[0].accesses[0].form, "xchg");
            assert_eq!(sb.tso.verdict, Verdict::Forbidden);
            assert_eq!(get(&format!("SB+rlx@{cc}")).tso.verdict, Verdict::Allowed);
            assert_eq!(
                get(&format!("Counter+na@{cc}")).tso.verdict,
                Verdict::Allowed
            );
            assert_eq!(
                get(&format!("Counter+rlx@{cc}")).tso.verdict,
                Verdict::Forbidden
            );
        }
        let lb = get("LB+na@gcc");
        assert!(!lb.maps[0].accesses[2].in_order);
        assert_eq!(lb.tso.verdict, Verdict::Allowed);
        assert_eq!(get("LB+na@clang").tso.verdict, Verdict::Forbidden);
        // Data relocated to the fixed page: P0 of SB stores to x = 0x10000.
        let t = get("SB+rlx@gcc");
        let mi = &t.ing.threads[0].insns[0];
        assert_eq!(mi.lifted, "movl $0x1,(x)");
        let disp = i32::from_le_bytes(mi.bytes[2..6].try_into().unwrap()) as i64;
        assert_eq!(0x40_0000 + mi.bytes.len() as i64 + disp, 0x10000);
    }

    /// An atomic access without an x86 counterpart is an error, not a silent mismatch.
    #[test]
    fn missing_atomic_access_is_rejected() {
        let d = scratch("c11-neg");
        let spec = Spec::parse(
            "name Counter\nsource counter.c\nloc x\nresult r1\nthread P0\nst x 1\nthread P1\nfaa x 1 r1\n",
        )
        .unwrap();
        let p = root().join("counter/obj/rlx.gcc.o");
        let r = ingest_one(
            &p,
            &spec,
            Variant::Rlx,
            "gcc",
            "counter",
            "o",
            "s",
            &p,
            Path::new("objdump"),
            &d,
        );
        let _ = std::fs::remove_dir_all(&d);
        let e = r.err().expect("must fail").0;
        assert!(e.contains("no x86 counterpart"), "{e}");
    }

    /// Mutants: weaker code ingested under a stronger specification is rejected.
    #[test]
    fn weakened_code_is_rejected() {
        let d = scratch("c11-mut");
        let run = |shape: &str, obj: &str, v: Variant| {
            let spec = Spec::parse(
                &std::fs::read_to_string(root().join(shape).join("litmus.txt")).unwrap(),
            )
            .unwrap();
            let p = root().join(shape).join("obj").join(obj);
            ingest_one(
                &p,
                &spec,
                v,
                "gcc",
                shape,
                "o",
                "s",
                &p,
                Path::new("objdump"),
                &d,
            )
        };
        // seq_cst stores compiled as plain `mov` (the rlx object under the sc spec).
        for cc in ["gcc", "clang"] {
            let e = run("sb", &format!("rlx.{cc}.o"), Variant::Sc)
                .err()
                .expect("sb")
                .0;
            assert!(e.contains("seq_cst store"), "{e}");
            let e = run("2+2w", &format!("rlx.{cc}.o"), Variant::Sc)
                .err()
                .expect("2+2w")
                .0;
            assert!(e.contains("seq_cst store"), "{e}");
        }
        // The plain (racy) counter is not accepted as an atomic one.
        assert!(run("counter", "na.gcc.o", Variant::Rlx).is_err());
        // A specification whose constants differ from the code's is rejected.
        for (shape, from, to) in [
            ("2+2w", "st y 2", "st y 3"),
            ("counter", "faa x 1\n", "faa x 2\n"),
        ] {
            let txt = std::fs::read_to_string(root().join(shape).join("litmus.txt")).unwrap();
            assert!(txt.contains(from));
            let spec = Spec::parse(&txt.replacen(from, to, 1)).unwrap();
            for cc in ["gcc", "clang"] {
                let p = root().join(shape).join("obj").join(format!("sc.{cc}.o"));
                let e = ingest_one(
                    &p,
                    &spec,
                    Variant::Sc,
                    cc,
                    shape,
                    "o",
                    "s",
                    &p,
                    Path::new("objdump"),
                    &d,
                )
                .err()
                .expect("value mutant")
                .0;
                assert!(e.contains("does not write the value"), "{e}");
            }
        }
        // A store the specification does not mention is an error in an atomic variant.
        let txt = std::fs::read_to_string(root().join("mp/litmus.txt")).unwrap();
        let spec = Spec::parse(&txt.replacen("st y 1\n", "", 1)).unwrap();
        let p = root().join("mp/obj/rlx.clang.o");
        let e = ingest_one(
            &p,
            &spec,
            Variant::Rlx,
            "clang",
            "mp",
            "o",
            "s",
            &p,
            Path::new("objdump"),
            &d,
        )
        .err()
        .expect("extra-store mutant")
        .0;
        assert!(e.contains("not accounted for"), "{e}");
        // A C11-forbidden witness that the compiled code allows is an error.
        let txt = std::fs::read_to_string(root().join("sb/litmus.txt")).unwrap();
        let spec = Spec::parse(&txt.replacen("c11 rlx allowed", "c11 rlx forbidden", 1)).unwrap();
        let p = root().join("sb/obj/rlx.gcc.o");
        let e = ingest_one(
            &p,
            &spec,
            Variant::Rlx,
            "gcc",
            "sb",
            "o",
            "s",
            &p,
            Path::new("objdump"),
            &d,
        )
        .err()
        .expect("verdict mutant")
        .0;
        assert!(e.contains("C11 forbids"), "{e}");
        let _ = std::fs::remove_dir_all(&d);
    }

    #[test]
    fn toolchains() {
        let t = parse_toolchains(
            "# c\nflags | -O2 -g0\ngcc | version | gcc 13\ngcc | driver | /usr/bin/gcc | 0000000000000000000000000000000000000000000000000000000000000000\n",
        )
        .unwrap();
        assert_eq!(t.flags, vec!["-O2", "-g0"]);
        assert_eq!(t.compilers[0].driver, PathBuf::from("/usr/bin/gcc"));
        assert!(parse_toolchains("gcc | version | x\n").is_err());
    }
}
