//! `syswrap-gen`: find the system call wrappers of an x86-64 C library and write their
//! `Silmaril.Libc.SysWrap` contracts as a Lean module.
//!
//! For every requested exported function (`name@version`), the bytes from its entry are matched
//! against the templates that `Silmaril.Libc.SysWrap.checkCode` accepts: an optional `endbr64`,
//! register moves (`mov`, `mov $imm`, `xor r32,r32`) with an optional `SINGLE_THREAD_P` test
//! (`cmpb $0, disp(%rip); je`), `syscall`, and one of the five tails (`errno64`, `errnoInt`,
//! `errnoLong`, `errnoZero`, `raw`). The matcher computes the description (`Desc`: number,
//! kernel arguments, convention, offsets); the Lean kernel re-checks all of it with the machine's
//! own decoder, so a wrong match here makes the build fail, never a wrong theorem.
//!
//! The kernel argument count of each call (`--syscalls`, `data/x86_64-syscalls.tsv`) fixes how
//! many kernel argument registers the description states.
//!
//! Usage (`scripts/syswrap/gen.sh` runs it for the three glibc pins):
//!   syswrap-gen --lib libc.so.6 --pin PIN --title TITLE --namespace NS --symbols IDS \
//!     --syscalls data/x86_64-syscalls.tsv --defs Defs.lean --defs-module MOD --thms Thms.lean \
//!     --report report.tsv
//!
//! `IDS` lists one `name@version` per line (`#` comments), optionally followed by a tab and the
//! kernel call a classification expects (only reported). The report has one row per requested
//! symbol: `id address status nr syscall expected conv single detail`, with status `ok`
//! (proved), `ifunc`, `missing` or `nomatch` (the first instruction or tail outside the
//! templates, in `detail`).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::process::ExitCode;

// ---------------------------------------------------------------- SHA-256

fn sha256(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bits.to_be_bytes());
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [
                t1.wrapping_add(t2),
                v[0],
                v[1],
                v[2],
                v[3].wrapping_add(t1),
                v[4],
                v[5],
                v[6],
            ];
        }
        for i in 0..8 {
            h[i] = h[i].wrapping_add(v[i]);
        }
    }
    h.iter().map(|x| format!("{x:08x}")).collect()
}

// ---------------------------------------------------------------- ELF

fn u16le(b: &[u8], o: usize) -> u64 {
    u16::from_le_bytes([b[o], b[o + 1]]) as u64
}
fn u32le(b: &[u8], o: usize) -> u64 {
    u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) as u64
}
fn u64le(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}

struct Shdr {
    typ: u64,
    offset: u64,
    size: u64,
    link: u64,
}

struct Sym {
    name: String,
    ver: String,
    typ: u8,
    value: u64,
    size: u64,
}

fn cstr(b: &[u8], o: usize) -> String {
    let end = b[o..]
        .iter()
        .position(|&c| c == 0)
        .map(|p| o + p)
        .unwrap_or(b.len());
    String::from_utf8_lossy(&b[o..end]).into_owned()
}

fn read_syms(b: &[u8]) -> Result<Vec<Sym>, String> {
    if &b[0..4] != b"\x7fELF" || b[4] != 2 || b[5] != 1 || u16le(b, 18) != 62 {
        return Err("not an ELF64 little-endian x86-64 file".into());
    }
    let shoff = u64le(b, 0x28) as usize;
    let shentsize = u16le(b, 0x3a) as usize;
    let shnum = u16le(b, 0x3c) as usize;
    let sh: Vec<Shdr> = (0..shnum)
        .map(|i| {
            let o = shoff + i * shentsize;
            Shdr {
                typ: u32le(b, o + 4),
                offset: u64le(b, o + 24),
                size: u64le(b, o + 32),
                link: u32le(b, o + 40),
            }
        })
        .collect();
    let dynsym = sh.iter().find(|s| s.typ == 11).ok_or("no .dynsym")?;
    let dynstr = &sh[dynsym.link as usize];
    let versym = sh.iter().find(|s| s.typ == 0x6fffffff);
    let verdef = sh.iter().find(|s| s.typ == 0x6ffffffd);
    // version index -> name
    let mut vnames: BTreeMap<u64, String> = BTreeMap::new();
    if let Some(vd) = verdef {
        let mut o = vd.offset as usize;
        loop {
            let ndx = u16le(b, o + 4);
            let aux = u32le(b, o + 12) as usize;
            let next = u32le(b, o + 16) as usize;
            let name_off = u32le(b, o + aux) as usize;
            vnames.insert(ndx, cstr(b, dynstr.offset as usize + name_off));
            if next == 0 {
                break;
            }
            o += next;
        }
    }
    let n = (dynsym.size / 24) as usize;
    let mut out = Vec::new();
    for k in 0..n {
        let o = dynsym.offset as usize + 24 * k;
        let name = cstr(b, dynstr.offset as usize + u32le(b, o) as usize);
        let info = b[o + 4];
        let shndx = u16le(b, o + 6);
        let value = u64le(b, o + 8);
        let size = u64le(b, o + 16);
        if shndx == 0 || name.is_empty() {
            continue;
        }
        let typ = info & 0xf;
        if typ != 2 && typ != 10 {
            continue;
        }
        let ver = match versym {
            Some(vs) => {
                let v = u16le(b, vs.offset as usize + 2 * k) & 0x7fff;
                vnames.get(&v).cloned().unwrap_or_default()
            }
            None => String::new(),
        };
        out.push(Sym {
            name,
            ver,
            typ,
            value,
            size,
        });
    }
    Ok(out)
}

/// File offset of a virtual address (the `PT_LOAD` that maps it).
fn file_off(b: &[u8], vaddr: u64) -> Option<u64> {
    let phoff = u64le(b, 0x20) as usize;
    let phentsize = u16le(b, 0x36) as usize;
    let phnum = u16le(b, 0x38) as usize;
    (0..phnum).find_map(|i| {
        let o = phoff + i * phentsize;
        if u32le(b, o) != 1 {
            return None;
        }
        let off = u64le(b, o + 8);
        let va = u64le(b, o + 16);
        let filesz = u64le(b, o + 32);
        (vaddr >= va && vaddr < va + filesz).then(|| vaddr - va + off)
    })
}

// ---------------------------------------------------------------- the templates

const REGS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const KEPT: [usize; 7] = [3, 5, 12, 13, 14, 15, 4];
const KERNEL_ARGS: [usize; 6] = [7, 6, 2, 10, 8, 9];

#[derive(Clone, Copy, PartialEq, Debug)]
enum Val {
    Reg(usize),
    Low(usize),
    Const(u64),
}

impl Val {
    fn low32(self) -> Val {
        match self {
            Val::Reg(r) | Val::Low(r) => Val::Low(r),
            Val::Const(w) => Val::Const(w & 0xffff_ffff),
        }
    }
    fn lean(self) -> String {
        match self {
            Val::Reg(r) => format!(".reg .{}", REGS[r]),
            Val::Low(r) => format!(".low .{}", REGS[r]),
            Val::Const(w) => format!(".const {w:#x}"),
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Conv {
    Errno64,
    ErrnoInt,
    ErrnoLong,
    ErrnoZero,
    Raw,
}

impl Conv {
    fn lean(self) -> &'static str {
        match self {
            Conv::Errno64 => "errno64",
            Conv::ErrnoInt => "errnoInt",
            Conv::ErrnoLong => "errnoLong",
            Conv::ErrnoZero => "errnoZero",
            Conv::Raw => "raw",
        }
    }
}

struct Found {
    nr: u64,
    args: [Val; 6],
    conv: Conv,
    sys_off: usize,
    errno_got: u64,
    single: Option<u64>,
    /// The kernel argument count of the call (`args[..nargs]` are stated).
    nargs: usize,
    /// The bytes the checker reads: from the entry to the end of the last instruction checked.
    len: usize,
}

fn sext8(b: u8) -> i64 {
    b as i8 as i64
}
fn sext32(b: &[u8]) -> i64 {
    i32::from_le_bytes(b[0..4].try_into().unwrap()) as i64
}

fn hex(w: u64) -> String {
    format!("{w:#x}")
}

/// Match the bytes of one function from its entry. `arity` gives the kernel argument count of a
/// call number.
fn find(code: &[u8], arity: &dyn Fn(u64) -> Option<usize>) -> Result<Found, String> {
    let at = |o: usize, n: usize| -> Option<&[u8]> { code.get(o..o + n) };
    let mut sigma: [Val; 16] = core::array::from_fn(Val::Reg);
    let mut fl = false;
    let mut single = None;
    let mut o = 0usize;
    let scratch = |r: usize| !KEPT.contains(&r);
    let mut steps = 0;
    loop {
        steps += 1;
        if steps > 31 {
            return Err("pre:too-long".into());
        }
        let b = at(o, 2).ok_or("pre:eof")?;
        if b == [0x0f, 0x05] {
            break;
        }
        // endbr64
        if at(o, 4) == Some(&[0xf3, 0x0f, 0x1e, 0xfa]) {
            o += 4;
            continue;
        }
        // cmpb $0, disp(%rip): the SINGLE_THREAD_P test
        if code[o] == 0x80 && at(o + 1, 1) == Some(&[0x3d]) && at(o + 6, 1) == Some(&[0]) {
            let disp = sext32(at(o + 2, 4).ok_or("pre:eof")?);
            single = Some(((o + 7) as i64 + disp) as u64);
            fl = true;
            o += 7;
            continue;
        }
        // je rel8 after it (the multi-threaded path, not followed)
        if code[o] == 0x74 {
            if !fl {
                return Err("pre:je-without-test".into());
            }
            o += 2;
            continue;
        }
        let (rex, p) = match code[o] {
            x @ 0x40..=0x4f => (x, o + 1),
            _ => (0, o),
        };
        let w = rex & 8 != 0;
        let rr = ((rex >> 2) & 1) as usize * 8;
        let rb = (rex & 1) as usize * 8;
        let op = *code.get(p).ok_or("pre:eof")?;
        match op {
            // mov %src, %dst (89 /r, register form)
            0x89 => {
                let m = *code.get(p + 1).ok_or("pre:eof")? as usize;
                if m >> 6 != 3 || rex & 2 != 0 {
                    return Err(format!("pre:mov-mem@{o:#x}"));
                }
                let d = (m & 7) + rb;
                let s = ((m >> 3) & 7) + rr;
                if !scratch(d) {
                    return Err(format!("pre:writes-kept@{o:#x}"));
                }
                sigma[d] = if w { sigma[s] } else { sigma[s].low32() };
                o = p + 2;
            }
            // mov $imm32, %r32
            0xb8..=0xbf if !w => {
                let d = (op - 0xb8) as usize + rb;
                let imm = u32le(code.get(p + 1..p + 5).ok_or("pre:eof")?, 0);
                if !scratch(d) {
                    return Err(format!("pre:writes-kept@{o:#x}"));
                }
                sigma[d] = Val::Const(imm);
                o = p + 5;
            }
            // xor %r32, %r32
            0x31 if !w => {
                let m = *code.get(p + 1).ok_or("pre:eof")? as usize;
                let d = (m & 7) + rb;
                let s = ((m >> 3) & 7) + rr;
                if m >> 6 != 3 || d != s || rex & 2 != 0 {
                    return Err(format!("pre:xor@{o:#x}"));
                }
                if !scratch(d) {
                    return Err(format!("pre:writes-kept@{o:#x}"));
                }
                sigma[d] = Val::Const(0);
                fl = false;
                o = p + 2;
            }
            _ => {
                let n = code.len().min(o + 4);
                let bytes: String = code[o..n].iter().map(|b| format!("{b:02x}")).collect();
                return Err(format!("pre:{bytes}@{o:#x}"));
            }
        }
    }
    let sys_off = o;
    let nr = match sigma[0] {
        Val::Const(n) => n,
        _ => return Err("nr:not-constant".into()),
    };
    let n = arity(nr).ok_or_else(|| format!("nr:unknown-{nr}"))?;
    let args: [Val; 6] = core::array::from_fn(|i| sigma[KERNEL_ARGS[i]]);
    // the tail
    let p = sys_off + 2;
    let eq = |o: usize, bs: &[u8]| at(o, bs.len()) == Some(bs);
    let errblock = |e: usize| -> Result<u64, String> {
        // mov disp(%rip),%rcx|%rdx; neg %eax; mov %eax,%fs:(%rcx|%rdx)
        let (r, st) = if eq(e, &[0x48, 0x8b, 0x0d]) {
            (1, [0x64, 0x89, 0x01])
        } else if eq(e, &[0x48, 0x8b, 0x15]) {
            (2, [0x64, 0x89, 0x02])
        } else {
            return Err(format!("tail:no-got-load@{e:#x}"));
        };
        let _ = r;
        if !eq(e + 7, &[0xf7, 0xd8]) || !eq(e + 9, &st) {
            return Err(format!("tail:no-errno-store@{e:#x}"));
        }
        let disp = sext32(at(e + 3, 4).unwrap());
        Ok(((e + 7) as i64 + disp) as u64)
    };
    let target = |jo: usize| -> usize { (jo as i64 + 2 + sext8(code[jo + 1])) as usize };
    let (conv, errno_got, len) = if eq(p, &[0xc3]) {
        (Conv::Raw, 0, p + 1)
    } else if eq(p, &[0x48, 0x3d, 0x01, 0xf0, 0xff, 0xff, 0x73]) && eq(p + 8, &[0xc3]) {
        let e = target(p + 6);
        let g = errblock(e)?;
        if !eq(e + 12, &[0x48, 0x83, 0xc8, 0xff, 0xc3]) {
            return Err("tail:errno64-no-or".into());
        }
        (Conv::Errno64, g, (e + 17).max(p + 9))
    } else if eq(p, &[0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff, 0x77]) && eq(p + 8, &[0xc3]) {
        let e = target(p + 6);
        let g = errblock(e)?;
        if eq(e + 12, &[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]) {
            (Conv::ErrnoInt, g, (e + 18).max(p + 9))
        } else if eq(e + 12, &[0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xc3]) {
            (Conv::ErrnoLong, g, (e + 20).max(p + 9))
        } else {
            return Err("tail:errno-no-result".into());
        }
    } else if eq(p, &[0x3d, 0x00, 0xf0, 0xff, 0xff, 0x77]) && eq(p + 7, &[0x31, 0xc0, 0xc3]) {
        let e = target(p + 5);
        let g = errblock(e)?;
        if !eq(e + 12, &[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]) {
            return Err("tail:errnoZero-no-result".into());
        }
        (Conv::ErrnoZero, g, (e + 18).max(p + 10))
    } else {
        let n = code.len().min(p + 8);
        let bytes: String = code[p..n].iter().map(|b| format!("{b:02x}")).collect();
        return Err(format!("tail:{bytes}"));
    };
    if n > 6 {
        return Err("nr:arity>6".into());
    }
    Ok(Found {
        nr,
        args,
        nargs: n,
        conv,
        sys_off,
        errno_got,
        single,
        len,
    })
}

// ---------------------------------------------------------------- output

fn lean_bytes(code: &[u8], indent: &str) -> String {
    let mut out = String::new();
    let mut line = String::new();
    for (i, b) in code.iter().enumerate() {
        let item = format!("0x{b:02x}{}", if i + 1 < code.len() { "," } else { "" });
        if line.len() + item.len() + indent.len() > 99 {
            out.push_str(indent);
            out.push_str(line.trim_end());
            out.push('\n');
            line.clear();
        }
        line.push_str(&item);
        line.push(' ');
    }
    if !line.is_empty() {
        out.push_str(indent);
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

fn lean_desc(f: &Found) -> String {
    let args: Vec<String> = f.args[..f.nargs].iter().map(|v| v.lean()).collect();
    format!(
        "  nr := {}\n  args := [{}]\n  conv := .{}\n  sysOff := {}\n  errnoGot := {}\n  single := {}\n",
        f.nr,
        args.join(", "),
        f.conv.lean(),
        f.sys_off,
        hex(f.errno_got),
        match f.single {
            Some(s) => format!("some {}", hex(s)),
            None => "none".into(),
        }
    )
}

/// A docstring, wrapped at 100 columns.
fn doc(text: &str) -> String {
    let mut lines = vec![String::from("/--")];
    for w in text.split(' ') {
        let last = lines.last_mut().unwrap();
        if last.len() + 1 + w.len() > 100 - 3 {
            lines.push(w.to_string());
        } else {
            last.push(' ');
            last.push_str(w);
        }
    }
    let mut out = lines.join("\n");
    out.push_str(" -/\n");
    out
}

struct Row {
    id: String,
    expected: String,
    addr: Option<u64>,
    status: String,
    found: Option<Found>,
    detail: String,
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter()
        .position(|a| a == k)
        .and_then(|i| args.get(i + 1).cloned())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let need = |k: &str| -> String {
        arg(&args, k).unwrap_or_else(|| {
            eprintln!(
                "usage: syswrap-gen --lib LIB --pin PIN --title TITLE --namespace NS --symbols IDS \
                 --syscalls TABLE --defs DEFS.lean --defs-module MOD --thms THMS.lean --report R.tsv"
            );
            std::process::exit(2)
        })
    };
    let lib = need("--lib");
    let pin = need("--pin");
    let title = need("--title");
    let ns = need("--namespace");
    let syms_path = need("--symbols");
    let table_path = need("--syscalls");
    let defs_path = need("--defs");
    let defs_mod = need("--defs-module");
    let thms_path = need("--thms");
    let report_path = need("--report");
    let b = match fs::read(&lib) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("syswrap-gen: {lib}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let digest = sha256(&b);
    let syms = match read_syms(&b) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("syswrap-gen: {lib}: {e}");
            return ExitCode::FAILURE;
        }
    };
    // the syscall table: nr -> (name, nargs)
    let mut table: BTreeMap<u64, (String, usize)> = BTreeMap::new();
    for l in fs::read_to_string(&table_path)
        .expect("syscall table")
        .lines()
    {
        if l.starts_with('#') || l.trim().is_empty() {
            continue;
        }
        let p: Vec<&str> = l.split('\t').collect();
        table.insert(
            p[0].parse().unwrap(),
            (p[1].to_string(), p[2].parse().unwrap()),
        );
    }
    let arity = |nr: u64| table.get(&nr).map(|t| t.1);
    let mut rows = Vec::new();
    for l in fs::read_to_string(&syms_path).expect("symbols").lines() {
        let l = l.trim_end();
        if l.starts_with('#') || l.is_empty() {
            continue;
        }
        let mut it = l.split('\t');
        let id = it.next().unwrap().to_string();
        let expected = it.next().unwrap_or("").to_string();
        let (name, ver) = id.split_once('@').unwrap_or((&id, ""));
        let s = syms.iter().find(|s| s.name == name && s.ver == ver);
        let mut row = Row {
            id: id.clone(),
            expected,
            addr: None,
            status: String::new(),
            found: None,
            detail: String::new(),
        };
        match s {
            None => row.status = "missing".into(),
            Some(s) if s.typ == 10 => {
                row.addr = Some(s.value);
                row.status = "ifunc".into();
            }
            Some(s) => {
                row.addr = Some(s.value);
                let off = file_off(&b, s.value).unwrap() as usize;
                let end = (off + s.size.max(64) as usize + 64).min(b.len());
                match find(&b[off..end], &arity) {
                    Ok(f) => {
                        row.status = "ok".into();
                        if f.len > s.size as usize {
                            row.detail = format!("beyond-size {}>{}", f.len, s.size);
                        }
                        row.found = Some(f);
                    }
                    Err(e) => {
                        row.status = "nomatch".into();
                        row.detail = e;
                    }
                }
            }
        }
        rows.push(row);
    }
    // the report
    let mut rep =
        String::from("# id\taddress\tstatus\tnr\tsyscall\texpected\tconv\tsingle\tdetail\n");
    for r in &rows {
        let (nr, nm, conv, single) = match &r.found {
            Some(f) => (
                f.nr.to_string(),
                table.get(&f.nr).map(|t| t.0.clone()).unwrap_or_default(),
                f.conv.lean().to_string(),
                if f.single.is_some() {
                    "cancel".to_string()
                } else {
                    String::new()
                },
            ),
            None => Default::default(),
        };
        let _ = writeln!(
            rep,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            r.id,
            r.addr.map(hex).unwrap_or_default(),
            r.status,
            nr,
            nm,
            r.expected,
            conv,
            single,
            r.detail
        );
    }
    fs::write(&report_path, rep).expect("report");
    // the Lean modules: one code/desc pair per address
    let mut by_addr: BTreeMap<u64, Vec<&Row>> = BTreeMap::new();
    for r in rows.iter().filter(|r| r.found.is_some()) {
        by_addr.entry(r.addr.unwrap()).or_default().push(r);
    }
    let nbytes: usize = by_addr
        .values()
        .map(|v| v[0].found.as_ref().unwrap().len)
        .sum();
    let mut defs = String::new();
    let _ = write!(
        defs,
        "module\n\npublic import Silmaril.Libc.SysWrap.Defs\n\n/-!\n# System call wrappers of {title}: code\n\n\
         GENERATED by `tools/syswrap-gen` (`scripts/syswrap/gen.sh`); do not edit.\n\n\
         For each of the {} addresses below, `code_<address>` is the bytes of `libc.so.6` from the\n\
         address to the end of the last instruction the checker reads, and `desc_<address>` what\n\
         the wrapper does (`Silmaril.Libc.SysWrap.Desc`); the docstrings list the exports at each\n\
         address. The file: `{pin}`, sha256\n`{digest}`.\n\n\
         The {nbytes} bytes in all are machine code of the GNU C Library (LGPL-2.1-or-later; see\n\
         `NOTICES/glibc-syswrap/README.md`).\n-/\n\n\
         @[expose] public section\n\nnamespace {ns}\n\nopen Silmaril.X86 (Byte)\nopen Silmaril.Libc.SysWrap\n",
        by_addr.len()
    );
    let mut thms = String::new();
    let _ = write!(
        thms,
        "module\n\npublic import {defs_mod}\npublic import Silmaril.Libc.SysWrap.Thms\n\n/-!\n# System call wrappers of {title}: contracts\n\n\
         GENERATED by `tools/syswrap-gen` (`scripts/syswrap/gen.sh`); do not edit.\n\n\
         `spec_<address>`: the bytes `code_<address>` meet `Spec` for `desc_<address>`, by the\n\
         kernel-evaluated checker (`syscall_wrapper`). One theorem per export (`name@version`)\n\
         restates it. A cancellable wrapper (`single := some _`) is proved on its single-threaded\n\
         path only (`Silmaril.Libc.SysWrap.Entry.single`).\n-/\n\n\
         @[expose] public section\n\n\
         -- The theorem names are the exports' symbol ids (`__close@GLIBC_2.2.5`), not Mathlib names.\n\
         set_option linter.style.nameCheck false\n\nnamespace {ns}\n\nopen Silmaril.Libc.SysWrap\n"
    );
    for (a, rs) in &by_addr {
        let f = rs[0].found.as_ref().unwrap();
        let off = file_off(&b, *a).unwrap() as usize;
        let code = &b[off..off + f.len];
        let ids: Vec<String> = rs.iter().map(|r| format!("`{}`", r.id)).collect();
        let call = table.get(&f.nr).map(|t| t.0.as_str()).unwrap_or("?");
        let _ = write!(
            defs,
            "\n{}def code_{a:x} : List Byte := [\n{}]\n\n{}def desc_{a:x} : Desc where\n{}",
            doc(&format!(
                "The code at {} (`{call}`, `{}`).",
                hex(*a),
                f.conv.lean()
            )),
            lean_bytes(code, "  "),
            doc(&format!("The wrapper at {}: {}.", hex(*a), ids.join(", "))),
            lean_desc(f)
        );
        let _ = write!(
            thms,
            "\n/-- `{call}` at {}. -/\ntheorem spec_{a:x} : Spec code_{a:x} desc_{a:x} := by syscall_wrapper\n",
            hex(*a)
        );
        for r in rs {
            let _ = write!(
                thms,
                "\ntheorem «{}» : Spec code_{a:x} desc_{a:x} := spec_{a:x}\n",
                r.id
            );
        }
    }
    let _ = write!(defs, "\nend {ns}\n");
    let _ = write!(thms, "\nend {ns}\n");
    fs::write(&defs_path, defs).expect("defs");
    fs::write(&thms_path, thms).expect("thms");
    let ok = rows.iter().filter(|r| r.found.is_some()).count();
    eprintln!(
        "syswrap-gen: {pin}: {ok} of {} symbols matched ({} addresses, {nbytes} bytes)",
        rows.len(),
        by_addr.len()
    );
    ExitCode::SUCCESS
}
