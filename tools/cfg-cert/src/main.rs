//! `cfg-cert`: from an x86-64 ELF file and entry addresses, propose a certificate
//! (`Silmaril.Elf.Effects.Cert`: one CFG per internal function reached, and the call graph) and
//! write it as a Lean module, with the reachable node set and the `decide` checks.
//!
//! The tool is untrusted: Lean re-decodes every block (`Graph.sub`) and re-checks every edge
//! (`Cert.check`, `CallGraph.closedB`). Jump tables and non-returning calls are proposals: a jump
//! table becomes `.table` (its targets are the `IndOk` assumption of the world), and a call to a
//! function that never returns gets no return site.
//!
//! Usage: `cfg-cert --elf FILE --entry 0xADDR [--entry ...] --name LeanName --module Mod.Path
//!                  [--title TEXT] [--license TEXT] [--summary]`

mod x64;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::fs;
use std::process::ExitCode;
use x64::{Info, Kind, Opnd, Rax};

// ---------------------------------------------------------------- SHA-256 (provenance)

fn sha256(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    let mut m = data.to_vec();
    let bits = (data.len() as u64) * 8;
    m.push(0x80);
    while m.len() % 64 != 56 {
        m.push(0);
    }
    m.extend_from_slice(&bits.to_be_bytes());
    for c in m.chunks(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes(c[4 * i..4 * i + 4].try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7].wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [t1.wrapping_add(t2), v[0], v[1], v[2], v[3].wrapping_add(t1), v[4], v[5], v[6]];
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
fn cstr(b: &[u8], o: usize) -> Vec<u8> {
    let end = b[o..].iter().position(|&c| c == 0).map(|p| o + p).unwrap_or(b.len());
    b[o..end].to_vec()
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Ver {
    name: Vec<u8>,
    hash: u64,
    hidden: bool,
}

/// An import reference (`Silmaril.Elf.Ref`).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Ref {
    name: Vec<u8>,
    weak: bool,
    ver: Option<Ver>,
}

impl Ref {
    fn show(&self) -> String {
        let n = String::from_utf8_lossy(&self.name).into_owned();
        match &self.ver {
            Some(v) => format!("{n}@{}", String::from_utf8_lossy(&v.name)),
            None => n,
        }
    }
}

struct DynSym {
    name: Vec<u8>,
    defined: bool,
    value: u64,
    typ: u8,
    r#ref: Ref,
}

struct Seg {
    vaddr: u64,
    off: u64,
    filesz: u64,
    flags: u64,
}

struct Elf {
    b: Vec<u8>,
    segs: Vec<Seg>,
    syms: Vec<DynSym>,
    /// GOT slot -> relocation: `Ok(dynsym index)` for `GLOB_DAT`/`JUMP_SLOT`, `Err(addend)` for
    /// `RELATIVE`.
    slots: BTreeMap<u64, Result<usize, u64>>,
    /// Function names from `.symtab`/`.dynsym` (for comments).
    names: BTreeMap<u64, String>,
}

impl Elf {
    fn parse(b: Vec<u8>) -> Result<Elf, String> {
        if b.len() < 64 || &b[0..4] != b"\x7fELF" || b[4] != 2 || b[5] != 1 || u16le(&b, 18) != 62 {
            return Err("not an ELF64 little-endian x86-64 file".into());
        }
        let phoff = u64le(&b, 0x20) as usize;
        let phentsize = u16le(&b, 0x36) as usize;
        let phnum = u16le(&b, 0x38) as usize;
        let mut segs = Vec::new();
        for i in 0..phnum {
            let o = phoff + i * phentsize;
            if u32le(&b, o) == 1 {
                segs.push(Seg {
                    flags: u32le(&b, o + 4),
                    off: u64le(&b, o + 8),
                    vaddr: u64le(&b, o + 16),
                    filesz: u64le(&b, o + 32),
                });
            }
        }
        let shoff = u64le(&b, 0x28) as usize;
        let shentsize = u16le(&b, 0x3a) as usize;
        let shnum = u16le(&b, 0x3c) as usize;
        struct Sh {
            typ: u64,
            off: usize,
            size: usize,
            link: usize,
            entsize: usize,
        }
        let sh: Vec<Sh> = (0..shnum)
            .map(|i| {
                let o = shoff + i * shentsize;
                Sh {
                    typ: u32le(&b, o + 4),
                    off: u64le(&b, o + 24) as usize,
                    size: u64le(&b, o + 32) as usize,
                    link: u32le(&b, o + 40) as usize,
                    entsize: u64le(&b, o + 56) as usize,
                }
            })
            .collect();
        let mut syms = Vec::new();
        let mut names = BTreeMap::new();
        if let Some(ds) = sh.iter().find(|s| s.typ == 11) {
            let strs = sh[ds.link].off;
            // version needs: index -> Ver
            let mut need: BTreeMap<u64, Ver> = BTreeMap::new();
            if let Some(vn) = sh.iter().find(|s| s.typ == 0x6ffffffe) {
                let vstr = sh[vn.link].off;
                let mut o = vn.off;
                loop {
                    let cnt = u16le(&b, o + 2);
                    let aux = u32le(&b, o + 8) as usize;
                    let next = u32le(&b, o + 12) as usize;
                    let mut a = o + aux;
                    for _ in 0..cnt {
                        let hash = u32le(&b, a);
                        let flags = u16le(&b, a + 4);
                        let other = u16le(&b, a + 6);
                        let name = cstr(&b, vstr + u32le(&b, a + 8) as usize);
                        need.insert(other, Ver { name, hash, hidden: flags & 2 != 0 });
                        let an = u32le(&b, a + 12) as usize;
                        if an == 0 {
                            break;
                        }
                        a += an;
                    }
                    if next == 0 {
                        break;
                    }
                    o += next;
                }
            }
            let versym = sh.iter().find(|s| s.typ == 0x6fffffff);
            for k in 0..ds.size / 24 {
                let o = ds.off + 24 * k;
                let name = cstr(&b, strs + u32le(&b, o) as usize);
                let info = b[o + 4];
                let shndx = u16le(&b, o + 6);
                let value = u64le(&b, o + 8);
                let (vi, hidden) = match versym {
                    Some(vs) => {
                        let v = u16le(&b, vs.off + 2 * k);
                        (v & 0x7fff, v & 0x8000 != 0)
                    }
                    None => (0, false),
                };
                let ver = need.get(&vi).map(|v| Ver { hidden: hidden || v.hidden, ..v.clone() });
                let defined = shndx != 0;
                if defined && (info & 0xf) == 2 && !name.is_empty() {
                    names.entry(value).or_insert_with(|| String::from_utf8_lossy(&name).into_owned());
                }
                syms.push(DynSym {
                    r#ref: Ref { name: name.clone(), weak: info >> 4 == 2, ver: if defined { None } else { ver } },
                    name,
                    defined,
                    value,
                    typ: info & 0xf,
                });
            }
        }
        if let Some(st) = sh.iter().find(|s| s.typ == 2) {
            let strs = sh[st.link].off;
            for k in 0..st.size / 24 {
                let o = st.off + 24 * k;
                let info = b[o + 4];
                let value = u64le(&b, o + 8);
                if (info & 0xf) == 2 && u16le(&b, o + 6) != 0 {
                    let name = cstr(&b, strs + u32le(&b, o) as usize);
                    names.entry(value).or_insert_with(|| String::from_utf8_lossy(&name).into_owned());
                }
            }
        }
        let mut slots = BTreeMap::new();
        for s in sh.iter().filter(|s| s.typ == 4 && s.entsize == 24) {
            for k in 0..s.size / 24 {
                let o = s.off + 24 * k;
                let off = u64le(&b, o);
                let info = u64le(&b, o + 8);
                let addend = u64le(&b, o + 16);
                match info & 0xffffffff {
                    6 | 7 => {
                        slots.insert(off, Ok((info >> 32) as usize));
                    }
                    8 => {
                        slots.insert(off, Err(addend));
                    }
                    _ => {}
                }
            }
        }
        Ok(Elf { b, segs, syms, slots, names })
    }

    /// Up to `n` bytes of an executable `PT_LOAD` at `v`.
    fn code(&self, v: u64, n: usize) -> Option<&[u8]> {
        let s = self.segs.iter().find(|s| s.flags & 1 != 0 && v >= s.vaddr && v < s.vaddr + s.filesz)?;
        let o = (s.off + v - s.vaddr) as usize;
        let end = (s.off + s.filesz) as usize;
        Some(&self.b[o..end.min(o + n)])
    }

    /// Bytes of any `PT_LOAD` at `v`.
    fn data(&self, v: u64, n: usize) -> Option<&[u8]> {
        let s = self.segs.iter().find(|s| v >= s.vaddr && v + n as u64 <= s.vaddr + s.filesz)?;
        let o = (s.off + v - s.vaddr) as usize;
        Some(&self.b[o..o + n])
    }

    fn lookup_def(&self, name: &str) -> Option<u64> {
        self.syms
            .iter()
            .find(|s| s.defined && s.name == name.as_bytes() && (s.typ == 2 || s.typ == 10))
            .map(|s| s.value)
    }
}

// ---------------------------------------------------------------- certificates

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Target {
    Blk(u64),
    Fn(u64),
    Ext(Ref),
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Why {
    Got(u64),
    Table(u64, u64, u64),
    Flagged,
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Term {
    Fall(u64),
    Jcc(u64, u64),
    Jmp(Target),
    JmpInd(Option<Vec<Target>>, Why),
    Call(Target, Option<u64>),
    CallInd(Option<Vec<Target>>, Why, Option<u64>),
    Sys(Option<u64>, u64),
    SysOther(u64),
    Ret,
    Trap,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Node {
    Fn(u64),
    Ext(Ref),
    Sys(u64),
    SysAny,
    Unresolved,
}

struct Block {
    start: u64,
    len: u64,
    term: Term,
}

struct Graph {
    entry: u64,
    blocks: Vec<Block>,
}

const NORET: &[&str] = &[
    "exit", "_exit", "_Exit", "abort", "__stack_chk_fail", "__assert_fail", "__fortify_fail",
    "__chk_fail", "err", "errx", "verr", "verrx", "longjmp", "siglongjmp", "__longjmp_chk",
    "pthread_exit", "quick_exit", "__libc_start_main", "__cxa_throw", "_Unwind_Resume",
];

fn wrap(x: i128) -> u64 {
    x.rem_euclid(1i128 << 64) as u64
}

struct Ctx<'a> {
    elf: &'a Elf,
    /// Internal functions known to return.
    returns: BTreeSet<u64>,
}

impl<'a> Ctx<'a> {
    fn dec(&self, a: u64) -> Result<(Info, u64), String> {
        let w = self.elf.code(a, 15).ok_or_else(|| format!("{a:#x}: not in an executable segment"))?;
        let (i, l) = x64::decode(w).ok_or_else(|| format!("{a:#x}: undecodable {:02x?}", &w[..w.len().min(8)]))?;
        Ok((i, l as u64))
    }

    /// The target of a GOT slot.
    fn slot(&self, slot: u64) -> Option<Target> {
        match self.elf.slots.get(&slot)? {
            Ok(k) => {
                let s = self.elf.syms.get(*k)?;
                if s.defined && s.typ == 2 { Some(Target::Fn(s.value)) } else if !s.defined { Some(Target::Ext(s.r#ref.clone())) } else { None }
            }
            Err(a) => Some(Target::Fn(*a)),
        }
    }

    fn noret_target(&self, t: &Target) -> bool {
        match t {
            Target::Fn(a) => !self.returns.contains(a),
            Target::Ext(r) => NORET.iter().any(|n| n.as_bytes() == r.name.as_slice()),
            Target::Blk(_) => false,
        }
    }

    /// A gcc/clang jump table before `jmp *%reg` at `a`: `cmp $n, ...; ja ...; lea T(%rip), ...;
    /// movslq (...,...,4), ...; add ..., ...; jmp *...`.
    fn table(&self, insns: &BTreeMap<u64, (Info, u64)>, a: u64) -> Option<(u64, u64, Vec<u64>)> {
        // strip `3E`/`2E` and read a REX byte
        let parse = |x: u64, l: u64| -> Option<(Vec<u8>, usize, u8)> {
            let w = self.elf.code(x, l as usize)?.to_vec();
            let mut p = 0;
            while p < w.len() && (w[p] == 0x3e || w[p] == 0x2e) {
                p += 1;
            }
            let rex = if p < w.len() && (0x40..0x50).contains(&w[p]) { p += 1; w[p - 1] } else { 0 };
            Some((w, p, rex))
        };
        // the base register of `movslq (base, idx, 4), r` just before the jump, and the bound
        let mut base = None;
        let mut n = None;
        for (&x, &(_, l)) in insns.range(a.saturating_sub(48)..a) {
            let (w, p, rex) = parse(x, l)?;
            if p + 2 < w.len() && w[p] == 0x63 && (w[p + 1] & 7) == 4 && (w[p + 1] >> 6) < 2 && (w[p + 2] >> 6) == 2 {
                base = Some((w[p + 2] & 7) | ((rex & 1) << 3));
            }
            if p + 2 < w.len() && matches!(w[p], 0x80 | 0x81 | 0x83) && (w[p + 1] >> 3) & 7 == 7 && w[p + 1] >> 6 == 3 {
                let imm = if w[p] == 0x81 { u32le(&w, p + 2) } else { w[p + 2] as u64 };
                n = Some(imm + 1);
            }
            if p + 1 < w.len() && (w[p] == 0x3c || w[p] == 0x3d) && rex == 0 {
                n = Some(if w[p] == 0x3c { w[p + 1] as u64 } else { u32le(&w, p + 1) } + 1);
            }
        }
        let (base, n) = (base?, n?);
        // the nearest `lea T(%rip), base` before the jump in the function
        let mut tbl = None;
        for (&x, &(_, l)) in insns.range(..a).rev() {
            let (w, p, rex) = parse(x, l)?;
            if p + 5 < w.len() && w[p] == 0x8d && (w[p + 1] & 0xc7) == 0x05 && rex & 8 != 0
                && ((w[p + 1] >> 3) & 7) | ((rex & 4) << 1) == base
            {
                let d = u32le(&w, p + 2) as i32 as i64;
                tbl = Some(wrap(x as i128 + l as i128 + d as i128));
                break;
            }
        }
        let t = tbl?;
        if n == 0 || n > 4096 {
            return None;
        }
        let mut ts = Vec::new();
        for k in 0..n {
            let e = u32le(self.elf.data(t + 4 * k, 4)?, 0) as i32 as i64;
            ts.push(wrap(t as i128 + e as i128));
        }
        Some((t, n, ts))
    }

    /// The CFG of the function at `f`.
    fn graph(&self, f: u64, entries: &BTreeSet<u64>) -> Result<Graph, String> {
        let mut insns: BTreeMap<u64, (Info, u64)> = BTreeMap::new();
        let mut leaders: BTreeSet<u64> = [f].into();
        let mut work: VecDeque<u64> = [f].into();
        let mut tables: BTreeMap<u64, (u64, u64, Vec<u64>)> = BTreeMap::new();
        while let Some(a) = work.pop_front() {
            if insns.contains_key(&a) {
                continue;
            }
            let (i, l) = self.dec(a)?;
            insns.insert(a, (i, l));
            let next = a + l;
            let rel = |r: i64| wrap(next as i128 + r as i128);
            match i.kind {
                Kind::Seq | Kind::Rep => work.push_back(next),
                Kind::Jcc(r) => {
                    leaders.insert(rel(r));
                    leaders.insert(next);
                    work.push_back(rel(r));
                    work.push_back(next);
                }
                Kind::Jmp(r) => {
                    let t = rel(r);
                    if !(entries.contains(&t) && t != f) {
                        leaders.insert(t);
                        work.push_back(t);
                    }
                }
                Kind::JmpInd(Opnd::RipMem(_)) => {}
                Kind::JmpInd(_) => {
                    if let Some(tb) = self.table(&insns, a) {
                        for &t in &tb.2 {
                            leaders.insert(t);
                            work.push_back(t);
                        }
                        tables.insert(a, tb);
                    }
                }
                Kind::Call(r) => {
                    if !self.noret_target(&Target::Fn(rel(r))) || entries.contains(&rel(r)) && self.returns.contains(&rel(r)) {
                        leaders.insert(next);
                        work.push_back(next);
                    }
                }
                Kind::CallInd(op) => {
                    let t = match op {
                        Opnd::RipMem(d) => self.slot(wrap(next as i128 + d as i128)),
                        _ => None,
                    };
                    if !t.is_some_and(|t| self.noret_target(&t)) {
                        leaders.insert(next);
                        work.push_back(next);
                    }
                }
                Kind::Syscall | Kind::SysOther => {
                    leaders.insert(next);
                    work.push_back(next);
                }
                Kind::Ret | Kind::Trap => {}
                Kind::Other => return Err(format!("{a:#x}: unsupported transfer in {f:#x}")),
            }
        }
        let mut blocks = Vec::new();
        for &s in &leaders {
            let mut a = s;
            let mut rax: Option<u64> = None;
            let term = loop {
                let &(i, l) = insns.get(&a).ok_or_else(|| format!("{a:#x}: not decoded"))?;
                let next = a + l;
                let rel = |r: i64| wrap(next as i128 + r as i128);
                let ret_site = |t: &Target| if self.noret_target(t) { None } else { Some(next) };
                let t = match i.kind {
                    Kind::Seq | Kind::Rep => None,
                    Kind::Jcc(r) => Some(Term::Jcc(rel(r), next)),
                    Kind::Jmp(r) => {
                        let t = rel(r);
                        Some(Term::Jmp(if entries.contains(&t) && t != f { Target::Fn(t) } else { Target::Blk(t) }))
                    }
                    Kind::JmpInd(Opnd::RipMem(d)) => {
                        let slot = rel(d);
                        Some(match self.slot(slot) {
                            Some(t) => Term::JmpInd(Some(vec![t]), Why::Got(slot)),
                            None => Term::JmpInd(None, Why::Flagged),
                        })
                    }
                    Kind::JmpInd(_) => Some(match tables.get(&a) {
                        Some((t, n, ts)) => Term::JmpInd(
                            Some(ts.iter().collect::<BTreeSet<_>>().into_iter().map(|&x| Target::Blk(x)).collect()),
                            Why::Table(*t, *n, 4),
                        ),
                        None => Term::JmpInd(None, Why::Flagged),
                    }),
                    Kind::Call(r) => {
                        let t = Target::Fn(rel(r));
                        let rs = if entries.contains(&rel(r)) && self.returns.contains(&rel(r)) { Some(next) } else { ret_site(&t) };
                        Some(Term::Call(t, rs))
                    }
                    Kind::CallInd(Opnd::RipMem(d)) => {
                        let slot = rel(d);
                        Some(match self.slot(slot) {
                            Some(t) => {
                                let rs = ret_site(&t);
                                Term::CallInd(Some(vec![t]), Why::Got(slot), rs)
                            }
                            None => Term::CallInd(None, Why::Flagged, Some(next)),
                        })
                    }
                    Kind::CallInd(_) => Some(Term::CallInd(None, Why::Flagged, Some(next))),
                    Kind::Syscall => Some(Term::Sys(rax, next)),
                    Kind::SysOther => Some(Term::SysOther(next)),
                    Kind::Ret => Some(Term::Ret),
                    Kind::Trap => Some(Term::Trap),
                    Kind::Other => unreachable!(),
                };
                if let Some(t) = t {
                    break (t, next);
                }
                rax = match i.rax {
                    Rax::Keep => rax,
                    Rax::Set(n) => Some(n),
                    Rax::Clobber => None,
                };
                if leaders.contains(&next) {
                    break (Term::Fall(next), next);
                }
                a = next;
            };
            blocks.push(Block { start: s, len: term.1 - s, term: term.0 });
        }
        Ok(Graph { entry: f, blocks })
    }
}

fn tgt_nodes(t: &Target) -> Vec<Node> {
    match t {
        Target::Fn(a) => vec![Node::Fn(*a)],
        Target::Ext(r) => vec![Node::Ext(r.clone())],
        Target::Blk(_) => vec![],
    }
}

/// `termNodes`.
fn term_nodes(t: &Term) -> Vec<Node> {
    match t {
        Term::Jmp(t) | Term::Call(t, _) => tgt_nodes(t),
        Term::JmpInd(Some(ts), _) | Term::CallInd(Some(ts), _, _) => ts.iter().flat_map(tgt_nodes).collect(),
        Term::JmpInd(None, _) | Term::CallInd(None, _, _) => vec![Node::Unresolved],
        Term::Sys(Some(n), _) => vec![Node::Sys(*n)],
        Term::Sys(None, _) | Term::SysOther(_) => vec![Node::SysAny],
        _ => vec![],
    }
}

/// Does `g` return (a reachable `ret`, a tail call to a returning function or import)?
fn returns(g: &Graph, ctx: &Ctx) -> bool {
    g.blocks.iter().any(|b| match &b.term {
        Term::Ret => true,
        Term::Jmp(Target::Fn(a)) => ctx.returns.contains(a),
        Term::JmpInd(Some(ts), _) => ts.iter().any(|t| match t {
            Target::Blk(_) => false,
            t => !ctx.noret_target(t),
        }),
        Term::JmpInd(None, _) => true,
        _ => false,
    })
}

/// Build every function reached from the roots; iterate the "returns" analysis to a fixpoint.
fn build(elf: &Elf, roots: &[u64]) -> Result<(BTreeMap<u64, Graph>, Vec<(Node, Node)>), String> {
    let mut ctx = Ctx { elf, returns: BTreeSet::new() };
    loop {
        let mut entries: BTreeSet<u64> = roots.iter().copied().collect();
        let mut graphs: BTreeMap<u64, Graph> = BTreeMap::new();
        loop {
            let todo: Vec<u64> = entries.iter().copied().filter(|a| !graphs.contains_key(a)).collect();
            if todo.is_empty() {
                break;
            }
            for f in todo {
                let g = ctx.graph(f, &entries)?;
                for b in &g.blocks {
                    for n in term_nodes(&b.term) {
                        if let Node::Fn(a) = n {
                            entries.insert(a);
                        }
                    }
                }
                graphs.insert(f, g);
            }
            // a new entry may turn an earlier intraprocedural jump into a tail call
            let stale: Vec<u64> = graphs
                .iter()
                .filter(|(f, g)| {
                    g.blocks.iter().any(|b| matches!(b.term, Term::Jmp(Target::Blk(t)) if entries.contains(&t) && t != **f))
                })
                .map(|(f, _)| *f)
                .collect();
            for f in stale {
                graphs.remove(&f);
            }
        }
        let new: BTreeSet<u64> = graphs.iter().filter(|(_, g)| returns(g, &ctx)).map(|(f, _)| *f).collect();
        let new: BTreeSet<u64> = new.union(&ctx.returns).copied().collect();
        if new == ctx.returns {
            let mut edges = BTreeSet::new();
            for (f, g) in &graphs {
                for b in &g.blocks {
                    for n in term_nodes(&b.term) {
                        edges.insert((Node::Fn(*f), n));
                    }
                }
            }
            return Ok((graphs, edges.into_iter().collect()));
        }
        ctx.returns = new;
    }
}

// ---------------------------------------------------------------- Lean output

struct Out {
    refs: BTreeMap<Ref, String>,
}

impl Out {
    fn nm(s: &[u8]) -> String {
        format!("nm [{}]", s.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", "))
    }
    fn r(&mut self, r: &Ref) -> String {
        let k = self.refs.len();
        self.refs.entry(r.clone()).or_insert_with(|| format!("r{k}")).clone()
    }
    fn target(&mut self, t: &Target) -> String {
        match t {
            Target::Blk(a) => format!(".blk {a:#x}"),
            Target::Fn(a) => format!(".fn {a:#x}"),
            Target::Ext(r) => format!(".ext {}", self.r(r)),
        }
    }
    fn targets(&mut self, ts: &Option<Vec<Target>>) -> String {
        match ts {
            None => "none".into(),
            Some(ts) => format!("(some [{}])", ts.iter().map(|t| self.target(t)).collect::<Vec<_>>().join(", ")),
        }
    }
    fn why(w: &Why) -> String {
        match w {
            Why::Got(s) => format!("(.got {s:#x})"),
            Why::Table(t, n, k) => format!("(.table {t:#x} {n} {k})"),
            Why::Flagged => ".flagged".into(),
        }
    }
    fn opt(o: &Option<u64>) -> String {
        match o {
            None => "none".into(),
            Some(a) => format!("(some {a:#x})"),
        }
    }
    fn term(&mut self, t: &Term) -> String {
        match t {
            Term::Fall(n) => format!(".fall {n:#x}"),
            Term::Jcc(a, n) => format!(".jcc {a:#x} {n:#x}"),
            Term::Jmp(t) => format!(".jmp ({})", self.target(t)),
            Term::JmpInd(ts, w) => format!(".jmpInd {} {}", self.targets(ts), Self::why(w)),
            Term::Call(t, r) => format!(".call ({}) {}", self.target(t), Self::opt(r)),
            Term::CallInd(ts, w, r) => format!(".callInd {} {} {}", self.targets(ts), Self::why(w), Self::opt(r)),
            Term::Sys(n, r) => format!(".sys {} {r:#x}", match n { Some(n) => format!("(some {n})"), None => "none".into() }),
            Term::SysOther(r) => format!(".sysOther {r:#x}"),
            Term::Ret => ".ret".into(),
            Term::Trap => ".trap".into(),
        }
    }
    fn node(&mut self, n: &Node) -> String {
        match n {
            Node::Fn(a) => format!(".fn {a:#x}"),
            Node::Ext(r) => format!(".ext {}", self.r(r)),
            Node::Sys(k) => format!(".sys {k}"),
            Node::SysAny => ".sysAny".into(),
            Node::Unresolved => ".unresolved".into(),
        }
    }
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.windows(2).find(|w| w[0] == k).map(|w| w[1].clone())
}
fn args_all(args: &[String], k: &str) -> Vec<String> {
    args.windows(2).filter(|w| w[0] == k).map(|w| w[1].clone()).collect()
}
fn parse_addr(s: &str) -> Option<u64> {
    let s = s.trim();
    s.strip_prefix("0x").map_or_else(|| s.parse().ok(), |h| u64::from_str_radix(h, 16).ok())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let Some(path) = arg(&args, "--elf") else {
        eprintln!("usage: cfg-cert --elf FILE --entry ADDR|SYMBOL [--entry ...] --module Mod.Path [--title T] [--license T]");
        return ExitCode::from(2);
    };
    let bytes = match fs::read(&path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("cfg-cert: {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let digest = sha256(&bytes);
    let elf = match Elf::parse(bytes) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("cfg-cert: {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut roots = Vec::new();
    for e in args_all(&args, "--entry") {
        match parse_addr(&e).or_else(|| elf.lookup_def(&e)) {
            Some(a) => roots.push(a),
            None => {
                eprintln!("cfg-cert: no entry {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    let (graphs, edges) = match build(&elf, &roots) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("cfg-cert: {e}");
            return ExitCode::FAILURE;
        }
    };
    // reachable nodes
    let mut reach: BTreeSet<Node> = roots.iter().map(|&a| Node::Fn(a)).collect();
    let mut q: VecDeque<Node> = reach.iter().cloned().collect();
    while let Some(n) = q.pop_front() {
        for (a, b) in &edges {
            if *a == n && reach.insert(b.clone()) {
                q.push_back(b.clone());
            }
        }
    }
    let module = arg(&args, "--module").unwrap_or_else(|| "Cert".into());
    let title = arg(&args, "--title").unwrap_or_else(|| path.clone());
    let license = arg(&args, "--license").unwrap_or_default();
    let mut o = Out { refs: BTreeMap::new() };
    let mut body = String::new();
    let nblocks: usize = graphs.values().map(|g| g.blocks.len()).sum();
    let nbytes: u64 = graphs.values().flat_map(|g| g.blocks.iter().map(|b| b.len)).sum();
    for (f, g) in &graphs {
        let name = elf.names.get(f).map(|n| format!(" (`{n}`)")).unwrap_or_default();
        if g.blocks.len() > 64 {
            let _ = writeln!(body, "set_option maxRecDepth 16384 in");
        }
        let _ = writeln!(body, "/-- The CFG of the function at `{f:#x}`{name}. -/");
        let _ = writeln!(body, "def g_{f:x} : Graph Ref where\n  entry := {:#x}\n  blocks := [", g.entry);
        let n = g.blocks.len();
        for (k, b) in g.blocks.iter().enumerate() {
            let code = elf.code(b.start, b.len as usize).unwrap();
            let bs: Vec<String> = code.iter().map(|c| format!("0x{c:02x}")).collect();
            let t = o.term(&b.term);
            let _ = writeln!(body, "    ⟨{:#x}, [{}],\n      {t}⟩{}", b.start, bs.join(", "), if k + 1 < n { "," } else { "" });
        }
        let _ = writeln!(body, "  ]\n");
    }
    let fns: Vec<String> = graphs.keys().map(|f| format!("({f:#x}, g_{f:x})")).collect();
    let es: Vec<String> = edges.iter().map(|(a, b)| format!("({}, {})", o.node(a), o.node(b))).collect();
    let ns: Vec<String> = reach.iter().map(|n| o.node(n)).collect();
    let _ = writeln!(body, "set_option maxRecDepth 16384 in\n/-- The certificate. -/\ndef cert : Cert where\n  fns := [\n    {}]\n  graph := ⟨[\n    {}]⟩\n", fns.join(",\n    "), es.join(",\n    "));
    let _ = writeln!(body, "set_option maxRecDepth 16384 in\n/-- The nodes reachable from the entries. -/\ndef nodes : List Node := [\n  {}]\n", ns.join(",\n  "));
    let roots_s: Vec<String> = roots.iter().map(|a| format!("{a:#x}")).collect();
    let _ = writeln!(body, "/-- The entries. -/\ndef roots : List Nat := [{}]\n", roots_s.join(", "));
    let mut refs = String::new();
    let mut rs: Vec<(&Ref, &String)> = o.refs.iter().collect();
    rs.sort_by_key(|(_, k)| k[1..].parse::<usize>().unwrap_or(0));
    for (r, k) in rs {
        let ver = match &r.ver {
            None => "none".into(),
            Some(v) => format!("some ⟨{}, {:#x}, {}⟩", Out::nm(&v.name), v.hash, v.hidden),
        };
        let _ = writeln!(refs, "/-- `{}` -/\ndef {k} : Ref := ⟨{}, {}, {ver}⟩\n", r.show(), Out::nm(&r.name), r.weak);
    }
    let imports: Vec<String> = reach.iter().filter_map(|n| if let Node::Ext(r) = n { Some(format!("`{}`", r.show())) } else { None }).collect();
    let sys: Vec<String> = reach.iter().filter_map(|n| match n { Node::Sys(k) => Some(k.to_string()), Node::SysAny => Some("any".into()), _ => None }).collect();
    let unres = reach.contains(&Node::Unresolved);
    let mut out = String::new();
    let _ = write!(
        out,
        "module\n\npublic import Silmaril.Elf.Effects.Shapes.Thms\n\n/-!\n# {title}: a CFG and call-graph certificate\n\n\
GENERATED by `tools/cfg-cert`; do not edit. The file: sha256 `{digest}`. Entries: {}.\n\n\
{} functions, {nblocks} blocks, {nbytes} bytes of code{}.\n\n\
Reachable imports: {}.\n\nDirect system calls reachable: {}.{}\n-/\n\n@[expose] public section\n\nnamespace {module}\n\n\
open Silmaril.X86.Cfg (Graph)\nopen Silmaril.Elf (Ref)\nopen Silmaril.Elf.Effects\n\n\
/-- Name bytes. -/\ndef nm (l : List Nat) : Silmaril.Formats.ELF.NameBytes := l.map (BitVec.ofNat 8)\n\n",
        roots_s.join(", "),
        graphs.len(),
        if license.is_empty() { String::new() } else { format!(" ({license})") },
        if imports.is_empty() { "none".into() } else { imports.join(", ") },
        if sys.is_empty() { "none".into() } else { sys.join(", ") },
        if unres { " An unresolved transfer is reachable." } else { "" },
    );
    out.push_str(&refs);
    out.push_str(&body);
    let _ = writeln!(out, "end {module}");
    print!("{out}");
    if args.iter().any(|a| a == "--summary") {
        eprintln!("functions {} blocks {nblocks} bytes {nbytes}", graphs.len());
        eprintln!("imports: {}", imports.join(" "));
        eprintln!("syscalls: {}", sys.join(" "));
        eprintln!("unresolved: {unres}");
        for (f, g) in &graphs {
            for b in &g.blocks {
                if matches!(b.term, Term::JmpInd(None, _) | Term::CallInd(None, _, _)) {
                    eprintln!("  unresolved at {:#x} in {f:#x} ({})", b.start + b.len, elf.names.get(f).cloned().unwrap_or_default());
                }
            }
        }
    }
    if args.iter().any(|a| a == "--insns") {
        for g in graphs.values() {
            for b in &g.blocks {
                let code = elf.code(b.start, b.len as usize).unwrap();
                let mut o = 0usize;
                while o < code.len() {
                    let (i, l) = x64::decode(&code[o..]).unwrap();
                    eprintln!("I {:x} {l} {:?} {:?}", b.start + o as u64, i.kind, i.rax);
                    o += l;
                }
            }
        }
    }
    ExitCode::SUCCESS
}
