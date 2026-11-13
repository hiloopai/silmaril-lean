//! The JSON export for the hardware harness (`tools/litmus-run`).
//!
//! `litmus-x86 export` writes `export/corpus.json`. It is produced in the same run, from the same
//! `Entry` values, as the Lean module `Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean`, and the
//! tool refuses to export unless that Lean module is byte-identical to its regeneration. So the
//! bytes, layout, initial registers, condition and recorded verdicts in the JSON are the ones in
//! the Lean table.
//!
//! The model-allowed outcome sets (`allowed.tso`, `allowed.sc`) are the distinct final states of
//! the consistent executions found by this crate's checker (`checker.rs`, a transcription of
//! herd's `x86tso.cat`), projected onto the observed registers and the location bytes. They
//! exist for TSO-covered tests only. They are computed by the Rust checker, which is tested,
//! not proved; they are not herd7 output and not computed by Lean.
//!
//! Format (one object per test, in index order):
//!
//! ```text
//! { "name", "path", "coverage": "tso"|"xl", "quant": "exists"|"not_exists"|"forall",
//!   "tso"|"sc": "allowed"|"forbidden"|null, "xl": "allowed"|"forbidden",
//!   "locs": [{"name", "addr", "size", "init": "<hex bytes, little-endian>"}],
//!   "threads": [{"regs": [[num, "0x.."]], "observe": [num],
//!                "code": [{"asm", "bytes": "<hex>"}]}],
//!   "witness": <cond>,
//!   "allowed": null | {"tso": [<outcome>], "sc": [<outcome>]} }
//! <cond>    = {"true": true} | {"not": c} | {"and": [c, c]} | {"or": [c, c]}
//!           | {"reg": [thread, num, bits, "0x.."]} | {"mem": ["0x addr", size, "0x.."]}
//! <outcome> = {"regs": [["0x.." per observed register] per thread], "mem": ["<hex>" per loc]}
//! ```
//!
//! Numbers that may exceed 2^53 are hex strings. `witness` is the condition the verdicts are
//! about: the body for `exists`/`~exists`, its negation for `forall`.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::checker::{Final, Verdict};
use crate::emit::{Coverage, Entry};
use crate::litmus::{Error, Quant};
use crate::model::{Atom, Cond, Model};

/// Per test: the TSO and SC final-state sets, for TSO-covered tests.
pub type Sets = Option<(BTreeSet<Final>, BTreeSet<Final>)>;

pub(crate) fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

pub(crate) fn hex_bytes(v: u128, size: u64) -> String {
    let mut s = String::new();
    for i in 0..size.min(16) {
        let _ = write!(s, "{:02x}", (v >> (8 * i)) as u8);
    }
    // Locations wider than 16 bytes are arrays that start at zero.
    for _ in 16..size.max(16) {
        s.push_str("00");
    }
    s
}

pub(crate) fn verdict(v: Option<Verdict>) -> String {
    v.map_or("null".into(), |v| json_str(v.name()))
}

pub(crate) fn cond(c: &Cond) -> String {
    match c {
        Cond::True => "{\"true\":true}".into(),
        Cond::Not(a) => format!("{{\"not\":{}}}", cond(a)),
        Cond::And(a, b) => format!("{{\"and\":[{},{}]}}", cond(a), cond(b)),
        Cond::Or(a, b) => format!("{{\"or\":[{},{}]}}", cond(a), cond(b)),
        Cond::Atom(Atom::Reg {
            thread,
            reg,
            bits,
            value,
        }) => format!("{{\"reg\":[{thread},{reg},{bits},\"0x{value:x}\"]}}"),
        Cond::Atom(Atom::Mem { addr, size, value }) => {
            format!("{{\"mem\":[\"0x{addr:x}\",{size},\"0x{value:x}\"]}}")
        }
    }
}

fn cond_regs(c: &Cond, out: &mut Vec<(usize, u8)>) {
    match c {
        Cond::True | Cond::Atom(Atom::Mem { .. }) => {}
        Cond::Not(a) => cond_regs(a, out),
        Cond::And(a, b) | Cond::Or(a, b) => {
            cond_regs(a, out);
            cond_regs(b, out)
        }
        Cond::Atom(Atom::Reg { thread, reg, .. }) => out.push((*thread, *reg)),
    }
}

/// Per thread, the observed registers: those an instruction may write plus those of the
/// condition, sorted, never `rsp` (the harness's stack pointer; no corpus test uses it).
pub fn observed(m: &Model) -> Result<Vec<Vec<u8>>, Error> {
    let mut cr = Vec::new();
    cond_regs(&m.cond, &mut cr);
    let mut out = Vec::new();
    for (t, (insns, _)) in m.threads.iter().enumerate() {
        let mut s: BTreeSet<u8> = insns.iter().flat_map(|i| i.writes()).collect();
        s.extend(cr.iter().filter(|(th, _)| *th == t).map(|(_, r)| *r));
        if s.contains(&4) {
            return Err(Error(format!("{}: thread {t} uses rsp", m.name)));
        }
        out.push(s.into_iter().collect());
    }
    Ok(out)
}

fn outcome(m: &Model, obs: &[Vec<u8>], f: &Final) -> String {
    let regs: Vec<String> = obs
        .iter()
        .enumerate()
        .map(|(t, rs)| {
            let v: Vec<String> = rs
                .iter()
                .map(|r| format!("\"0x{:x}\"", f.regs[t][*r as usize]))
                .collect();
            format!("[{}]", v.join(","))
        })
        .collect();
    let mem: Vec<String> = m
        .locs
        .iter()
        .zip(&f.mem)
        .map(|(l, v)| format!("\"{}\"", hex_bytes(*v as u128, l.size)))
        .collect();
    format!(
        "{{\"regs\":[{}],\"mem\":[{}]}}",
        regs.join(","),
        mem.join(",")
    )
}

fn outcome_set(m: &Model, obs: &[Vec<u8>], s: &BTreeSet<Final>) -> String {
    // Projection may merge states; keep the rendered set sorted and duplicate-free.
    let v: BTreeSet<String> = s.iter().map(|f| outcome(m, obs, f)).collect();
    let v: Vec<String> = v.into_iter().collect();
    format!("[\n      {}]", v.join(",\n      "))
}

/// Render the export.
pub fn render(entries: &[Entry], sets: &[Sets], provenance: &[String]) -> Result<String, Error> {
    let mut s = String::from("{\n\"format\": \"silmaril-litmus-x86-export/1\",\n");
    s.push_str("\"generated_by\": \"tools/litmus-x86 export (do not edit)\",\n");
    s.push_str("\"allowed_source\": \"litmus-x86 checker (x86tso.cat transcription, tested not proved); not herd7, not Lean\",\n");
    s.push_str("\"lean_module\": \"Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean\",\n");
    let p: Vec<String> = provenance.iter().map(|p| json_str(p)).collect();
    let _ = writeln!(s, "\"provenance\": [{}],", p.join(", "));
    s.push_str("\"tests\": [");
    for (i, (e, set)) in entries.iter().zip(sets).enumerate() {
        let m = &e.model;
        let obs = observed(m)?;
        s.push_str(if i == 0 { "\n" } else { ",\n" });
        s.push_str("  {");
        let _ = write!(
            s,
            "\"name\": {}, \"path\": {}, ",
            json_str(&m.name),
            json_str(&e.path)
        );
        let cov = match e.coverage {
            Coverage::Tso => "tso",
            Coverage::Xl => "xl",
        };
        let q = match m.quant {
            Quant::Exists => "exists",
            Quant::NotExists => "not_exists",
            Quant::Forall => "forall",
        };
        let _ = writeln!(
            s,
            "\"coverage\": \"{cov}\", \"quant\": \"{q}\", \"tso\": {}, \"sc\": {}, \"xl\": {},",
            verdict(e.tso),
            verdict(e.sc),
            verdict(Some(e.xl))
        );
        let locs: Vec<String> = m
            .locs
            .iter()
            .map(|l| {
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
        for (t, ((_, regs), code)) in m.threads.iter().zip(&e.code).enumerate() {
            s.push_str(if t == 0 { "\n" } else { ",\n" });
            let rs: Vec<String> = regs
                .iter()
                .map(|(r, v)| format!("[{r},\"0x{v:x}\"]"))
                .collect();
            let ob: Vec<String> = obs[t].iter().map(|r| r.to_string()).collect();
            let cs: Vec<String> = code
                .iter()
                .map(|(g, b)| {
                    let mut h = String::new();
                    for x in b {
                        let _ = write!(h, "{x:02x}");
                    }
                    format!("{{\"asm\": {}, \"bytes\": \"{h}\"}}", json_str(g))
                })
                .collect();
            let _ = write!(
                s,
                "    {{\"regs\": [{}], \"observe\": [{}],\n     \"code\": [{}]}}",
                rs.join(","),
                ob.join(","),
                cs.join(", ")
            );
        }
        s.push_str("],\n");
        let _ = writeln!(s, "   \"witness\": {},", cond(&m.witness()));
        match set {
            None => s.push_str("   \"allowed\": null}"),
            Some((tso, sc)) => {
                let _ = write!(
                    s,
                    "   \"allowed\": {{\n    \"tso\": {},\n    \"sc\": {}}}}}",
                    outcome_set(m, &obs, tso),
                    outcome_set(m, &obs, sc)
                );
            }
        }
    }
    s.push_str("\n]\n}\n");
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_and_strings() {
        assert_eq!(hex_bytes(0x0102, 4), "02010000");
        assert_eq!(hex_bytes(0, 18).len(), 36);
        assert_eq!(json_str("a\"\\\n\u{1}"), "\"a\\\"\\\\\\n\\u0001\"");
    }

    #[test]
    fn observed_registers() {
        let t = crate::litmus::parse(
            "X86 T\n{}\n P0 | P1 ;\n MOV [x],$1 | MOV EAX,[x] ;\n | XCHG [y],ECX ;\nexists (0:EBX=0 /\\ 1:EAX=1)\n",
        )
        .unwrap();
        let m = Model::resolve(&t).unwrap();
        assert_eq!(observed(&m).unwrap(), vec![vec![3], vec![0, 1]]);
    }
}
