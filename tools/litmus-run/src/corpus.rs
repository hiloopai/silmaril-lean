//! The litmus corpus as exported by `litmus-x86 export` (`tools/litmus-x86/export/corpus.json`),
//! read into typed values: layout, per-thread bytes and initial registers, the witness
//! condition, the recorded verdicts and the model-allowed outcome sets.

use std::collections::BTreeSet;

use crate::json::{self, Error, Value};

/// System V names of the 16 general-purpose registers, in hardware order.
pub const GPR64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// A recorded verdict about a test's witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Allowed,
    Forbidden,
}

/// One location of the fixed layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loc {
    pub name: String,
    pub addr: u64,
    pub init: Vec<u8>,
}

/// One thread.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Thread {
    /// Initial registers (hardware number, value); the others start at zero.
    pub regs: Vec<(u8, u64)>,
    /// The registers recorded in an outcome, in this order.
    pub observe: Vec<u8>,
    /// Per instruction: AT&T text and the assembled bytes.
    pub code: Vec<(String, Vec<u8>)>,
    /// The fixed address the code must run at (`code_base` in the JSON), for code with
    /// rip-relative operands (the compiled C11 tests, `export/c11.json`). `None`: the code is
    /// position-independent (the herd corpus) and runs anywhere.
    pub code_base: Option<u64>,
}

/// A witness condition, as in the Lean `Cond`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    True,
    Not(Box<Cond>),
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
    /// Thread, register number, width in bits, value.
    Reg(usize, u8, u32, u64),
    /// Address, size in bytes, little-endian value.
    Mem(u64, u64, u128),
}

/// A final state, projected onto the observed registers and the location bytes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Outcome {
    /// Per thread, the values of `Thread::observe`.
    pub regs: Vec<Vec<u64>>,
    /// Per location, its bytes.
    pub mem: Vec<Vec<u8>>,
}

/// The model-allowed outcome sets of a TSO-covered test.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Allowed {
    pub tso: BTreeSet<Outcome>,
    pub sc: BTreeSet<Outcome>,
}

/// One test.
#[derive(Clone, Debug)]
pub struct Test {
    pub name: String,
    pub path: String,
    /// `true` for TSO-covered tests, `false` for XL-only ones.
    pub tso_covered: bool,
    pub tso: Option<Verdict>,
    pub sc: Option<Verdict>,
    pub xl: Verdict,
    pub locs: Vec<Loc>,
    pub threads: Vec<Thread>,
    pub witness: Cond,
    pub allowed: Option<Allowed>,
}

/// The whole export.
#[derive(Clone, Debug)]
pub struct Corpus {
    pub provenance: Vec<String>,
    pub tests: Vec<Test>,
}

fn verdict(v: &Value) -> Result<Option<Verdict>, Error> {
    if v.is_null() {
        return Ok(None);
    }
    match v.str()? {
        "allowed" => Ok(Some(Verdict::Allowed)),
        "forbidden" => Ok(Some(Verdict::Forbidden)),
        s => Err(Error(format!("bad verdict `{s}`"))),
    }
}

fn u64v(v: &Value) -> Result<u64, Error> {
    u64::try_from(v.uint()?).map_err(|_| Error("value exceeds 64 bits".into()))
}

fn cond(v: &Value) -> Result<Cond, Error> {
    let Value::Obj(fs) = v else {
        return Err(Error("condition is not an object".into()));
    };
    let [(k, a)] = fs.as_slice() else {
        return Err(Error("condition must have one field".into()));
    };
    let two = |a: &Value| -> Result<(Box<Cond>, Box<Cond>), Error> {
        match a.arr()? {
            [x, y] => Ok((Box::new(cond(x)?), Box::new(cond(y)?))),
            _ => Err(Error("binary condition needs two operands".into())),
        }
    };
    Ok(match k.as_str() {
        "true" => Cond::True,
        "not" => Cond::Not(Box::new(cond(a)?)),
        "and" => {
            let (x, y) = two(a)?;
            Cond::And(x, y)
        }
        "or" => {
            let (x, y) = two(a)?;
            Cond::Or(x, y)
        }
        "reg" => match a.arr()? {
            [t, r, b, x] => Cond::Reg(
                t.uint()? as usize,
                u8::try_from(r.uint()?).map_err(|_| Error("bad register".into()))?,
                b.uint()? as u32,
                u64v(x)?,
            ),
            _ => return Err(Error("bad reg atom".into())),
        },
        "mem" => match a.arr()? {
            [ad, s, x] => Cond::Mem(u64v(ad)?, u64v(s)?, x.uint()?),
            _ => return Err(Error("bad mem atom".into())),
        },
        k => return Err(Error(format!("unknown condition `{k}`"))),
    })
}

fn outcome(v: &Value) -> Result<Outcome, Error> {
    let regs = v
        .get("regs")?
        .arr()?
        .iter()
        .map(|t| t.arr()?.iter().map(u64v).collect::<Result<Vec<_>, _>>())
        .collect::<Result<Vec<_>, _>>()?;
    let mem = v
        .get("mem")?
        .arr()?
        .iter()
        .map(|m| json::hex_bytes(m.str()?))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Outcome { regs, mem })
}

fn outcomes(v: &Value) -> Result<BTreeSet<Outcome>, Error> {
    v.arr()?.iter().map(outcome).collect()
}

fn test(v: &Value) -> Result<Test, Error> {
    let name = v.get("name")?.str()?.to_string();
    let ctx = |e: Error| Error(format!("{name}: {}", e.0));
    let inner = || -> Result<Test, Error> {
        let locs = v
            .get("locs")?
            .arr()?
            .iter()
            .map(|l| {
                let init = json::hex_bytes(l.get("init")?.str()?)?;
                if init.len() as u128 != l.get("size")?.uint()? {
                    return Err(Error("location init/size mismatch".into()));
                }
                Ok(Loc {
                    name: l.get("name")?.str()?.to_string(),
                    addr: u64v(l.get("addr")?)?,
                    init,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let threads = v
            .get("threads")?
            .arr()?
            .iter()
            .map(|t| {
                let regs = t
                    .get("regs")?
                    .arr()?
                    .iter()
                    .map(|p| match p.arr()? {
                        [r, x] => Ok((r.uint()? as u8, u64v(x)?)),
                        _ => Err(Error("bad register init".into())),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let observe = t
                    .get("observe")?
                    .arr()?
                    .iter()
                    .map(|r| Ok(r.uint()? as u8))
                    .collect::<Result<Vec<_>, Error>>()?;
                let code = t
                    .get("code")?
                    .arr()?
                    .iter()
                    .map(|c| {
                        Ok((
                            c.get("asm")?.str()?.to_string(),
                            json::hex_bytes(c.get("bytes")?.str()?)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                if regs
                    .iter()
                    .map(|(r, _)| *r)
                    .chain(observe.iter().copied())
                    .any(|r| r == 4 || r > 15)
                {
                    return Err(Error("rsp or a bad register number".into()));
                }
                let code_base = match t.get("code_base") {
                    Ok(b) => Some(u64v(b)?),
                    Err(_) => None,
                };
                Ok(Thread {
                    regs,
                    observe,
                    code,
                    code_base,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let allowed = v.get("allowed")?;
        let allowed = if allowed.is_null() {
            None
        } else {
            Some(Allowed {
                tso: outcomes(allowed.get("tso")?)?,
                sc: outcomes(allowed.get("sc")?)?,
            })
        };
        let coverage = v.get("coverage")?.str()?;
        Ok(Test {
            name: name.clone(),
            path: v.get("path")?.str()?.to_string(),
            tso_covered: match coverage {
                "tso" => true,
                "xl" => false,
                c => return Err(Error(format!("bad coverage `{c}`"))),
            },
            tso: verdict(v.get("tso")?)?,
            sc: verdict(v.get("sc")?)?,
            xl: verdict(v.get("xl")?)?.ok_or_else(|| Error("missing xl verdict".into()))?,
            locs,
            threads,
            witness: cond(v.get("witness")?)?,
            allowed,
        })
    };
    inner().map_err(ctx)
}

/// Parse an export.
pub fn parse(src: &str) -> Result<Corpus, Error> {
    let v = json::parse(src)?;
    if v.get("format")?.str()? != "silmaril-litmus-x86-export/1" {
        return Err(Error("unknown export format".into()));
    }
    let provenance = v
        .get("provenance")?
        .arr()?
        .iter()
        .map(|p| Ok(p.str()?.to_string()))
        .collect::<Result<Vec<_>, Error>>()?;
    let tests = v
        .get("tests")?
        .arr()?
        .iter()
        .map(test)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Corpus { provenance, tests })
}

impl Test {
    /// Evaluate a condition on an outcome. `None` if it names an unobserved register or a
    /// byte range outside every location.
    pub fn eval(&self, c: &Cond, o: &Outcome) -> Option<bool> {
        Some(match c {
            Cond::True => true,
            Cond::Not(a) => !self.eval(a, o)?,
            Cond::And(a, b) => self.eval(a, o)? & self.eval(b, o)?,
            Cond::Or(a, b) => self.eval(a, o)? | self.eval(b, o)?,
            Cond::Reg(t, r, bits, v) => {
                let i = self.threads.get(*t)?.observe.iter().position(|x| x == r)?;
                let x = *o.regs.get(*t)?.get(i)?;
                let m = if *bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << bits) - 1
                };
                x & m == *v
            }
            Cond::Mem(addr, size, v) => {
                let (k, l) = self.locs.iter().enumerate().find(|(_, l)| {
                    l.addr <= *addr && addr + size <= l.addr + l.init.len() as u64
                })?;
                let off = (addr - l.addr) as usize;
                let bytes = o.mem.get(k)?.get(off..off + *size as usize)?;
                if *size > 16 {
                    return None;
                }
                let x = bytes
                    .iter()
                    .rev()
                    .fold(0u128, |a, b| (a << 8) | u128::from(*b));
                x == *v
            }
        })
    }

    /// Whether the witness holds on an outcome (`None` if it cannot be evaluated).
    pub fn witness_holds(&self, o: &Outcome) -> Option<bool> {
        self.eval(&self.witness, o)
    }

    /// Whether some outcome of the set satisfies the witness, as a verdict.
    pub fn verdict_of(&self, set: &BTreeSet<Outcome>) -> Option<Verdict> {
        let mut any = false;
        for o in set {
            any |= self.witness_holds(o)?;
        }
        Some(if any {
            Verdict::Allowed
        } else {
            Verdict::Forbidden
        })
    }

    /// Render an outcome: observed registers, then each location as a little-endian value
    /// (hex bytes for locations wider than 8 bytes).
    pub fn show(&self, o: &Outcome) -> String {
        let mut parts = Vec::new();
        for (t, th) in self.threads.iter().enumerate() {
            for (i, r) in th.observe.iter().enumerate() {
                if let Some(v) = o.regs.get(t).and_then(|v| v.get(i)) {
                    parts.push(format!("{t}:{}={v:#x}", GPR64[*r as usize]));
                }
            }
        }
        for (l, m) in self.locs.iter().zip(&o.mem) {
            if m.len() <= 8 {
                let v = m.iter().rev().fold(0u64, |a, b| (a << 8) | u64::from(*b));
                parts.push(format!("{}={v:#x}", l.name));
            } else {
                let nz: Vec<String> = m
                    .iter()
                    .enumerate()
                    .filter(|(_, b)| **b != 0)
                    .map(|(i, b)| format!("{i}:{b:02x}"))
                    .collect();
                parts.push(format!("{}=[{}]", l.name, nz.join(",")));
            }
        }
        parts.join(" ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ONE: &str = r#"{"format": "silmaril-litmus-x86-export/1", "provenance": ["p"], "tests": [
      {"name": "SB", "path": "p", "coverage": "tso", "quant": "exists", "tso": "allowed",
       "sc": "forbidden", "xl": "allowed",
       "locs": [{"name": "x", "addr": "0x10000", "size": 4, "init": "00000000"}],
       "threads": [{"regs": [[7,"0x10000"]], "observe": [0], "code": [{"asm": "mfence", "bytes": "0faef0"}]}],
       "witness": {"and":[{"reg":[0,0,32,"0x0"]},{"not":{"mem":["0x10001",2,"0x0102"]}}]},
       "allowed": {"tso": [{"regs":[["0x0"]],"mem":["00000000"]}], "sc": []}}]}"#;

    #[test]
    fn parse_and_eval() {
        let c = parse(ONE).unwrap();
        let t = &c.tests[0];
        assert_eq!(t.threads[0].regs, vec![(7, 0x10000)]);
        assert_eq!(t.threads[0].code[0].1, vec![0x0f, 0xae, 0xf0]);
        assert_eq!(t.threads[0].code_base, None);
        let fixed = parse(&ONE.replace(
            "\"observe\": [0],",
            "\"observe\": [0], \"code_base\": \"0x400000\",",
        ))
        .unwrap();
        assert_eq!(fixed.tests[0].threads[0].code_base, Some(0x40_0000));
        let a = t.allowed.as_ref().unwrap();
        assert_eq!(t.verdict_of(&a.tso), Some(Verdict::Allowed));
        assert_eq!(t.verdict_of(&a.sc), Some(Verdict::Forbidden));
        let o = Outcome {
            regs: vec![vec![0xffff_ffff_0000_0000]],
            mem: vec![vec![0, 2, 1, 0]],
        };
        // 32-bit view of rax is 0, but bytes 1..3 of x read 0x0102 little-endian.
        assert_eq!(t.witness_holds(&o), Some(false));
        assert_eq!(t.show(&o), "0:rax=0xffffffff00000000 x=0x10200");
    }
}
