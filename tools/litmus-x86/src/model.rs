//! A parsed test resolved against the fixed memory layout and the System V register file.
//!
//! Layout: locations get absolute addresses from `BASE` upward in declaration order (then in
//! order of first use for undeclared ones), each aligned to 64 bytes and padded to a multiple
//! of 64, so distinct locations never share a cache line. Undeclared locations are `int`
//! (4 bytes), as in herd. Registers are the 16 System V general-purpose registers, numbered
//! as in the hardware encoding; a herd `EAX` is the low 32 bits of `rax`.

use std::collections::BTreeMap;

use crate::insn::{self, Insn, Reg};
use crate::litmus::{self, Error, Expr, Quant, RegInit};

/// First location address.
pub const BASE: u64 = 0x10000;
/// Alignment and padding unit of a location.
pub const LINE: u64 = 64;

/// A location in the layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loc {
    pub name: String,
    pub addr: u64,
    /// Total size in bytes.
    pub size: u64,
    /// Initial value, little-endian over `size` bytes (scalars; arrays start at zero).
    pub init: u128,
}

/// A resolved final-condition atom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// Thread, register number, width in bits, value modulo `2^bits`.
    Reg {
        thread: usize,
        reg: u8,
        bits: u32,
        value: u64,
    },
    /// Address, size in bytes, little-endian value modulo `2^(8*size)`.
    Mem { addr: u64, size: u64, value: u128 },
}

/// A resolved formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    True,
    Atom(Atom),
    Not(Box<Cond>),
    And(Box<Cond>, Box<Cond>),
    Or(Box<Cond>, Box<Cond>),
}

/// A thread: its instructions and nonzero initial registers (number, 64-bit value).
pub type ThreadModel = (Vec<Insn>, Vec<(u8, u64)>);

/// A test resolved against the layout.
#[derive(Clone, Debug)]
pub struct Model {
    pub name: String,
    pub doc: Option<String>,
    pub locs: Vec<Loc>,
    /// Per thread: the instructions and their initial registers (number, 64-bit value),
    /// nonzero values only, sorted by register number.
    pub threads: Vec<ThreadModel>,
    pub quant: Quant,
    pub cond: Cond,
}

fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

impl Model {
    /// Address map, for [`Insn::gas`].
    pub fn addrs(&self) -> BTreeMap<String, u64> {
        self.locs.iter().map(|l| (l.name.clone(), l.addr)).collect()
    }

    /// The location with the given name.
    pub fn loc(&self, name: &str) -> Option<&Loc> {
        self.locs.iter().find(|l| l.name == name)
    }

    /// The witness formula: the body for `exists`/`~exists`, its negation for `forall`.
    pub fn witness(&self) -> Cond {
        match self.quant {
            Quant::Forall => Cond::Not(Box::new(self.cond.clone())),
            _ => self.cond.clone(),
        }
    }

    /// Resolve a parsed test.
    pub fn resolve(t: &litmus::Test) -> Result<Model, Error> {
        let mut threads = Vec::new();
        for (i, cells) in t.threads.iter().enumerate() {
            let insns = cells
                .iter()
                .map(|c| insn::parse(t.arch, c).map_err(|e| Error(format!("P{i}: {e}"))))
                .collect::<Result<Vec<_>, _>>()?;
            threads.push(insns);
        }
        // Locations: declared, then first use in code, then in the condition.
        let mut names: Vec<(String, u64, u128)> = Vec::new();
        for d in &t.decls {
            let size = d.elem * d.count;
            let init = (d.init as u128) & mask((8 * size).min(128) as u32);
            names.push((d.name.clone(), size, init));
        }
        let mut add = |n: &str| {
            if !names.iter().any(|(m, _, _)| m == n) {
                names.push((n.to_string(), 4, 0));
            }
        };
        for th in &threads {
            for i in th {
                if let Some(m) = i.mem() {
                    add(&m.loc);
                }
            }
        }
        for (_, _, r) in &t.regs {
            if let RegInit::Addr(n) = r {
                add(n);
            }
        }
        fn cond_locs(e: &Expr, out: &mut Vec<String>) {
            match e {
                Expr::Atom(litmus::Atom::Loc { name, .. }) => out.push(name.clone()),
                Expr::Not(a) => cond_locs(a, out),
                Expr::And(a, b) | Expr::Or(a, b) => {
                    cond_locs(a, out);
                    cond_locs(b, out)
                }
                _ => {}
            }
        }
        let mut cl = Vec::new();
        cond_locs(&t.cond, &mut cl);
        for n in &cl {
            add(n);
        }
        let mut locs = Vec::new();
        let mut next = BASE;
        for (name, size, init) in names {
            locs.push(Loc {
                name,
                addr: next,
                size,
                init,
            });
            next += size.div_ceil(LINE).max(1) * LINE;
        }
        let mut model = Model {
            name: t.name.clone(),
            doc: t.doc.clone(),
            locs,
            threads: Vec::new(),
            quant: t.quant,
            cond: Cond::True,
        };
        // Accesses stay inside their location.
        for (i, th) in threads.iter().enumerate() {
            for ins in th {
                if let Some(m) = ins.mem() {
                    let l = model
                        .loc(&m.loc)
                        .ok_or_else(|| Error(format!("unknown location {}", m.loc)))?;
                    if m.off + ins.mem_size() > l.size {
                        return Err(Error(format!(
                            "P{i}: access to {}+{} overruns the location",
                            m.loc, m.off
                        )));
                    }
                }
            }
        }
        for (i, insns) in threads.into_iter().enumerate() {
            let mut regs: BTreeMap<u8, u64> = BTreeMap::new();
            for (th, name, init) in &t.regs {
                if *th != i {
                    continue;
                }
                let r = Reg::parse(name).ok_or_else(|| Error(format!("bad register {name}")))?;
                let v = match init {
                    RegInit::Int(v) => (*v as u64) & (mask(8 * r.size as u32) as u64),
                    RegInit::Addr(n) => model
                        .loc(n)
                        .map(|l| l.addr)
                        .ok_or_else(|| Error(format!("unknown {n}")))?,
                };
                regs.insert(r.num, v);
            }
            if t.regs.iter().any(|(th, _, _)| *th >= t.threads.len()) {
                return Err(Error("register initialised for a missing thread".into()));
            }
            model
                .threads
                .push((insns, regs.into_iter().filter(|(_, v)| *v != 0).collect()));
        }
        model.cond = model.resolve_cond(&t.cond)?;
        Ok(model)
    }

    fn resolve_cond(&self, e: &Expr) -> Result<Cond, Error> {
        Ok(match e {
            Expr::True => Cond::True,
            Expr::Not(a) => Cond::Not(Box::new(self.resolve_cond(a)?)),
            Expr::And(a, b) => Cond::And(
                Box::new(self.resolve_cond(a)?),
                Box::new(self.resolve_cond(b)?),
            ),
            Expr::Or(a, b) => Cond::Or(
                Box::new(self.resolve_cond(a)?),
                Box::new(self.resolve_cond(b)?),
            ),
            Expr::Atom(litmus::Atom::Reg { thread, reg, value }) => {
                if *thread >= self.threads.len() {
                    return Err(Error(format!("bad thread {thread}")));
                }
                let r = Reg::parse(reg).ok_or_else(|| Error(format!("bad register `{reg}`")))?;
                let bits = 8 * r.size as u32;
                Cond::Atom(Atom::Reg {
                    thread: *thread,
                    reg: r.num,
                    bits,
                    value: ((*value as u128) & mask(bits)) as u64,
                })
            }
            Expr::Atom(litmus::Atom::Loc { name, value }) => {
                let l = self
                    .loc(name)
                    .ok_or_else(|| Error(format!("unknown location `{name}`")))?;
                let size = l.size.min(16);
                Cond::Atom(Atom::Mem {
                    addr: l.addr,
                    size,
                    value: (*value as u128) & mask(8 * size as u32),
                })
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_and_registers() {
        let t = litmus::parse(
            "X86_64 T\n{ uint8_t b[128]; int64_t x=-1; 0:rdi=x; 0:eax=-1; }\n P0 | P1 ;\n movq %rax,(b+60) | movl (z),%ebx ;\nexists (1:ebx=-1 /\\ x=2)\n",
        )
        .unwrap();
        let m = Model::resolve(&t).unwrap();
        assert_eq!(
            m.locs[0],
            Loc {
                name: "b".into(),
                addr: BASE,
                size: 128,
                init: 0
            }
        );
        assert_eq!(
            m.locs[1],
            Loc {
                name: "x".into(),
                addr: BASE + 128,
                size: 8,
                init: u64::MAX as u128
            }
        );
        assert_eq!(m.locs[2].name, "z");
        assert_eq!(m.locs[2].addr, BASE + 192);
        assert_eq!(m.threads[0].1, vec![(0, 0xffff_ffff), (7, BASE + 128)]);
        let Cond::And(a, _) = &m.cond else { panic!() };
        assert_eq!(
            **a,
            Cond::Atom(Atom::Reg {
                thread: 1,
                reg: 3,
                bits: 32,
                value: 0xffff_ffff
            })
        );
    }

    #[test]
    fn overrun_is_rejected() {
        let t =
            litmus::parse("X86_64 T\n{ int x; }\n P0 ;\n movq $1,(x) ;\nexists (x=1)\n").unwrap();
        assert!(Model::resolve(&t).is_err());
    }
}
