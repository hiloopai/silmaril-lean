//! A port of `Silmaril.X86.Flow.X64` (the Lean decoder is the reference; this one only proposes).
//! Same structure, function by function, so that the certificate's blocks decode in Lean exactly
//! as they did here.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Opnd {
    Reg(u8),
    RipMem(i64),
    Mem,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Seq,
    Rep,
    Jcc(i64),
    Jmp(i64),
    JmpInd(Opnd),
    Call(i64),
    CallInd(Opnd),
    Syscall,
    SysOther,
    Ret,
    Trap,
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rax {
    Keep,
    Set(u64),
    Clobber,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Info {
    pub kind: Kind,
    pub rax: Rax,
}

struct Rd<'a> {
    b: &'a [u8],
    p: usize,
}

type R<T> = Option<T>;

impl<'a> Rd<'a> {
    fn byte(&mut self) -> R<u64> {
        let v = *self.b.get(self.p)?;
        self.p += 1;
        Some(v as u64)
    }
    fn le(&mut self, n: u32) -> R<u64> {
        let mut v: u64 = 0;
        for k in 0..n {
            v |= self.byte()? << (8 * k);
        }
        Some(v)
    }
}

fn sx(n: u32, v: u64) -> i64 {
    if n == 0 {
        return 0;
    }
    let bits = 8 * n;
    if bits >= 64 {
        return v as i64;
    }
    if v < (1u64 << (bits - 1)) { v as i64 } else { v as i64 - (1i64 << bits) }
}

#[derive(Clone, Copy, Default)]
struct Pfx {
    opsz: bool,
    adsz: bool,
    rep: bool,
    rex: Option<u64>,
}
impl Pfx {
    fn w(&self) -> bool {
        matches!(self.rex, Some(r) if r / 8 % 2 == 1)
    }
    fn r(&self) -> u64 {
        self.rex.map_or(0, |r| r / 4 % 2)
    }
    fn b(&self) -> u64 {
        self.rex.map_or(0, |r| r % 2)
    }
}

fn is_legacy(b: u64) -> bool {
    matches!(b, 0x26 | 0x2E | 0x36 | 0x3E | 0x64 | 0x65 | 0x66 | 0x67 | 0xF0 | 0xF2 | 0xF3)
}

#[derive(Clone, Copy)]
struct ModRM {
    md: u64,
    reg: u64,
    rm: u64,
    rip: bool,
    disp: i64,
}

fn disp_len(md: u64, rm: u64, sib_base: u64) -> u32 {
    if md == 1 {
        1
    } else if md == 2 {
        4
    } else if md == 0 && (rm == 5 || (rm == 4 && sib_base == 5)) {
        4
    } else {
        0
    }
}

fn modrm(r: &mut Rd) -> R<ModRM> {
    let m = r.byte()?;
    let (md, reg, rm) = (m / 64, m / 8 % 8, m % 8);
    if md == 3 {
        return Some(ModRM { md, reg, rm, rip: false, disp: 0 });
    }
    let sib = if rm == 4 { r.byte()? } else { 0 };
    let n = disp_len(md, rm, sib % 8);
    let d = r.le(n)?;
    Some(ModRM { md, reg, rm, rip: md == 0 && rm == 5, disp: sx(n, d) })
}

fn keep_if_not(p: &Pfx, byte: bool, idx: u64) -> Rax {
    if idx == 0 || (byte && p.rex.is_none() && idx == 4) { Rax::Clobber } else { Rax::Keep }
}
fn rm_dest(p: &Pfx, byte: bool, m: &ModRM) -> Rax {
    if m.md == 3 { keep_if_not(p, byte, m.rm + 8 * p.b()) } else { Rax::Keep }
}
fn reg_dest(p: &Pfx, byte: bool, m: &ModRM) -> Rax {
    keep_if_not(p, byte, m.reg + 8 * p.r())
}
fn opnd(p: &Pfx, m: &ModRM) -> Opnd {
    if m.md == 3 {
        Opnd::Reg(((m.rm + 8 * p.b()) % 16) as u8)
    } else if m.rip && !p.adsz {
        Opnd::RipMem(m.disp)
    } else {
        Opnd::Mem
    }
}
fn seq(r: Rax) -> Info {
    Info { kind: Kind::Seq, rax: r }
}
fn imm_z(p: &Pfx) -> u32 {
    if p.opsz { 2 } else { 4 }
}
fn with_modrm(r: &mut Rd, n: u32, f: impl Fn(&ModRM) -> Rax) -> R<Info> {
    let m = modrm(r)?;
    r.le(n)?;
    Some(seq(f(&m)))
}
fn with_imm(r: &mut Rd, n: u32, i: Info) -> R<Info> {
    r.le(n)?;
    Some(i)
}
fn other() -> Info {
    Info { kind: Kind::Other, rax: Rax::Clobber }
}

fn alu(r: &mut Rd, p: &Pfx, op: u64) -> R<Info> {
    let k = op / 8;
    let j = op % 8;
    let is_cmp = k == 7;
    let dst = |m: &ModRM| -> Rax {
        if is_cmp {
            Rax::Keep
        } else if (k == 6 || k == 5)
            && m.md == 3
            && m.reg + 8 * p.r() == m.rm + 8 * p.b()
            && m.reg + 8 * p.r() == 0
            && j % 2 == 1
            && !p.opsz
        {
            Rax::Set(0)
        } else if j < 2 {
            rm_dest(p, j == 0, m)
        } else {
            reg_dest(p, j == 2, m)
        }
    };
    if j < 4 {
        with_modrm(r, 0, dst)
    } else if j == 4 {
        with_imm(r, 1, seq(if is_cmp { Rax::Keep } else { Rax::Clobber }))
    } else {
        with_imm(r, imm_z(p), seq(if is_cmp { Rax::Keep } else { Rax::Clobber }))
    }
}

fn map1(r: &mut Rd, p: &Pfx, op: u64) -> R<Info> {
    let ji = |k: Kind| Info { kind: k, rax: Rax::Keep };
    if op < 0x40 {
        return if op % 8 < 6 { alu(r, p, op) } else { None };
    }
    if op < 0x50 {
        return None;
    }
    if op < 0x58 {
        return Some(seq(Rax::Keep));
    }
    if op < 0x60 {
        return Some(seq(keep_if_not(p, false, op - 0x58 + 8 * p.b())));
    }
    match op {
        0x63 => return with_modrm(r, 0, |m| reg_dest(p, false, m)),
        0x68 => return with_imm(r, imm_z(p), seq(Rax::Keep)),
        0x69 => return with_modrm(r, imm_z(p), |m| reg_dest(p, false, m)),
        0x6A => return with_imm(r, 1, seq(Rax::Keep)),
        0x6B => return with_modrm(r, 1, |m| reg_dest(p, false, m)),
        _ => {}
    }
    if op < 0x70 {
        return if op < 0x6C { None } else { Some(other()) };
    }
    if op < 0x80 {
        let d = r.byte()?;
        return Some(ji(Kind::Jcc(sx(1, d))));
    }
    match op {
        0x80 | 0x83 => with_modrm(r, 1, |m| if m.reg == 7 { Rax::Keep } else { rm_dest(p, op == 0x80, m) }),
        0x81 => with_modrm(r, imm_z(p), |m| if m.reg == 7 { Rax::Keep } else { rm_dest(p, false, m) }),
        0x82 => None,
        0x84 | 0x85 => with_modrm(r, 0, |_| Rax::Keep),
        0x86 | 0x87 => with_modrm(r, 0, |m| {
            match (rm_dest(p, op == 0x86, m), reg_dest(p, op == 0x86, m)) {
                (Rax::Keep, Rax::Keep) => Rax::Keep,
                _ => Rax::Clobber,
            }
        }),
        0x88 | 0x89 => with_modrm(r, 0, |m| rm_dest(p, op == 0x88, m)),
        0x8A | 0x8B => with_modrm(r, 0, |m| reg_dest(p, op == 0x8A, m)),
        0x8C => with_modrm(r, 0, |m| rm_dest(p, false, m)),
        0x8D => with_modrm(r, 0, |m| reg_dest(p, false, m)),
        0x8E => with_modrm(r, 0, |_| Rax::Keep),
        0x8F => with_modrm(r, 0, |m| rm_dest(p, false, m)),
        0x90 => Some(seq(if p.b() == 1 { Rax::Clobber } else { Rax::Keep })),
        0x91..=0x97 => Some(seq(Rax::Clobber)),
        0x9A => None,
        0x9C => Some(seq(Rax::Keep)),
        0x98..=0x9F => Some(seq(Rax::Clobber)),
        0xA0..=0xA3 => with_imm(
            r,
            if p.adsz { 4 } else { 8 },
            seq(if op == 0xA2 || op == 0xA3 { Rax::Keep } else { Rax::Clobber }),
        ),
        0xA8 => with_imm(r, 1, seq(Rax::Keep)),
        0xA9 => with_imm(r, imm_z(p), seq(Rax::Keep)),
        0xA4..=0xAF => Some(Info {
            kind: if p.rep { Kind::Rep } else { Kind::Seq },
            rax: if op == 0xAC || op == 0xAD { Rax::Clobber } else { Rax::Keep },
        }),
        0xB0..=0xB7 => with_imm(r, 1, seq(keep_if_not(p, true, op - 0xB0 + 8 * p.b()))),
        0xB8..=0xBF => {
            let n = if p.w() { 8 } else { imm_z(p) };
            let v = r.le(n)?;
            Some(seq(if op == 0xB8 && p.b() == 0 {
                if p.opsz { Rax::Clobber } else { Rax::Set(v) }
            } else {
                Rax::Keep
            }))
        }
        0xC0 | 0xC1 => with_modrm(r, 1, |m| rm_dest(p, op == 0xC0, m)),
        0xC2 => with_imm(r, 2, other()),
        0xC3 => Some(Info { kind: Kind::Ret, rax: Rax::Keep }),
        0xC4 | 0xC5 => None,
        0xC6 => with_modrm(r, 1, |m| rm_dest(p, true, m)),
        0xC7 => {
            let m = modrm(r)?;
            if m.md == 3 && m.reg == 7 {
                r.le(imm_z(p))?;
                Some(other())
            } else {
                let v = r.le(imm_z(p))?;
                Some(seq(if m.md == 3 && m.rm + 8 * p.b() == 0 && !p.opsz {
                    if p.w() {
                        Rax::Set(if v < (1 << 31) { v } else { v + (u64::MAX - 0xFFFF_FFFF) })
                    } else {
                        Rax::Set(v)
                    }
                } else {
                    rm_dest(p, false, &m)
                }))
            }
        }
        0xC8 => with_imm(r, 3, seq(Rax::Keep)),
        0xC9 => Some(seq(Rax::Keep)),
        0xCA => with_imm(r, 2, other()),
        0xCB => Some(other()),
        0xCC => Some(Info { kind: Kind::Trap, rax: Rax::Keep }),
        0xCD => with_imm(r, 1, Info { kind: Kind::SysOther, rax: Rax::Clobber }),
        0xCE => None,
        0xCF => Some(other()),
        0xD0..=0xD3 => with_modrm(r, 0, |m| rm_dest(p, op == 0xD0 || op == 0xD2, m)),
        0xD4..=0xD6 => None,
        0xD7 => Some(seq(Rax::Clobber)),
        0xD8..=0xDF => with_modrm(r, 0, |_| Rax::Clobber),
        0xE0..=0xE3 => {
            let d = r.byte()?;
            Some(ji(Kind::Jcc(sx(1, d))))
        }
        0xE4..=0xE7 => with_imm(r, 1, other()),
        0xE8 => {
            let d = r.le(4)?;
            Some(if p.opsz { other() } else { ji(Kind::Call(sx(4, d))) })
        }
        0xE9 => {
            let d = r.le(4)?;
            Some(if p.opsz { other() } else { ji(Kind::Jmp(sx(4, d))) })
        }
        0xEA => None,
        0xEB => {
            let d = r.byte()?;
            Some(ji(Kind::Jmp(sx(1, d))))
        }
        0xEC..=0xEF => Some(other()),
        0xF1 | 0xF4 => Some(Info { kind: Kind::Trap, rax: Rax::Keep }),
        0xF5 => Some(seq(Rax::Keep)),
        0xF6 | 0xF7 => {
            let m = modrm(r)?;
            let n = if m.reg < 2 { if op == 0xF6 { 1 } else { imm_z(p) } } else { 0 };
            r.le(n)?;
            Some(seq(if m.reg < 2 {
                Rax::Keep
            } else if m.reg < 4 {
                rm_dest(p, op == 0xF6, &m)
            } else {
                Rax::Clobber
            }))
        }
        0xF8..=0xFD => Some(seq(Rax::Keep)),
        0xFE => with_modrm(r, 0, |m| if m.reg < 2 { rm_dest(p, true, m) } else { Rax::Clobber }),
        0xFF => {
            let m = modrm(r)?;
            match m.reg {
                2 => Some(ji(Kind::CallInd(opnd(p, &m)))),
                4 => Some(ji(Kind::JmpInd(opnd(p, &m)))),
                3 | 5 => Some(other()),
                6 => Some(seq(Rax::Keep)),
                7 => None,
                _ => Some(seq(rm_dest(p, false, &m))),
            }
        }
        _ => None, // F0, F2, F3 (prefixes) never reach here
    }
}

fn map0f(r: &mut Rd, p: &Pfx, op: u64) -> R<Info> {
    let fail_set = [
        0x0F, 0x04, 0x0A, 0x0C, 0x24, 0x25, 0x26, 0x27, 0x36, 0x39, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,
        0x7A, 0x7B, 0xA6, 0xA7,
    ];
    let other_set = [0x06, 0x08, 0x09, 0x0E, 0x30, 0x37, 0xAA];
    if op == 0x05 {
        return Some(Info { kind: Kind::Syscall, rax: Rax::Clobber });
    }
    if op == 0x0B {
        return Some(Info { kind: Kind::Trap, rax: Rax::Keep });
    }
    if op == 0x34 {
        return Some(Info { kind: Kind::SysOther, rax: Rax::Clobber });
    }
    if op == 0x07 || op == 0x35 {
        return Some(other());
    }
    if fail_set.contains(&op) {
        return None;
    }
    if other_set.contains(&op) {
        return Some(other());
    }
    if matches!(op, 0x31 | 0x32 | 0x33 | 0xA2) {
        return Some(seq(Rax::Clobber));
    }
    if matches!(op, 0x77 | 0xA0 | 0xA8 | 0xA1 | 0xA9) {
        return Some(seq(Rax::Keep));
    }
    if (0x80..0x90).contains(&op) {
        let d = r.le(4)?;
        return Some(if p.opsz { other() } else { Info { kind: Kind::Jcc(sx(4, d)), rax: Rax::Keep } });
    }
    if (0xC8..0xD0).contains(&op) {
        return Some(seq(keep_if_not(p, false, op - 0xC8 + 8 * p.b())));
    }
    if (0x20..0x24).contains(&op) {
        return with_modrm(r, 0, |_| Rax::Clobber);
    }
    if op == 0xB9 || op == 0xFF {
        modrm(r)?;
        return Some(Info { kind: Kind::Trap, rax: Rax::Keep });
    }
    if op == 0x0D || (0x18..0x20).contains(&op) {
        return with_modrm(r, 0, |_| Rax::Keep);
    }
    if (0x70..0x74).contains(&op) || matches!(op, 0xA4 | 0xAC | 0xBA | 0xC2 | 0xC4 | 0xC5 | 0xC6) {
        return with_modrm(r, 1, |m| {
            if op == 0xA4 || op == 0xAC {
                rm_dest(p, false, m)
            } else if op == 0xBA {
                if m.reg == 4 { Rax::Keep } else { rm_dest(p, false, m) }
            } else {
                Rax::Clobber
            }
        });
    }
    if (0x40..0x50).contains(&op) {
        return with_modrm(r, 0, |m| reg_dest(p, false, m));
    }
    if (0x90..0xA0).contains(&op) {
        return with_modrm(r, 0, |m| rm_dest(p, true, m));
    }
    if op == 0xA3 {
        return with_modrm(r, 0, |_| Rax::Keep);
    }
    if matches!(op, 0xAB | 0xB3 | 0xBB | 0xA5 | 0xAD) {
        return with_modrm(r, 0, |m| rm_dest(p, false, m));
    }
    if matches!(op, 0xAF | 0xB6 | 0xB7 | 0xBE | 0xBF | 0xBC | 0xBD | 0xB8) {
        return with_modrm(r, 0, |m| reg_dest(p, false, m));
    }
    with_modrm(r, 0, |_| Rax::Clobber)
}

fn vex_body(r: &mut Rd, map: u64, op: u64) -> R<Info> {
    if map == 1 && op == 0x77 {
        return Some(seq(Rax::Keep));
    }
    let imm = map == 3 || (map == 1 && ((0x70..0x74).contains(&op) || matches!(op, 0xC2 | 0xC4 | 0xC5 | 0xC6)));
    with_modrm(r, if imm { 1 } else { 0 }, |_| Rax::Clobber)
}

fn vex(r: &mut Rd, esc: u64) -> R<Info> {
    if esc == 0xC5 {
        r.byte()?;
        let op = r.byte()?;
        vex_body(r, 1, op)
    } else if esc == 0xC4 {
        let b1 = r.byte()?;
        r.byte()?;
        let op = r.byte()?;
        let map = b1 % 32;
        if matches!(map, 1 | 2 | 3) { vex_body(r, map, op) } else { None }
    } else {
        let p0 = r.byte()?;
        r.byte()?;
        r.byte()?;
        let op = r.byte()?;
        let map = p0 % 8;
        if matches!(map, 1 | 2 | 3 | 5 | 6) { vex_body(r, map, op) } else { None }
    }
}

fn after_pfx(r: &mut Rd, p: &Pfx, b: u64) -> R<Info> {
    if b == 0x0F {
        let op = r.byte()?;
        if op == 0x38 {
            r.byte()?;
            with_modrm(r, 0, |_| Rax::Clobber)
        } else if op == 0x3A {
            r.byte()?;
            with_modrm(r, 1, |_| Rax::Clobber)
        } else {
            map0f(r, p, op)
        }
    } else if matches!(b, 0xC4 | 0xC5 | 0x62) && p.rex.is_none() && !p.opsz && !p.rep {
        vex(r, b)
    } else {
        map1(r, p, b)
    }
}

fn rex_then(r: &mut Rd, p: &Pfx, b: u64) -> R<Info> {
    if (0x40..0x50).contains(&b) {
        let op = r.byte()?;
        let q = Pfx { rex: Some(b), ..*p };
        after_pfx(r, &q, op)
    } else {
        after_pfx(r, p, b)
    }
}

fn pfx(r: &mut Rd, k: u32, mut p: Pfx) -> R<Info> {
    for _ in 0..k {
        let b = r.byte()?;
        if is_legacy(b) {
            p.opsz |= b == 0x66;
            p.adsz |= b == 0x67;
            p.rep |= b == 0xF2 || b == 0xF3;
        } else {
            return rex_then(r, &p, b);
        }
    }
    None
}

fn instr(w: &[u8]) -> Option<(Info, usize)> {
    let mut r = Rd { b: w, p: 0 };
    let i = pfx(&mut r, 15, Pfx::default())?;
    Some((i, r.p))
}

/// `X64.decode`: the shortest prefix (at most 15 bytes) the reader consumes entirely.
pub fn decode(w: &[u8]) -> Option<(Info, usize)> {
    for l in 1..=15usize {
        if l > w.len() {
            return None;
        }
        if let Some((i, n)) = instr(&w[..l]) {
            if n == l {
                return Some((i, l));
            }
        }
    }
    None
}
