//! A minimal reader for ELF64 little-endian x86-64 relocatable objects (`ET_REL`), enough to
//! take thread functions out of a compiled `.o`: section headers, the symbol table and the
//! `RELA` relocation sections.
//!
//! Only what `src/ingest.rs` needs is decoded. Anything else (big-endian, 32-bit, other
//! machines, `REL` sections, compressed sections) is rejected with an error, never guessed.

use crate::litmus::Error;

/// `SHT_PROGBITS`.
pub const SHT_PROGBITS: u32 = 1;
/// `SHT_SYMTAB`.
pub const SHT_SYMTAB: u32 = 2;
/// `SHT_RELA`.
pub const SHT_RELA: u32 = 4;
/// `SHT_NOBITS` (`.bss`).
pub const SHT_NOBITS: u32 = 8;
/// `SHF_WRITE`.
pub const SHF_WRITE: u64 = 1;
/// `SHF_ALLOC`.
pub const SHF_ALLOC: u64 = 2;
/// `SHF_EXECINSTR`.
pub const SHF_EXECINSTR: u64 = 4;
/// `STT_OBJECT`.
pub const STT_OBJECT: u8 = 1;
/// `STT_FUNC`.
pub const STT_FUNC: u8 = 2;
/// `R_X86_64_PC32`.
pub const R_X86_64_PC32: u32 = 2;
/// `R_X86_64_PLT32`.
pub const R_X86_64_PLT32: u32 = 4;

/// A section header.
#[derive(Clone, Debug)]
pub struct Section {
    pub name: String,
    pub kind: u32,
    pub flags: u64,
    pub offset: u64,
    pub size: u64,
    pub link: u32,
    pub info: u32,
}

/// A symbol.
#[derive(Clone, Debug)]
pub struct Symbol {
    pub name: String,
    /// `STT_*`.
    pub kind: u8,
    /// Section index (`0` = undefined, `>= 0xff00` = special).
    pub shndx: u16,
    pub value: u64,
    pub size: u64,
}

/// A relocation with addend.
#[derive(Clone, Debug)]
pub struct Rela {
    /// Offset in the section the relocation applies to.
    pub offset: u64,
    /// Index into [`Object::symbols`].
    pub sym: usize,
    pub kind: u32,
    pub addend: i64,
}

/// A parsed relocatable object.
#[derive(Clone, Debug)]
pub struct Object {
    pub bytes: Vec<u8>,
    pub sections: Vec<Section>,
    pub symbols: Vec<Symbol>,
    /// Per section index: the relocations that apply to it.
    pub relas: Vec<Vec<Rela>>,
}

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

fn rd(b: &[u8], off: u64, n: usize) -> Result<u64, Error> {
    let o = usize::try_from(off).map_err(|_| Error("ELF offset overflow".into()))?;
    let s = b
        .get(
            o..o.checked_add(n)
                .ok_or_else(|| Error("ELF offset overflow".into()))?,
        )
        .ok_or_else(|| Error(format!("ELF read past the end at {off:#x}")))?;
    Ok(s.iter().rev().fold(0u64, |a, x| (a << 8) | u64::from(*x)))
}

fn cstr(b: &[u8], off: u64) -> Result<String, Error> {
    let o = usize::try_from(off).map_err(|_| Error("ELF offset overflow".into()))?;
    let tail = b
        .get(o..)
        .ok_or_else(|| Error("ELF string past the end".into()))?;
    let end = tail
        .iter()
        .position(|c| *c == 0)
        .ok_or_else(|| Error("unterminated ELF string".into()))?;
    String::from_utf8(tail[..end].to_vec()).map_err(|_| Error("non-UTF-8 ELF string".into()))
}

impl Object {
    /// Parse an ELF64 LE x86-64 `ET_REL` object.
    pub fn parse(bytes: Vec<u8>) -> Result<Object, Error> {
        let b = &bytes;
        if b.get(0..4) != Some(b"\x7fELF") {
            return err("not an ELF file");
        }
        if b.get(4) != Some(&2) || b.get(5) != Some(&1) {
            return err("not ELF64 little-endian");
        }
        if rd(b, 16, 2)? != 1 {
            return err("not a relocatable object (ET_REL)");
        }
        if rd(b, 18, 2)? != 62 {
            return err("not an x86-64 object (EM_X86_64)");
        }
        let shoff = rd(b, 0x28, 8)?;
        let shentsize = rd(b, 0x3a, 2)?;
        let shnum = rd(b, 0x3c, 2)?;
        let shstrndx = rd(b, 0x3e, 2)?;
        if shentsize != 64 {
            return err("unexpected section header size");
        }
        let mut raw = Vec::new();
        for i in 0..shnum {
            let h = shoff + 64 * i;
            raw.push((
                rd(b, h, 4)?,
                rd(b, h + 4, 4)? as u32,
                rd(b, h + 8, 8)?,
                rd(b, h + 0x18, 8)?,
                rd(b, h + 0x20, 8)?,
                rd(b, h + 0x28, 4)? as u32,
                rd(b, h + 0x2c, 4)? as u32,
            ));
        }
        let strtab_off = raw
            .get(shstrndx as usize)
            .ok_or_else(|| Error("bad section-name table index".into()))?
            .3;
        let mut sections = Vec::new();
        for (name, kind, flags, offset, size, link, info) in &raw {
            if flags & 0x800 != 0 {
                return err("compressed sections are not supported");
            }
            if *kind == 9 {
                return err("REL (no addend) relocations are not supported");
            }
            sections.push(Section {
                name: cstr(b, strtab_off + name)?,
                kind: *kind,
                flags: *flags,
                offset: *offset,
                size: *size,
                link: *link,
                info: *info,
            });
        }
        let symtabs: Vec<usize> = (0..sections.len())
            .filter(|&i| sections[i].kind == SHT_SYMTAB)
            .collect();
        let [st] = symtabs.as_slice() else {
            return err("expected exactly one symbol table");
        };
        let st = &sections[*st];
        let names = sections
            .get(st.link as usize)
            .ok_or_else(|| Error("bad symbol string table".into()))?
            .offset;
        let mut symbols = Vec::new();
        for k in 0..st.size / 24 {
            let e = st.offset + 24 * k;
            let info = rd(b, e + 4, 1)? as u8;
            symbols.push(Symbol {
                name: cstr(b, names + rd(b, e, 4)?)?,
                kind: info & 0xf,
                shndx: rd(b, e + 6, 2)? as u16,
                value: rd(b, e + 8, 8)?,
                size: rd(b, e + 16, 8)?,
            });
        }
        let mut relas = vec![Vec::new(); sections.len()];
        for s in &sections {
            if s.kind != SHT_RELA {
                continue;
            }
            let target = s.info as usize;
            if target >= sections.len() {
                return err("relocation section for a missing section");
            }
            for k in 0..s.size / 24 {
                let e = s.offset + 24 * k;
                let info = rd(b, e + 8, 8)?;
                let sym = (info >> 32) as usize;
                if sym >= symbols.len() {
                    return err("relocation against a missing symbol");
                }
                relas[target].push(Rela {
                    offset: rd(b, e, 8)?,
                    sym,
                    kind: info as u32,
                    addend: rd(b, e + 16, 8)? as i64,
                });
            }
        }
        Ok(Object {
            bytes,
            sections,
            symbols,
            relas,
        })
    }

    /// The contents of a section (`None` for `SHT_NOBITS`).
    pub fn section_bytes(&self, i: usize) -> Result<Option<&[u8]>, Error> {
        let s = &self.sections[i];
        if s.kind == SHT_NOBITS {
            return Ok(None);
        }
        let (o, n) = (s.offset as usize, s.size as usize);
        self.bytes
            .get(o..o + n)
            .map(Some)
            .ok_or_else(|| Error(format!("section {} past the end of the file", s.name)))
    }

    /// The defined symbol of the given name and kind.
    pub fn defined(&self, name: &str, kind: u8) -> Option<&Symbol> {
        self.symbols.iter().find(|s| {
            s.name == name && s.kind == kind && s.shndx != 0 && (s.shndx as usize) < 0xff00
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_non_elf() {
        assert!(Object::parse(b"\x7fELG".to_vec()).is_err());
        assert!(Object::parse(vec![0x7f, b'E', b'L', b'F', 1, 1]).is_err());
    }
}
