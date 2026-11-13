//! Assemble the threads of a test with GNU `as` and read the bytes back from the ELF object.
//!
//! Each instruction goes into its own section (`.t<thread>_<index>`), so the tool records
//! per-instruction bytes; a thread's code is their concatenation (the corpus has no branches,
//! so the code is position-independent). An object with any relocation section is rejected:
//! every memory operand is an absolute 32-bit address.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::litmus::Error;
use crate::model::Model;

/// Per thread, per instruction: the gas text and its bytes.
pub type Assembled = Vec<Vec<(String, Vec<u8>)>>;

fn u16le(b: &[u8], o: usize) -> Result<u16, Error> {
    b.get(o..o + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]))
        .ok_or_else(|| Error("truncated ELF".into()))
}
fn u32le(b: &[u8], o: usize) -> Result<u32, Error> {
    b.get(o..o + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        .ok_or_else(|| Error("truncated ELF".into()))
}
fn u64le(b: &[u8], o: usize) -> Result<u64, Error> {
    let s = b
        .get(o..o + 8)
        .ok_or_else(|| Error("truncated ELF".into()))?;
    let mut a = [0u8; 8];
    a.copy_from_slice(s);
    Ok(u64::from_le_bytes(a))
}

/// The sections of an ELF64 little-endian relocatable object: (name, type, contents).
pub fn sections(elf: &[u8]) -> Result<Vec<(String, u32, Vec<u8>)>, Error> {
    if elf.get(0..6) != Some(&[0x7f, b'E', b'L', b'F', 2, 1][..]) {
        return Err(Error("not an ELF64 little-endian object".into()));
    }
    let shoff = u64le(elf, 0x28)? as usize;
    let shentsize = u16le(elf, 0x3a)? as usize;
    let shnum = u16le(elf, 0x3c)? as usize;
    let shstrndx = u16le(elf, 0x3e)? as usize;
    let hdr = |i: usize| shoff + i * shentsize;
    let strtab_off = u64le(elf, hdr(shstrndx) + 0x18)? as usize;
    let mut out = Vec::new();
    for i in 0..shnum {
        let h = hdr(i);
        let name_off = u32le(elf, h)? as usize;
        let ty = u32le(elf, h + 4)?;
        let off = u64le(elf, h + 0x18)? as usize;
        let size = u64le(elf, h + 0x20)? as usize;
        let start = strtab_off + name_off;
        let end = elf[start..]
            .iter()
            .position(|&c| c == 0)
            .ok_or_else(|| Error("bad section name".into()))?;
        let name = String::from_utf8_lossy(&elf[start..start + end]).into_owned();
        // SHT_NOBITS (8) has no file contents.
        let data = if ty == 8 {
            Vec::new()
        } else {
            elf.get(off..off + size)
                .ok_or_else(|| Error("section outside file".into()))?
                .to_vec()
        };
        out.push((name, ty, data));
    }
    Ok(out)
}

/// The assembler source for a test.
pub fn source(m: &Model) -> Result<(String, Vec<Vec<String>>), Error> {
    let addrs = m.addrs();
    let mut s = String::from("\t.text\n");
    let mut texts = Vec::new();
    for (t, (insns, _)) in m.threads.iter().enumerate() {
        let mut tx = Vec::new();
        for (k, i) in insns.iter().enumerate() {
            let g = i.gas(&addrs)?;
            s.push_str(&format!("\t.section .t{t}_{k},\"ax\",@progbits\n\t{g}\n"));
            tx.push(g);
        }
        texts.push(tx);
    }
    Ok((s, texts))
}

/// Assemble a test in `dir` with the assembler `asm`.
pub fn assemble(m: &Model, asm: &Path, dir: &Path) -> Result<Assembled, Error> {
    let (src, texts) = source(m)?;
    let tag: String = m
        .name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let s_path: PathBuf = dir.join(format!("{tag}.s"));
    let o_path: PathBuf = dir.join(format!("{tag}.o"));
    std::fs::write(&s_path, &src).map_err(|e| Error(format!("write {}: {e}", s_path.display())))?;
    let out = Command::new(asm)
        .arg("--64")
        .arg("-o")
        .arg(&o_path)
        .arg(&s_path)
        .output()
        .map_err(|e| Error(format!("run {}: {e}", asm.display())))?;
    if !out.status.success() || !out.stderr.is_empty() {
        return Err(Error(format!(
            "{}: assembler failed or warned:\n{}",
            m.name,
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    let elf =
        std::fs::read(&o_path).map_err(|e| Error(format!("read {}: {e}", o_path.display())))?;
    let _ = std::fs::remove_file(&s_path);
    let _ = std::fs::remove_file(&o_path);
    let secs = sections(&elf)?;
    // SHT_REL = 9, SHT_RELA = 4.
    if let Some((n, _, _)) = secs
        .iter()
        .find(|(_, ty, d)| (*ty == 4 || *ty == 9) && !d.is_empty())
    {
        return Err(Error(format!(
            "{}: unexpected relocation section {n}",
            m.name
        )));
    }
    let mut res = Vec::new();
    for (t, tx) in texts.into_iter().enumerate() {
        let mut th = Vec::new();
        for (k, g) in tx.into_iter().enumerate() {
            let want = format!(".t{t}_{k}");
            let bytes = secs
                .iter()
                .find(|(n, _, _)| *n == want)
                .map(|(_, _, d)| d.clone())
                .ok_or_else(|| Error(format!("{}: missing section {want}", m.name)))?;
            if bytes.is_empty() || bytes.len() > 15 {
                return Err(Error(format!(
                    "{}: `{g}` assembled to {} bytes",
                    m.name,
                    bytes.len()
                )));
            }
            th.push((g, bytes));
        }
        res.push(th);
    }
    Ok(res)
}

/// The first line of `as --version`.
pub fn version(asm: &Path) -> Result<String, Error> {
    let out = Command::new(asm)
        .arg("--version")
        .output()
        .map_err(|e| Error(format!("run {}: {e}", asm.display())))?;
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .next()
        .unwrap_or("")
        .to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_non_elf() {
        assert!(sections(b"not an elf at all, really").is_err());
    }
}
