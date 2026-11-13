//! Decode x86-64 machine code into the instructions of Silmaril's Lean model.
//!
//! [`lift`] decodes a byte string placed at a base address by linear sweep with
//! iced-x86, maps each instruction into `Silmaril.X86.Ext.Instr` ([`ext`],
//! [`from_iced`]) and re-encodes it with a Rust port of `Ext.encode`
//! ([`encode`]), refusing any instruction whose bytes are not the model's
//! canonical encoding. The result is what `Silmaril.X86.Decompile`'s
//! `Region.decode` should produce on the same bytes. Nothing here is trusted: a
//! Lean module that states a listing checks it against the model's decoder.

pub mod cfg;
pub mod encode;
pub mod ext;
pub mod from_iced;

use anyhow::{Result, bail};
use iced_x86::{Decoder, DecoderOptions, Formatter, GasFormatter, Instruction};

use cfg::{Flow, Node};
pub use ext::Instr;

/// One lifted instruction.
#[derive(Clone, Debug)]
pub struct Lifted {
    /// The address of its first byte.
    pub addr: u64,
    /// Its bytes (`len = bytes.len()`).
    pub bytes: Vec<u8>,
    /// The instruction in the Lean model's syntax.
    pub instr: Instr,
    /// iced-x86's AT&T rendering, for comments.
    pub asm: String,
}

impl Lifted {
    /// The encoded length.
    pub fn len(&self) -> u64 {
        self.bytes.len() as u64
    }

    /// Never true: every instruction has at least one byte.
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// The fall-through address, modulo 2^64.
    pub fn next(&self) -> u64 {
        self.addr.wrapping_add(self.len())
    }

    /// The control flow out of this instruction, as `Decompile.Decoded.edges`
    /// computes it in Lean (targets are `next + sign-extended rel`, mod 2^64).
    pub fn flow(&self) -> Flow {
        let t32 = |r: u32| self.next().wrapping_add(r as i32 as i64 as u64);
        let t8 = |r: u8| self.next().wrapping_add(r as i8 as i64 as u64);
        match self.instr {
            Instr::Jmp(r) => Flow::Jump(t32(r)),
            Instr::Jmp8(r) => Flow::Jump(t8(r)),
            Instr::Jcc(_, r) => Flow::Branch(t32(r)),
            Instr::Jcc8(_, r) => Flow::Branch(t8(r)),
            Instr::Call(r) => Flow::Call(t32(r)),
            Instr::Ret => Flow::Ret,
            Instr::Ud2 => Flow::Halt,
            _ => Flow::Next,
        }
    }

    /// The instruction as a control-flow-graph builder sees it.
    pub fn node(&self) -> Node {
        Node {
            addr: self.addr,
            len: self.len(),
            flow: self.flow(),
        }
    }
}

/// Decode `bytes` placed at `base`, front to back, into the model.
///
/// Fails at the first instruction iced cannot decode, the model does not
/// contain, or whose bytes are not the model's canonical encoding — each error
/// names the address and the bytes.
pub fn lift(bytes: &[u8], base: u64) -> Result<Vec<Lifted>> {
    let mut decoder = Decoder::with_ip(64, bytes, base, DecoderOptions::NONE);
    let mut fmt = GasFormatter::new();
    let mut ins = Instruction::default();
    let mut out = Vec::new();
    while decoder.can_decode() {
        decoder.decode_out(&mut ins);
        let addr = ins.ip();
        let off = decoder.position() - ins.len();
        let raw = &bytes[off..off + ins.len()];
        let hex: String = raw.iter().map(|b| format!("{b:02x}")).collect();
        if ins.is_invalid() {
            bail!("{addr:#x}: iced cannot decode {hex}");
        }
        let mut asm = String::new();
        fmt.format(&ins, &mut asm);
        let instr =
            from_iced::map(&ins).map_err(|e| anyhow::anyhow!("{addr:#x}: {hex} ({asm}): {e}"))?;
        let enc = encode::encode(&instr);
        if enc != raw {
            let ehex: String = enc.iter().map(|b| format!("{b:02x}")).collect();
            bail!(
                "{addr:#x}: {hex} ({asm}) maps to {} whose canonical encoding is {ehex}; \
                 the Lean decoder would reject these bytes",
                instr.lean()
            );
        }
        out.push(Lifted {
            addr,
            bytes: raw.to_vec(),
            instr,
            asm,
        });
    }
    Ok(out)
}
