//! Instruction boundaries of a byte range of an x86-64 file, by iced-x86's linear sweep, as
//! `offset length` lines (hex file offset, decimal length), the format of
//! `boundaries-objdump.sh`.
//!
//!     iced-boundaries FILE OFFSET SIZE VADDR      (numbers in hex with 0x, or decimal)
use iced_x86::{Decoder, DecoderOptions};
use std::io::Write;

fn num(s: &str) -> u64 {
    match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16).expect("hex"),
        None => s.parse().expect("number"),
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 5 {
        eprintln!("usage: iced-boundaries FILE OFFSET SIZE VADDR");
        std::process::exit(2);
    }
    let bytes = std::fs::read(&a[1]).expect("read");
    let (off, size, vaddr) = (num(&a[2]) as usize, num(&a[3]) as usize, num(&a[4]));
    let code = &bytes[off..off + size];
    let mut dec = Decoder::with_ip(64, code, vaddr, DecoderOptions::NONE);
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());
    let mut pos = off;
    while dec.can_decode() {
        let insn = dec.decode();
        writeln!(out, "{:#x} {}", pos, insn.len()).unwrap();
        pos += insn.len();
    }
}
