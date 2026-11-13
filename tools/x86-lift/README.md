# lift-x86: x86-64 bytes as instructions of the Lean model

`lift-x86` is a Rust library that decodes x86-64 machine code into `Silmaril.X86.Ext.Instr`,
the instruction syntax of Silmaril's extended x86-64 model (`Silmaril/X86/Ext/Syntax.lean`),
and prints each instruction as a Lean term. [`tools/c-tv`](../c-tv/README.md) uses it for the
listings of the Lean headers it generates. This directory holds only this decoder; the
transcription generator that `Silmaril/X86/Lift/Transcript.lean` mentions is not part of it.

```rust
// Every instruction of `code`, placed at address 0, or the first one it refuses.
for x in lift_x86::lift(code, 0)? {
    println!("({:#x}, {}, {})  -- {}", x.addr, x.instr.lean(), x.len(), x.asm);
}
```

`lift(bytes, base)` reads the bytes front to back:

1. iced-x86 decodes the next instruction (linear sweep from `base`);
2. `from_iced::map` maps iced's instruction form (its `Code`, such as `Add_rm32_imm8`) and
   operands to `ext::Instr`. What the model does not have is refused: a form outside it (named
   by its `Code`), the `8B` load with a register source, high-byte registers, segment overrides
   other than `fs`, 32-bit addressing;
3. `encode::encode`, a Rust port of the model's `Ext.encode`, re-encodes the instruction. Bytes
   that are not its canonical encoding (a redundant prefix, a non-minimal displacement, …) are
   refused: the Lean decoder `Ext.decode` accepts only canonical encodings.

Each error names the address and the bytes, with iced's AT&T text when iced decodes them. A
`Lifted` instruction holds its address, bytes, `Instr` and AT&T text; `Lifted::flow` and
`Lifted::node` give its control flow (`cfg::Flow`, `cfg::Node`) as `Silmaril.X86.Decompile`
computes it (`Decoded.edges`, `Decoded.cfgTargets`), modulo 2^64.

Nothing here is trusted. A Lean module that states a listing checks it against the model's
decoder (c-tv's headers do so by `decide +kernel`); the encoder port only keeps a refused
instruction out of a slow Lean build. `ext.rs` and `encode.rs` mirror the Lean syntax and
encoder one for one, so a change to `Silmaril/X86/Ext/Syntax.lean`, `Encoding.lean` or
`Raw.lean` must be made here too; a Lean check of a listing fails otherwise.

Build and test (Rust 1.98 or later):

```sh
cd tools/x86-lift
cargo build --locked
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
```

The tests check known encodings of the encoder port, the flow types, and in `tests/lift.rs`
hand-picked encodings and refusals (exact lengths and fall-through addresses, address
wrap-around, register matrices) and gcc's `-O0` and `-O2` code for a small C function.
