module

/-!
# `var_u32` as wasmparser reads it

The unsigned LEB128 reader of wasmparser 0.262 (`BinaryReader::read_var_u32`, the reader of
`wasm-tools 1.262.0`) and the minimal encoder of wasm-encoder, on byte lists.

* `readU32 bs` reads one `var_u32` from the front of `bs`: at most five bytes; in the fifth byte
  the continuation bit and the bits above bit 31 must be clear (otherwise "integer representation
  too long" or "integer too large"). Non-minimal encodings within five bytes are accepted.
* `encU32 n` is the minimal encoding (wasm-encoder's `encode` of a `u32`/`usize`).

Theorems (`Silmaril.Wasm.Tools.Meta.Leb.Thms`): `readU32_encU32` (the reader inverts the encoder
below `2^32`), `readU32_lt` (results are below `2^32`) and `readU32_suffix` (the reader consumes
a prefix).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- The error messages of wasmparser's reader that the tools here can produce. -/
def errEof : String := "unexpected end-of-file"

/-- The continuation bytes of a `var_u32`: `acc` holds the bits read so far, `shift` their
count (7, 14, 21 or 28). -/
def readU32Go (acc shift : Nat) : List UInt8 → Except String (Nat × List UInt8)
  | [] => .error errEof
  | b :: bs =>
    let acc' := acc + b.toNat % 128 * 2 ^ shift
    if 25 ≤ shift ∧ b.toNat / 2 ^ (32 - shift) ≠ 0 then
      .error (if 128 ≤ b.toNat then "invalid var_u32: integer representation too long"
        else "invalid var_u32: integer too large")
    else if b.toNat < 128 then .ok (acc', bs) else readU32Go acc' (shift + 7) bs

/-- wasmparser's `read_var_u32`: one unsigned LEB128 `u32` and the rest of the input. -/
def readU32 : List UInt8 → Except String (Nat × List UInt8)
  | [] => .error errEof
  | b :: bs => if b.toNat < 128 then .ok (b.toNat, bs) else readU32Go (b.toNat % 128) 7 bs

/-- The minimal unsigned LEB128 encoding of `n` (wasm-encoder). -/
def encU32 (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encU32 (n / 128)
termination_by n
decreasing_by omega

end Silmaril.Wasm.Tools.Meta

end
