module

public import Silmaril.Wasm.Examples.RustAdder.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

/-!
# The compiled Rust adder: its bytes decode to its module

`decode_eq`: silmaril-lean's binary decoder, run by the kernel on the 124 bytes of
`examples/wasm-demos/rust-adder/wasm/adder.wasm`, returns `module` (the term printed by
`tools/wasm-to-lean`); `encodes`: hence, by the decoder's soundness theorem
(`Decode.decodeModule_sound`), the bytes are a binary encoding of `module` in silmaril-lean's
`Encodes` relation.
-/

namespace Silmaril.Wasm.Examples.RustAdder

open Silmaril.Wasm Silmaril.Wasm.Binary.Core

/-- The decoder maps the compiled bytes to `module` (kernel evaluation). -/
theorem decode_eq : Decode.decodeModule bytes = .ok module := by kernel_rfl

/-- The compiled bytes encode `module`. -/
theorem encodes : Encodes bytes.data.toList module := Decode.decodeModule_sound decode_eq

end Silmaril.Wasm.Examples.RustAdder
