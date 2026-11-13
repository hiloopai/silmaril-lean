module

public import Silmaril.Wasm.Examples.CAdder.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

/-!
# The compiled C adder: its bytes decode to its module

`decode_eq`: silmaril-lean's binary decoder, run by the kernel on the 192 bytes of
`examples/wasm-demos/c-adder/wasm/adder.wasm`, returns `module` (the term printed by
`tools/wasm-to-lean`); `encodes`: hence, by the decoder's soundness theorem
(`Decode.decodeModule_sound`), the bytes are a binary encoding of `module`.
-/

namespace Silmaril.Wasm.Examples.CAdder

open Silmaril.Wasm Silmaril.Wasm.Binary.Core

/-- The decoder maps the compiled bytes to `module` (kernel evaluation). -/
theorem decode_eq : Decode.decodeModule bytes = .ok module := by kernel_rfl

/-- The compiled bytes encode `module`. -/
theorem encodes : Encodes bytes.data.toList module := Decode.decodeModule_sound decode_eq

end Silmaril.Wasm.Examples.CAdder
