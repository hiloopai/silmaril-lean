module

public import Silmaril.Wasm.Perf.CoreDecode.Defs
import Silmaril.Proofs.Wasm.Perf.CoreDecode.Eq

/-!
# The fast Core decoder is silmaril's decoder

`decodeF_eq : decodeF = Silmaril.Wasm.Binary.Core.decode?`, registered with `@[csimp]`
(`decode?_eq_decodeF`), and `decodeModule_eq`, `readModule_eq` on the way. The leaves are equal
because `a <<< s = a * 2 ^ s` and `n >>> N = 0 ↔ n < 2 ^ N`; every copied reader is then equal
to its original by rewriting the readers it calls and unfolding. The proofs, one `_eq` per
reader, are in `Silmaril.Proofs.Wasm.Perf.CoreDecode.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.CoreDecode

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem readModule_eq : readModule = Decode.readModule :=
  Silmaril.Proofs.Wasm.Perf.CoreDecode.readModule_eq

theorem decodeModule_eq : decodeModule = Decode.decodeModule :=
  Silmaril.Proofs.Wasm.Perf.CoreDecode.decodeModule_eq

/-- **The fast decoder is silmaril's decoder.** -/
theorem decodeF_eq : decodeF = decode? :=
  Silmaril.Proofs.Wasm.Perf.CoreDecode.decodeF_eq

/-- `decodeF_eq` for the compiler: code compiled in a module that imports this one calls
`decodeF` where its source says `decode?`. -/
@[csimp] theorem decode?_eq_decodeF : @decode? = @decodeF := decodeF_eq.symm

end Silmaril.Wasm.Perf.CoreDecode
