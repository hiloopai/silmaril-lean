module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEq

/-!
# The 2.0 script is clean at `$utf8`

`refFree20`: in `Scripts.Wasm20.fixed` (the script of `simEnv20 B`, without the `STORE` erratum)
only `$utf8`, the type `name` and the grammar `Bname` refer to `$utf8` (kernel). Hence
**`clean20`**: `simEnv20 B` is `Clean` at `$utf8`. The `fixedT20` counterpart is `clean20T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **Only `$utf8`, `name` and `Bname` refer to `$utf8` in the 2.0 script** (kernel). -/
theorem refFree20 : refFreeB "utf8" utf8Users20 Scripts.Wasm20.fixed = true := by
  decide +kernel

/-- **`simEnv20 B` never refers to `$utf8` outside `$utf8`.** -/
theorem clean20 (B : Builtins) : Clean (simEnv20 B) "utf8" :=
  clean_of_refFree refFree20 (fun x hx => by simp [utf8Users20, hx])
    (fun x => by simp [utf8Users20]) B

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
