module

public import Silmaril.Proofs.Wasm.Models.FXSurplusK.Example
public import Silmaril.Wasm.Models.FXAsyncSus.Thms

/-!
# The example is outside the tight fragment, and the tight condition is needed

`FXAsyncSus.beh_eq_tight` would give `sk_not_beh_eq` the other way, so the kernel run of `skW`
is not tight (`sk_not_tight`): the tight hypothesis of `beh_eq_tight` cannot be dropped, even
when `Ok`, `Rel` and `Supported` hold.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplusK

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- **The kernel run of `skW` is not tight** (its first `suspend` finds three operands). -/
theorem sk_not_tight (o : GrowKind → Nat → Nat → Nat → Bool) :
    ¬ TightSupported skW skInit := fun hsup =>
  sk_not_beh_eq (Profile.deterministic o) noHost
    (Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight (skS (Profile.deterministic o) noHost) rfl rfl
      (skOk _ _) (Silmaril.Proofs.Wasm.Models.FXAsyncFX.rel_init _ 1 []) hsup)

end Silmaril.Proofs.Wasm.Models.FXSurplusK
