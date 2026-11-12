module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef

/-!
# Two components linked in the reference machine

`dblFwdL`: the doubler `dblS` answers the import `g` of `fwdS`. Its translation
`Linked2.toRef` (nested `component` definitions, `instantiate` with the exporter's aliased
export) is accepted by the reference validator (`dblFwdL_valid`), and over `core3 neverFail`
the call `f(3)` returns `6` (`dblFwd_ref`): the call of the importer's lifted `f` goes through its
`canon lower` of `g` into the exporter's `canon lift` and core code, inside the machine, with no
host function. Closed computations of the copied validator and drivers (`decide +kernel`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

theorem dblS_valid : ∃ ct, check? Features.p2 dblS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

theorem dblFwdL_valid : ∃ ct, check? Features.p2 dblFwdL.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- **The linked components compute `f(3) = 6`** in the reference machine. -/
theorem dblFwd_ref : Outcome.returns (some [toRefVal (.u32 6)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () dblFwdL.toRef [] "f"
      [toRefVal (.u32 3)] :=
  returns_of_summary (by decide +kernel)

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
