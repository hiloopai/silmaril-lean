module

public import Silmaril.Proofs.Wasm.Component.Lime1Ref.Call

/-!
# The engine-run half for Lime1, and the reduction

* Facts for the engine-run half (used by `Lime1Bridge.specSub_of_instBridgeE`): a Core
  behaviour of a returned or trapping result comes from a finite run (`result_of_beh`), and a
  divergence behaviour from a divergence (`diverges_of_beh`). The Lime1 results read back
  unchanged through `toFlat?` (`mapM_toFlat`).
* `refToSpecOn_of_specE`: for any engine, the machine half against the engine's own
  specification and the engine-run half give the reference-machine half on a domain.

New proofs.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Runtime (Value)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

theorem toCore_eq_ofFlat : Value.toCore = Silmaril.Wasm.SingleThreaded.ofFlat := rfl

theorem mapM_toFlat (ys : List Value) :
    (ys.map Value.toCore).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [Silmaril.Wasm.SingleThreaded.toFlat?, Value.toCore, ih]

/-- A Core behaviour that is a returned (or trapping) behaviour comes from a finite run. -/
theorem result_of_beh {S : Silmaril.Wasm.Execution.Core.Store Nat} {a : Nat}
    {vs : List Silmaril.Wasm.Execution.Core.Val} {res : Silmaril.Wasm.Execution.Core.Result}
    (hres : res = .trap ∨ ∃ us, res = .values us)
    (hb : res.toBehaviour ∈ Silmaril.Wasm.Execution.Core.behaviours Profile.spec
      Silmaril.Wasm.SingleThreaded.Det.noHost S a vs) :
    ∃ c', Silmaril.Wasm.Execution.Core.Steps Profile.spec Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke S a vs) c' ∧ c'.code = res.toAdmin := by
  rcases hb with ⟨c', res', run, hc, he⟩ | ⟨he, -⟩
  · refine ⟨c', run, ?_⟩
    rcases hres with rfl | ⟨us, rfl⟩ <;> cases res' <;>
      simp_all [Silmaril.Wasm.Execution.Core.Result.toBehaviour]
  · rcases hres with rfl | ⟨us, rfl⟩ <;> cases he

/-- A Core divergence behaviour is a divergence. -/
theorem diverges_of_beh {S : Silmaril.Wasm.Execution.Core.Store Nat} {a : Nat}
    {vs : List Silmaril.Wasm.Execution.Core.Val}
    (hb : Silmaril.Wasm.Behaviour.diverges ∈ Silmaril.Wasm.Execution.Core.behaviours Profile.spec
      Silmaril.Wasm.SingleThreaded.Det.noHost S a vs) :
    Silmaril.Wasm.Execution.Core.Diverges Profile.spec Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke S a vs) := by
  rcases hb with ⟨c', res, -, -, he⟩ | ⟨-, hd⟩
  · cases res <;> cases he
  · exact hd

/-- **The reduction**: the machine half against the engine's own specification and the
engine-run half give the reference-machine half on a domain. -/
theorem refToSpecOn_of_specE {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} {emb : NumModule → E.Module} {P : Profile}
    {D : Simple → Prop} (hR : RefToSpecEOn E ofCore emb D) (hS : SpecSubOn E emb P D) :
    RefToSpecOn E ofCore P D :=
  fun prof c hD hc hf hi ha x hx vs hvs _ hb =>
    hS c hD hc hi x hx vs (hR prof c hD hc hf hi ha x hx vs hvs hb)

end Silmaril.Proofs.Wasm.Component.Lime1Ref
