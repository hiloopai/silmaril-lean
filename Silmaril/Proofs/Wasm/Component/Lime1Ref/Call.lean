module

public import Silmaril.Wasm.Component.Lime1Ref.Defs
public import Silmaril.Wasm.Models.Lime1Core.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Lime1 engine runs are Core 3.0 runs of the image store

The call phase of the engine-run half of `RefToSpecLime1`. An invocation of the Lime1
engine `lime1` takes only internal steps (no host functions), so its engine runs are runs of
`Silmaril.Wasm.Lime1.Execution` under the empty host `noHostL` (`steps_exec`, `diverges_exec`,
through the copied `Engine.Lime1.steps_bridge` and `diverges_bridge`). The copied Lime1 → Core
simulation (`Silmaril.Wasm.Models.Lime1Core.lime1_core_beh`, at `Profile.spec`) then makes every
returned or diverging run a Core 3.0 behaviour of the image store `s.toCore`
(`returned_core`, `diverges_core`). The Core host induced by `noHostL` is the empty Core host
(`liftHostC_noHostL`).

New proofs.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Ref

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1 toConfig HostStep)
open Silmaril.Wasm.Models.Lime1Core (behavioursL liftHostC)
open Silmaril.Wasm.Models.V10 (LStore LHost)
open Silmaril.Wasm.Component.Lime1Ref (noHostL)

theorem liftHostC_noHostL {H : Type} :
    liftHostC (noHostL (H := H)) = Silmaril.Wasm.SingleThreaded.Det.noHost := by
  funext h S args out
  simp [liftHostC, noHostL]

theorem hostSteps_of_steps {c c' : lime1.Config Nat} (run : Steps lime1 c c') :
    Silmaril.Wasm.Component.Engine.Lime1.HostSteps noHostL c c' := by
  induction run with
  | refl => exact .refl
  | tail _ hi ih => exact ih.tail (HostStep.internal hi)

theorem steps_exec {s s' : LStore Nat} {t t' : lime1.Thread Nat}
    (run : Steps lime1 (s, t) (s', t')) :
    Silmaril.Wasm.Lime1.Execution.Steps noHostL (toConfig (s, t)) (toConfig (s', t')) :=
  (Silmaril.Wasm.Component.Engine.Lime1.steps_bridge noHostL _ _).mp (hostSteps_of_steps run)

theorem diverges_exec {s : LStore Nat} {t : lime1.Thread Nat}
    (hd : Diverges lime1 (s, t)) :
    Silmaril.Wasm.Lime1.Execution.Diverges noHostL (toConfig (s, t)) :=
  (Silmaril.Wasm.Component.Engine.Lime1.diverges_bridge noHostL _).mpr
    (.inl (hd.map id fun _ _ hi => HostStep.internal hi))

theorem core_beh {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value) {b : Behaviour Value}
    (hb : b ∈ behavioursL noHostL s a xs) :
    b.map Value.toCore ∈ Silmaril.Wasm.Execution.Core.behaviours Silmaril.Wasm.Numerics.Profile.spec
      Silmaril.Wasm.SingleThreaded.Det.noHost s.toCore a.value (xs.map Value.toCore) := by
  rw [← liftHostC_noHostL]
  exact Silmaril.Wasm.Models.Lime1Core.lime1_core_beh hwf (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ _ h => h.elim) ha xs ⟨b, hb, rfl⟩

/-- A returned engine run of an invocation is a Core 3.0 behaviour of the image store. -/
theorem returned_core {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value) {s' : LStore Nat}
    {t' : lime1.Thread Nat} (run : Steps lime1 (s, lime1.invoke a xs) (s', t')) {r : CallResult}
    (hst : lime1.status s' t' = .returned r) :
    ((Silmaril.Wasm.Component.Engine.Lime1.toResult r).toBehaviour).map Value.toCore ∈
      Silmaril.Wasm.Execution.Core.behaviours Silmaril.Wasm.Numerics.Profile.spec
        Silmaril.Wasm.SingleThreaded.Det.noHost s.toCore a.value (xs.map Value.toCore) := by
  refine core_beh hwf ha xs (Or.inl ⟨toConfig (s', t'), _, steps_exec run, ?_, rfl⟩)
  exact Silmaril.Wasm.Lime1.Execution.terminal?_sound
    (Silmaril.Wasm.Component.Engine.Lime1.status_eq_returned hst)

/-- A diverging engine run of an invocation is a Core 3.0 divergence of the image store. -/
theorem diverges_core {s : LStore Nat} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (xs : List Value)
    (hd : Diverges lime1 (s, lime1.invoke a xs)) :
    Behaviour.diverges ∈
      Silmaril.Wasm.Execution.Core.behaviours Silmaril.Wasm.Numerics.Profile.spec
        Silmaril.Wasm.SingleThreaded.Det.noHost s.toCore a.value (xs.map Value.toCore) :=
  core_beh hwf ha xs (b := .diverges) (Or.inr ⟨rfl, diverges_exec hd⟩)

end Silmaril.Proofs.Wasm.Component.Lime1Ref
