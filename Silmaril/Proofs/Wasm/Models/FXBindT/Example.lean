module

public import Silmaril.Proofs.Wasm.Models.FXBindT.Behaviours

/-!
# The pass-1 counterexample under the typed `cont.bind`

An earlier step refuted the intended equality for the untyped `cont.bind` with the function
`first = (func (param i32 i32) (result i32) (local.get 0))` (`bind_ne_target`, and
`bind_ne_target'` for `StepFX'`). Here the same source runs in a frame whose module gives the
two continuation types `$ct = 0` (two parameters, the type of `first`) and `$ct' = 1` (one
parameter), so `cont.bind $ct $ct'` binds exactly one value:

* `firstF`, `oneD`: the frame and the one-parameter type;
* `firstF_arity`: `BindArity firstF.module 0 1 1`;
* **`bindT_first`** (deterministic profile, no host calls): under `StepFXT` the source's
  behaviours are those of the intended target `first y x`;
* **`bindT_first_not_x`**: so for `x ≠ y` the source no longer returns `[x]`, the behaviour that
  refuted the untyped lowering.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXBind (firstS firstD firstD_expand firstS_func first_returns_only)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- `(func (param i32) (result i32))` as a closed defined type. -/
def oneD : DefType :=
  .defn (.group (.cons (.sub true .nil (Ty.funcOf [Ty.i32] [Ty.i32])) .nil)) 0

/-- A frame whose module has the types `first` (index 0) and `oneD` (index 1). -/
def firstF : Frame := { module := { types := [firstD, oneD] } }

/-- `cont.bind 0 1` binds exactly one value in `firstF`. -/
theorem firstF_arity : BindArity firstF.module ⟨0⟩ ⟨1⟩ 1 := ⟨_, _, rfl, rfl, rfl⟩

/-- **Under the typed `cont.bind` the counterexample is the intended call.** -/
theorem bindT_first (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (x y : Val)
    (K : List (Option ContFX)) :
    behavioursFXT (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, firstF, srcBind 0 ⟨0⟩ ⟨1⟩ [] [x] [y]⟩ =
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), firstF, tgtCall 0 firstD ([y] ++ [x])⟩ :=
  bindT_eq (hs' := []) (firstS_func (H := H)) firstD_expand rfl firstF_arity rfl

/-- **The typed source does not return `[x]`** (`x ≠ y`). -/
theorem bindT_first_not_x (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {x y : Val} (hxy : x ≠ y) (K : List (Option ContFX)) :
    Behaviour.returns [x] ∉ behavioursFXT (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, firstF, srcBind 0 ⟨0⟩ ⟨1⟩ [] [x] [y]⟩ := by
  rw [bindT_first]
  intro h
  have := first_returns_only o firstF h
  simp only [List.cons.injEq, and_true] at this
  exact hxy this

end Silmaril.Proofs.Wasm.Models.FXBindT
