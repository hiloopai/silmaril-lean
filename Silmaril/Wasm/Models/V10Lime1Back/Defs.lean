module

public import Silmaril.Wasm.Models.V10Lime1.Thms

/-!
# The converse of `v10own → lime1own`: definitions

`V10Lime1.v10Lime1Emb` is `sub`: 1.0 behaviours are Lime1 behaviours of the image. The converse
asks for Lime1 behaviours of the image to be 1.0 behaviours.

* `twoFn`, `cxStore`, `cxHost`, `cxPt`: a 1.0 point whose store holds one Wasm function of type
  `[] → [i32 i32]` (body `i32.const 0; i32.const 0`), with the empty host. 1.0's `invokeWasm`
  asks `ft.results.length ≤ 1`, Lime1's does not, so 1.0 is stuck where Lime1 returns;
* `Store1 s`: every Wasm function of the 1.0 store has at most one result, the 1.0 restriction
  that the domain of `v10own` does not impose on stores;
* `StepBack src`: the **backward lock-step simulation** at a 1.0 host `src`: every Lime1 step
  from the image of a 1.0 configuration with a `Store1` store, under the transported host, is the
  image of a 1.0 step.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10Lime1Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime

/-- `i32.const 0; i32.const 0`, of type `[] → [i32 i32]`. -/
def twoFn : Silmaril.Wasm.V1.Func :=
  { type := ⟨0⟩, locals := [], body := [.intConst .i32 0, .intConst .i32 0] }

/-- The function type with two results. -/
def twoType : Silmaril.Wasm.V1.FuncType := ⟨[], [.i32, .i32]⟩

/-- A 1.0 store with one two-result Wasm function. -/
def cxStore : V10.OStore Unit := { funcs := [.wasm twoType {} twoFn] }

/-- The empty host. -/
def cxHost : V10.OHost Unit := fun _ _ _ _ => False

/-- The counterexample point. -/
def cxPt : V10.Pt Unit := (cxStore, cxHost)

/-- The Wasm functions of a 1.0 store have at most one result. -/
def Store1 {H : Type} (s : V10.OStore H) : Prop :=
  ∀ ft m fn, FuncInst.wasm ft m fn ∈ s.funcs → ft.results.length ≤ 1

/-- **The backward lock-step simulation** at a 1.0 host: a Lime1 step from the image of a 1.0
configuration with a `Store1` store is the image of a 1.0 step. -/
def StepBack {H : Type} (src : V10.OHost H) : Prop :=
  ∀ (a : Silmaril.Wasm.V1.Execution.Config H) (b' : Silmaril.Wasm.Lime1.Execution.Config H),
    Store1 a.store →
    Silmaril.Wasm.Lime1.Execution.Step (src.mapCode Silmaril.Wasm.V1.Func.toLime) a.toLime b' →
      ∃ b, Silmaril.Wasm.V1.Execution.Step src a b ∧ b' = b.toLime

end Silmaril.Wasm.Models.V10Lime1Back
