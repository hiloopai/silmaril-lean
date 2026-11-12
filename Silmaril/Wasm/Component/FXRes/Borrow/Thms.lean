module

public import Silmaril.Wasm.Component.FXRes.Borrow.Defs
public import Silmaril.Wasm.Component.FXRes.ContEngine.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.Borrow.Run

/-!
# The borrow discipline of `cont` handles, from the reference machine's programs: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.Borrow.{Basic,Run}`, for every core engine `E`
(the statements below are for `E`; `cont_*` restate them at the WasmFX engine with a
continuation table `fxCE P`, where the handles are those of the resource type `cont`). Every
result is about successful runs (`SRun`, or `CRunP` for `Task.return_`) of the reference
machine's own programs; none is decided on an event list.

* **`borrow_not_given`** (the `give` of a borrowed handle, which `obProto` rejects): right after
  `lower_borrow` gives a callee a borrowed handle at index `i`, `lift_own` of `i` in that
  instance has no successful run, because the handle object has `own = false`
  (`lowered_borrow_at`). Hypotheses: the callee is not the resource's implementing instance
  (otherwise no handle is made), and the callee's table satisfies `FreeOK` (it does along machine
  runs: `Resource.table_steps_run` from `Table.empty`, `Resource.refMulti_tables_host`).
* **`lent_not_given`**, **`lent_not_dropped`** (the lender's side of `lend`): after
  `lift_borrow` lends the handle at `i` to a callee (`num_lends ≥ 1`, `lent_at`), its owner can
  neither transfer it (`lift_own`) nor drop it (`resource.drop`) in a successful run.
* **`crun_return`** (`endCall`): `Task.return_`, the end of an export call, succeeds only
  when the task holds no borrow (`num_borrows = 0`), whatever the late-bound `on_resolve` call
  answers; so a borrow cannot outlive the call that received it.

What is not shown: an invariant along whole machine runs linking `num_borrows` to the number of
borrowed handles in the table (so that `crun_return` would say "no borrowed handle is left in the
table"), and the acceptance of whole machine histories by `obProto`. Early drops of borrowed
handles, which the Component Model allows (they end the borrow), have no `obProto` event.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Borrow

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Numerics (Profile)

variable {σ : Type}

/-- **`cont` handles at `fxCE P`: a borrowed continuation cannot be transferred.** -/
theorem cont_borrow_not_given (P : Profile) {lim lim' : Limits}
    {cx cx' : LiftLowerContext (fxCE P)} {rt rt' : RtId} {rep : ℕ} {τ : TaskId}
    (hsc : cx.scope = .task τ) (hj : cx'.inst = cx.inst) {s s₁ s₂ : CStore (fxCE P)} {i r : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? s rt = some rty → rty.impl ≠ some cx.inst)
    (hwf : ∀ st, s.inst? cx.inst = some st → FreeOK st.handles)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) s i s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx' rt' i) s₁ r s₂ :=
  borrow_not_given hsc hj himpl hwf h₁

/-- **`cont` handles at `fxCE P`: a lent continuation cannot be transferred or dropped.** -/
theorem cont_lent_kept (P : Profile) {lim lim' : Limits} {cx : LiftLowerContext (fxCE P)}
    {rt rt' : RtId} {i : ℕ} {sb : SubtaskId} (hsc : cx.scope = .subtask sb)
    {s s₁ s₂ : CStore (fxCE P)} {r r' : ℕ} {o : Option (DtorRequest (fxCE P))}
    (h₁ : SRun (σ := σ) (liftBorrow lim cx rt i) s r s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx rt' i) s₁ r' s₂ ∧
      ¬ SRun (σ := σ) (resourceDropCore lim' cx.inst rt' i) s₁ o s₂ :=
  ⟨lent_not_given hsc rfl h₁, lent_not_dropped hsc h₁⟩

/-- **`cont` handles at `fxCE P`: an export call cannot end while it holds borrows.** -/
theorem cont_return (P : Profile) {τ : TaskId} {vs : List Silmaril.Wasm.Component.Value.Val}
    {s s' : CStore (fxCE P)} {u : Unit} (h : CRunP (σ := σ) (Task.return_ τ vs) s u s') :
    ∃ tk, ArenaField.tasks.get? s τ = some tk ∧ tk.numBorrows = 0 :=
  crun_return h

/-- info: 'Silmaril.Wasm.Component.FXRes.Borrow.borrow_not_given' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms borrow_not_given

/-- info: 'Silmaril.Wasm.Component.FXRes.Borrow.crun_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crun_return

end Silmaril.Wasm.Component.FXRes.Borrow
