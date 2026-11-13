module

public import Silmaril.Wasm.Component.FXRes.Reach.Defs
public import Silmaril.Wasm.Component.FXRes.Borrow.Thms
public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Wasm.Component.FXRes.ContComp.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.Reach.Basic

/-!
# Configurations reached by multi-call runs: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.Reach.Basic`, for every core engine and choice
profile, and every host whose programs are table-moving (`Silmaril.Wasm.Resource.TabHost`, e.g.
the reference host `refHostE E`, `tabHost_none`):

* `reached_tabMove`: at every configuration reached by a multi-call run (`Reached`: root
  instantiation, resolved calls, then any run without a host-frame program, e.g. a prefix of a
  call) every instance's handle table is on a successful history from `Table.empty`;
* **`reached_freeOK`**: so it satisfies `FreeOK`.

**`cont_borrow_not_given_reached`** removes the hypothesis `FreeOK` of
`FXRes.Borrow.cont_borrow_not_given`: for the `cont` component over `fxCE P` with the reference
host, if `lower_borrow` gives a callee a borrowed handle at `i`, starting from the store of a
reached configuration, then `lift_own` of `i` has no successful run. The same holds for every
component and engine (`reached_borrow_not_given`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Reach

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.FXRes.Borrow Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Numerics (Profile)

/-- **A borrowed handle cannot be transferred**, at every reached configuration of every
reference program over every engine, with a table-moving host: `borrow_not_given` without
its `FreeOK` hypothesis. -/
theorem reached_borrow_not_given {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ σ' : Type} {prof : ProfileKind}
    {h : Host E σ'} {σ0 : σ'} {X : CIface} {p : RefProg E X} {m : Config E σ'}
    {lim lim' : Limits} {cx cx' : LiftLowerContext E} {rt rt' : RtId} {rep : ℕ} {τ : TaskId}
    (hh : TabHost cx.inst h.impl) (hm : Reached prof h σ0 p m)
    (hsc : cx.scope = .task τ) (hj : cx'.inst = cx.inst) {s₁ s₂ : CStore E} {i r : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? m.store rt = some rty → rty.impl ≠ some cx.inst)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) m.store i s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx' rt' i) s₁ r s₂ :=
  borrow_not_given hsc hj himpl (reached_freeOK hh hm) h₁

/-- **`cont` handles: a borrowed continuation cannot be transferred**, on every multi-call run
of `contComp` over `fxCE P` with the reference host, with no hypothesis on the table. -/
theorem cont_borrow_not_given_reached (P : Profile) {σ : Type} {prof : ProfileKind}
    {m : Config (fxCE P) Unit}
    (hm : Reached prof (Silmaril.Wasm.Component.Param.refHostE (fxCE P)) ()
      (Silmaril.Wasm.Component.FXRes.ContComp.contProg P) m)
    {lim lim' : Limits} {cx cx' : LiftLowerContext (fxCE P)} {rt rt' : RtId} {rep : ℕ}
    {τ : TaskId} (hsc : cx.scope = .task τ) (hj : cx'.inst = cx.inst)
    {s₁ s₂ : CStore (fxCE P)} {i r : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? m.store rt = some rty → rty.impl ≠ some cx.inst)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) m.store i s₁) :
    ¬ SRun (σ := σ) (liftOwn lim' cx' rt' i) s₁ r s₂ :=
  reached_borrow_not_given tabHost_none hm hsc hj himpl h₁

/-- info: 'Silmaril.Wasm.Component.FXRes.Reach.cont_borrow_not_given_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_borrow_not_given_reached

end Silmaril.Wasm.Component.FXRes.Reach
