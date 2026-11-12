module

public import Silmaril.Wasm.Component.FXRes.EarlyDrop.Defs
public import Silmaril.Wasm.Component.FXRes.Reach.Thms
public import Silmaril.Proofs.Wasm.Component.FXRes.EarlyDrop.Basic

/-!
# Early drops of borrowed handles and the ownership protocol: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.EarlyDrop.Basic`, for every core engine:

* `srun_drop_borrowed`: `resource.drop` of a borrowed handle object (of the dropped resource
  type, not lent, with a borrow scope) succeeds, with no destructor call;
* `lowered_then_dropped`: right after `lower_borrow` gives a callee a borrowed handle at `i`,
  `resource.drop` of `i` succeeds;
* `obProto_rejects_early_drop`: `obProto` rejects `[lend i, free i]`;
* **`early_drop_rejected`**: so the machine runs a handle-table history,
  `[added i e, removed i e]` on a borrowed entry `e`, whose ownership reading `obEvOf (modeOf s)`
  is rejected by `obProto`. **`reached_early_drop_rejected`**: the same from every configuration
  reached by a multi-call run (no `FreeOK` hypothesis), and `cont_early_drop_rejected` for
  the `cont` component over `fxCE P` with the reference host. For `contComp` its hypotheses
  need a borrow lowered into an instance that does not implement the resource type; `contComp`
  has a single instance, the implementer of `cont`, so this restatement may well be vacuous
  there (not proved either way).

**Refuted** (as a statement about all components): "every machine handle history, read as
ownership events, is accepted by `obProto`". `obProto` would need an event for the early end of
one borrow (REF `canon_resource_drop` of an `own = False` handle). For `contComp` itself the
history in question does not arise from its own exports: `cont` is implemented by instance `0`,
the only instance, and `lower_borrow` in the implementing instance makes no handle; proving that
along whole runs needs a contextual invariant that the frame lemmas of
`Silmaril.Wasm.Resource.MachineTab` cannot express (see `docs/projects/wasm-components.md`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.EarlyDrop

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.FXRes.Borrow Silmaril.Wasm.Component.FXRes.Reach
open Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Numerics (Profile)

/-- **At reached configurations**: an early drop of a borrow succeeds and its ownership reading
is rejected by `obProto`. -/
theorem reached_early_drop_rejected {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)]
    {σ σ' : Type} {prof : ProfileKind} {h : Host E σ'} {σ0 : σ'} {X : CIface} {p : RefProg E X}
    {m : Config E σ'} {lim lim' : Limits} {cx : LiftLowerContext E} {rt : RtId} {rep : ℕ}
    {τ : TaskId} (hh : TabHost cx.inst h.impl) (hm : Reached prof h σ0 p m)
    (hsc : cx.scope = .task τ) {s₁ : CStore E} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? m.store rt = some rty → rty.impl ≠ some cx.inst)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) m.store i s₁) :
    ∃ st e, s₁.inst? cx.inst = some st ∧ st.handles.get? i = some e ∧
      ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) = [.lend i, .free i] ∧
      ¬ (obProto ℕ).Accepts ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) ∧
      ∃ s₂, SRun (σ := σ) (resourceDropCore lim' cx.inst rt i) s₁ none s₂ :=
  early_drop_rejected hsc himpl (reached_freeOK hh hm) h₁

/-- **`cont` handles at `fxCE P`**: the same on every multi-call run of `contComp`. -/
theorem cont_early_drop_rejected (P : Profile) {σ : Type} {prof : ProfileKind}
    {m : Config (fxCE P) Unit}
    (hm : Reached prof (Silmaril.Wasm.Component.Param.refHostE (fxCE P)) ()
      (Silmaril.Wasm.Component.FXRes.ContComp.contProg P) m)
    {lim lim' : Limits} {cx : LiftLowerContext (fxCE P)} {rt : RtId} {rep : ℕ} {τ : TaskId}
    (hsc : cx.scope = .task τ) {s₁ : CStore (fxCE P)} {i : ℕ}
    (himpl : ∀ rty, ArenaField.resourceTypes.get? m.store rt = some rty → rty.impl ≠ some cx.inst)
    (h₁ : SRun (σ := σ) (lowerBorrow lim cx rt rep) m.store i s₁) :
    ∃ st e, s₁.inst? cx.inst = some st ∧ st.handles.get? i = some e ∧
      ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) = [.lend i, .free i] ∧
      ¬ (obProto ℕ).Accepts ([Table.Event.added i e, .removed i e].map (obEvOf (modeOf s₁))) ∧
      ∃ s₂, SRun (σ := σ) (resourceDropCore lim' cx.inst rt i) s₁ none s₂ :=
  reached_early_drop_rejected tabHost_none hm hsc himpl h₁

/-- info: 'Silmaril.Wasm.Component.FXRes.EarlyDrop.cont_early_drop_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_early_drop_rejected

end Silmaril.Wasm.Component.FXRes.EarlyDrop
