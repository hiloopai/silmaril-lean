module

public import Silmaril.Proofs.Wasm.Game.Linking.Shared
public import Silmaril.Proofs.Wasm.Game.Linking.Reverse
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Proofs.Wasm.Game.Adequacy.Preservation

/-!
# Linked = shared, divergence observed (M3, step A)

The linked module and the shared world (provider and consumer instantiated separately in one
store) have the same **divergence-observing** strategies, for every profile:
`linked_dstrategy_eq_shared`. Both directions are lock-step divergence-sensitive simulations
(`LTS.DivSimulation` with the empty measure) of their transition systems with silent host-free
steps (`ScalarInstance.dlts`):

* shared to linked: the forward simulation of the linker relation (`internal_simulation`);
* linked to shared: its backward simulation (`internal_reverse`, every profile);

related states: idle states with `Persistent` stores, running states with matching
(`Simulation.Matching .same`) configurations, the shared one typed, its store well formed. An
answer of one side is an answer of the other (`resultAt_matching`, `Control.result_right`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.DivShared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.Linking Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC Silmaril.Wasm.Validation
  Silmaril.Wasm.Link.GC.AdminRelation

variable (S : Setup)

/-- The relation between states of the shared world and of the linked module. -/
inductive SL : S.sharedI.HState → S.linkedI.HState → Prop where
  | idle {s s' : Store Nat} (h : S.Persistent s s') : SL (.idle s) (.idle s')
  | run {f : S.sharedI.F.Op} {s s' : Store Nat} {t t' : Thread} {ts : List CValType}
      (hw : S.sharedI.WellFormed s) (typed : ConfigOk (t.config s) ts)
      (m : Simulation.Matching .same (t.config s) (t'.config s')) :
      SL (.running f s t) (.running f s' t')

variable {S}

/-- The empty measure. -/
def noLt {α : Type} : α → α → Prop := fun _ _ => False

theorem noLt_wf {α : Type} : WellFounded (noLt (α := α)) := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

/-- A closed instance has no import question. -/
theorem closed_op_elim {α : Prop} (e : (ifaceSig []).Op) : α := e.1.elim0

/-- A host-free step keeps the shared instance well formed and its configuration typed. -/
theorem step_typed {s s' : Store Nat} {t t' : Thread} {ts : List CValType} {P : Profile}
    (hw : S.sharedI.WellFormed s) (typed : ConfigOk (t.config s) ts)
    (h : InternalP P (s, t) (s', t')) :
    S.sharedI.WellFormed s' ∧ ConfigOk (t'.config s') ts := by
  have hs : StoreOk s := by
    have h0 := ConfigOk.storeOk typed
    rwa [Thread.config_store] at h0
  obtain ⟨hs', ht', -⟩ := InternalP.preserves hs typed h
  exact ⟨ScalarInstance.WellFormed.of_funcs_eq hw hs' (InternalP.funcs_prefix h), ht'⟩

/-- The stores of matching configurations are related. -/
theorem matching_stores {s s' : Store Nat} {t t' : Thread}
    (m : Simulation.Matching .same (t.config s) (t'.config s')) :
    StoreRelation.Related s s' := by
  have h := m.stores
  rwa [Thread.config_store, Thread.config_store] at h

/-- An export call starts related running states. -/
theorem start_rel {s s' : Store Nat} (hs : S.Persistent s s') (f : S.sharedI.F.Op) :
    SL S (.running f s (S.sharedI.initThread f)) (.running f s' (S.linkedI.initThread f)) := by
  obtain ⟨ts, typed, fi, hfi⟩ := ScalarInstance.invoke_typed hs.2 f
  exact .run hs.2 typed (Simulation.Matching.invoke hs.1 hfi f.2.1)

/-- A shared answer is a linked answer, with persistent stores. -/
theorem answer_rel {s s' : Store Nat} {t t' : Thread} {r : Result}
    (hw : S.sharedI.WellFormed s)
    (m : Simulation.Matching .same (t.config s) (t'.config s')) (final : ResultAt s t r) :
    ResultAt s' t' r ∧ S.Persistent s s' :=
  ⟨resultAt_matching final m, matching_stores m, hw⟩

/-- A linked answer is a shared answer. -/
theorem answer_rel' {s s' : Store Nat} {t t' : Thread} {r : Result}
    (m : Simulation.Matching .same (t.config s) (t'.config s')) (final : ResultAt s' t' r) :
    ResultAt s t r := by
  have hc : Control .same (t.config s).frame.module (t'.config s').frame.module
      (t.config s).code r.toAdmin := by
    have h := m.code
    rw [show (t'.config s').code = r.toAdmin from final] at h
    exact h
  exact Control.result_right hc

/-- Steps of the shared world are matched by single steps of the linked module. -/
theorem fwd_step {P : Profile} {x x' : S.sharedI.HState} {y : S.linkedI.HState}
    {l : Option (Move S.sharedI.E S.sharedI.F)} (hR : SL S x y)
    (h : S.sharedI.DTrans P x l x') :
    ∃ y', S.linkedI.DTrans P y l y' ∧ SL S x' y' := by
  cases h with
  | call s f =>
    cases hR with
    | idle hs => exact ⟨_, ScalarInstance.DTrans.call (I := S.linkedI) _ f, start_rel hs f⟩
  | tau hi =>
    cases hR with
    | @run _ _ s' _ t' _ hw typed m =>
      obtain ⟨y', hi', m'⟩ := internal_simulation (x' := (s', t')) hi typed m
      obtain ⟨hw', typed'⟩ := step_typed hw typed hi
      exact ⟨.running _ y'.1 y'.2, .tau hi', .run hw' typed' m'⟩
  | ucall _ _ => exact closed_op_elim (by assumption)
  | uret _ => cases hR
  | oret final answer =>
    cases hR with
    | run hw typed m =>
      obtain ⟨final', hp⟩ := answer_rel hw m final
      exact ⟨_, .oret final' answer, .idle hp⟩

/-- Steps of the linked module are matched by single steps of the shared world. -/
theorem bwd_step {P : Profile} {x : S.sharedI.HState} {y y' : S.linkedI.HState}
    {l : Option (Move S.linkedI.E S.linkedI.F)} (hR : SL S x y)
    (h : S.linkedI.DTrans P y l y') :
    ∃ x', S.sharedI.DTrans P x l x' ∧ SL S x' y' := by
  cases h with
  | call s f =>
    cases hR with
    | idle hs => exact ⟨_, ScalarInstance.DTrans.call (I := S.sharedI) _ f, start_rel hs f⟩
  | tau hi =>
    cases hR with
    | @run _ s _ t _ _ hw typed m =>
      obtain ⟨x', hx', m'⟩ := internal_reverse (x := (s, t)) typed m hi
      obtain ⟨hw', typed'⟩ := step_typed hw typed hx'
      exact ⟨.running _ x'.1 x'.2, .tau hx', .run hw' typed' m'⟩
  | ucall _ _ => exact closed_op_elim (by assumption)
  | uret _ => cases hR
  | oret final answer =>
    cases hR with
    | run hw typed m =>
      have final' := answer_rel' m final
      exact ⟨_, .oret final' answer, .idle (answer_rel hw m final').2⟩

/-- A single step as a run of the lock-step partner. -/
theorem run_of_step' {E F : Sig.{0}} {L : LTS E F} {y y' : L.State} {l : Option (Move E F)}
    (h : L.step y l y') : L.Run y l.toList y' := LTS.Run.of_step h

/-- **Shared to linked, divergence-sensitive.** -/
def fwdSim (hS : S.Scalar) (P : Profile) :
    LTS.DivSimulation (S.sharedI.dlts P S.sc) (S.linkedI.dlts P S.sl) where
  R := SL S
  init := .idle (S.persistent_initial hS)
  step hR h := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hR h
    exact ⟨y', run_of_step' (L := S.linkedI.dlts P S.sl) hy', hR'⟩
  lt := noLt
  wf := noLt_wf
  tau hR h := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hR h
    exact .inl ⟨y', .single hy', hR'⟩

/-- **Linked to shared, divergence-sensitive.** -/
def bwdSim (hS : S.Scalar) (P : Profile) :
    LTS.DivSimulation (S.linkedI.dlts P S.sl) (S.sharedI.dlts P S.sc) where
  R y x := SL S x y
  init := .idle (S.persistent_initial hS)
  step hR h := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hR h
    exact ⟨x', run_of_step' (L := S.sharedI.dlts P S.sc) hx', hR'⟩
  lt := noLt
  wf := noLt_wf
  tau hR h := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hR h
    exact .inl ⟨x', .single hx', hR'⟩

/-- **(A), divergence observed, every profile.** The linked module and the shared world have
the same divergence-observing strategies: plays, divergences and infinite plays. -/
theorem linked_dstrategy_eq_shared (hS : S.Scalar) (P : Profile) :
    S.linkedI.dstrategy P S.sl = S.sharedI.dstrategy P S.sc :=
  le_antisymm (bwdSim hS P).ofLTS_le (fwdSim hS P).ofLTS_le

end Silmaril.Proofs.Wasm.Game.Linking.DivShared
