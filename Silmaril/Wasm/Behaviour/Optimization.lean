module

public import Silmaril.Wasm.Behaviour.Basic
public import Silmaril.Wasm.Behaviour.OptimizationMode

@[expose] public section

/-! # Optimization policies with explicit feasibility

Relations are written source first. Refinement selects source observations and
preserves the existence of an observation when the source has one. Divergence
is an observation, so an empty set is not an implementation of divergence.

The liberal policy also permits inserting a trap. It never treats a source trap
as undefined behavior: at one call, a source whose only observation is a trap
must still have exactly that observation. A nondeterministic trap can be discarded when
another permitted observation remains. The separate feasibility field is what
excludes replacing a guaranteed trap by an empty behavior set.

`TrapOrder` also supports sessions. After a matching prefix of returns, a target
trap licenses the rest of that target trace, including an embedder's subsequent
calls after catching the trap. A source trap supplies no such license.
-/

namespace Silmaril.Wasm.Optimization

universe u

/-- A distinguished trap and a preorder of observations permitted by insertion.
Immediate traps form a class: in a session, an immediate trap may be followed
by later calls from an embedder that catches it. The relation preserves that
class when it occurs on the source side. -/
structure TrapOrder (O : Type u) where
  trap : O
  ImmediateTrap : O → Prop
  trap_immediate : ImmediateTrap trap
  Rel : O → O → Prop
  refl : ∀ o, Rel o o
  trans : ∀ {a b c}, Rel a b → Rel b c → Rel a c
  insert : ∀ o, Rel trap o
  preserve : ∀ {target source}, Rel target source → ImmediateTrap source → ImmediateTrap target

variable {O : Type u}

/-- Preserve the possibility of observing an outcome. This does not assert
termination: an observation may be divergence. -/
def Feasible (source target : Set O) : Prop := source.Nonempty → target.Nonempty

/-- Every target observation is a source observation, with feasibility retained. -/
def Refines (source target : Set O) : Prop := target ⊆ source ∧ Feasible source target

/-- A target observation is a trap or is matched by the insertion preorder.
The explicit trap alternative also permits trapping when the source set is empty. -/
def InsertsTraps (order : TrapOrder O) (source target : Set O) : Prop :=
  (∀ o ∈ target, order.ImmediateTrap o ∨ ∃ original ∈ source, order.Rel o original) ∧
    Feasible source target

def Correct (order : TrapOrder O) : Mode → Set O → Set O → Prop
  | .equivalence, source, target => source = target
  | .refinement, source, target => Refines source target
  | .trapInsertion, source, target => InsertsTraps order source target

theorem feasible_refl (source : Set O) : Feasible source source := id

theorem feasible_trans {a b c : Set O} (hab : Feasible a b) (hbc : Feasible b c) :
    Feasible a c := fun ha => hbc (hab ha)

theorem refines_refl (source : Set O) : Refines source source := ⟨fun _ h => h, id⟩

theorem refines_trans {a b c : Set O} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c := ⟨fun _ h => hab.1 (hbc.1 h), feasible_trans hab.2 hbc.2⟩

theorem insertsTraps_refl (order : TrapOrder O) (source : Set O) :
    InsertsTraps order source source :=
  ⟨fun o ho => .inr ⟨o, ho, order.refl o⟩, id⟩

theorem insertsTraps_trans (order : TrapOrder O) {a b c : Set O}
    (hab : InsertsTraps order a b) (hbc : InsertsTraps order b c) :
    InsertsTraps order a c := by
  refine ⟨?_, feasible_trans hab.2 hbc.2⟩
  intro o ho
  rcases hbc.1 o ho with trap | ⟨middle, hm, rel⟩
  · exact .inl trap
  · rcases hab.1 middle hm with trap | ⟨original, hs, rel'⟩
    · exact .inl (order.preserve rel trap)
    · exact .inr ⟨original, hs, order.trans rel rel'⟩

theorem correct_refl (order : TrapOrder O) (mode : Mode) (source : Set O) :
    Correct order mode source source := by
  cases mode
  · rfl
  · exact refines_refl source
  · exact insertsTraps_refl order source

theorem correct_trans (order : TrapOrder O) (mode : Mode) {a b c : Set O}
    (hab : Correct order mode a b) (hbc : Correct order mode b c) :
    Correct order mode a c := by
  cases mode
  · exact hab.trans hbc
  · exact refines_trans hab hbc
  · exact insertsTraps_trans order hab hbc

theorem equivalence_refines {source target : Set O} (h : source = target) :
    Refines source target := h ▸ refines_refl source

theorem refinement_insertsTraps (order : TrapOrder O) {source target : Set O}
    (h : Refines source target) : InsertsTraps order source target :=
  ⟨fun o ho => .inr ⟨o, h.1 ho, order.refl o⟩, h.2⟩

/-- Trapping immediately is permitted for every source observation set. -/
theorem always_trap (order : TrapOrder O) (source : Set O) :
    InsertsTraps order source {order.trap} :=
  ⟨fun _ ho => .inl ((Set.mem_singleton_iff.mp ho).symm ▸ order.trap_immediate),
    fun _ => ⟨_, rfl⟩⟩

/-- A guaranteed immediate trap remains an immediate trap, including existence.
The single-behavior specialization below identifies its exact singleton set. -/
theorem deterministic_trap (order : TrapOrder O) {target : Set O}
    (h : InsertsTraps order {order.trap} target) :
    target.Nonempty ∧ ∀ o ∈ target, order.ImmediateTrap o := by
  refine ⟨h.2 ⟨order.trap, rfl⟩, ?_⟩
  intro o ho
  rcases h.1 o ho with trap | ⟨original, hs, rel⟩
  · exact trap
  · exact order.preserve rel ((Set.mem_singleton_iff.mp hs).symm ▸ order.trap_immediate)

/-- This is the hole in subset-only refinement: it accepts the empty target
even when the source is a guaranteed trap. Feasibility rejects that target. -/
theorem empty_target_counterexample (order : TrapOrder O) :
    (∅ : Set O) ⊆ {order.trap} ∧ ¬ Refines ({order.trap} : Set O) ∅ := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro h
  obtain ⟨o, ho⟩ := h.2 ⟨order.trap, rfl⟩
  exact ho

/-- Discarding a nondeterministic trap is legal when another outcome remains. -/
theorem remove_nondeterministic_trap (order : TrapOrder O) (outcome : O) :
    Refines ({order.trap, outcome} : Set O) {outcome} := by
  refine ⟨?_, fun _ => ⟨outcome, rfl⟩⟩
  intro o ho
  exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp ho))

/-- At a single call, insertion permits a trap or exactly the source outcome. -/
def behaviourOrder (V : Type u) : TrapOrder (Behaviour V) where
  trap := .traps
  ImmediateTrap b := b = .traps
  trap_immediate := rfl
  Rel target source := target = .traps ∨ target = source
  refl _ := .inr rfl
  trans hab hbc := by
    rcases hab with h | h
    · exact .inl h
    · subst h
      exact hbc
  insert _ := .inl rfl
  preserve h trapped := h.elim id (fun same => same.trans trapped)

/-- At one call, a guaranteed source trap has exactly the same target outcome. -/
theorem deterministic_behaviour_trap {V : Type u} {target : Set (Behaviour V)}
    (h : InsertsTraps (behaviourOrder V) {.traps} target) : target = {.traps} := by
  obtain ⟨nonempty, only⟩ := deterministic_trap (behaviourOrder V) h
  apply Set.Subset.antisymm
  · exact fun o ho => Set.mem_singleton_iff.mpr (only o ho)
  · intro o ho
    obtain ⟨w, hw⟩ := nonempty
    rw [Set.mem_singleton_iff.mp ho, ← only w hw]
    exact hw

/-- A session may agree exactly or match returns until the target traps. After
that target trap the remaining trace is unconstrained, accommodating recovery
and subsequent embedder calls. A source trap never grants this license. Raw
list validity is supplied by the actual semantics, not this relation. -/
inductive TrapPrefix {V : Type u} : List (Behaviour V) → List (Behaviour V) → Prop where
  | refl (trace : List (Behaviour V)) : TrapPrefix trace trace
  | trap (source : List (Behaviour V)) {tail : List (Behaviour V)} : TrapPrefix (.traps :: tail) source
  | returns (vs : List V) {target source : List (Behaviour V)} :
      TrapPrefix target source → TrapPrefix (.returns vs :: target) (.returns vs :: source)

namespace TrapPrefix

variable {V : Type u}

theorem trans {a b c : List (Behaviour V)} (hab : TrapPrefix a b) (hbc : TrapPrefix b c) :
    TrapPrefix a c := by
  induction hab generalizing c with
  | refl => exact hbc
  | trap => exact .trap c
  | returns vs _ ih =>
      cases hbc with
      | refl => exact .returns vs (ih (.refl _))
      | returns _ h => exact .returns vs (ih h)

theorem from_trap {target : List (Behaviour V)} (h : TrapPrefix target [.traps]) :
    ∃ tail, target = .traps :: tail := by
  cases h <;> exact ⟨_, rfl⟩

theorem preserve_immediate {target source : List (Behaviour V)} (h : TrapPrefix target source)
    (trapped : ∃ tail, source = .traps :: tail) : ∃ tail, target = .traps :: tail := by
  cases h with
  | refl => exact trapped
  | trap => exact ⟨_, rfl⟩
  | returns => obtain ⟨_, bad⟩ := trapped; cases bad

/-- A source trap cannot disappear along a matching returned prefix. An
inserted earlier trap is permitted and also satisfies this property. -/
theorem mem_traps {target source : List (Behaviour V)} (h : TrapPrefix target source)
    (traps : Behaviour.traps ∈ source) : Behaviour.traps ∈ target := by
  induction h with
  | refl => exact traps
  | trap => exact List.mem_cons_self
  | returns vs _ ih =>
      exact List.mem_cons_of_mem _ (ih (by simpa using traps))

end TrapPrefix

/-- The same policy applied to export sessions, with a license after a target trap. -/
def sessionOrder (V : Type u) : TrapOrder (List (Behaviour V)) where
  trap := [.traps]
  ImmediateTrap trace := ∃ tail, trace = .traps :: tail
  trap_immediate := ⟨[], rfl⟩
  Rel := TrapPrefix
  refl := TrapPrefix.refl
  trans := TrapPrefix.trans
  insert source := TrapPrefix.trap source
  preserve := TrapPrefix.preserve_immediate

/-- Insertion can shorten an interacting session after a returned prefix. -/
theorem session_trap_prefix {V : Type u} (values : List V) (suffix : List (Behaviour V)) :
    TrapPrefix [.returns values, .traps] (.returns values :: suffix) :=
  .returns values (.trap suffix)

/-- Must-trap sessions retain a trap even when it occurs after earlier calls.
Feasibility separately retains observation existence when the source has one. -/
theorem session_must_trap {V : Type u} {source target : Set (List (Behaviour V))}
    (h : InsertsTraps (sessionOrder V) source target)
    (must : ∀ trace ∈ source, Behaviour.traps ∈ trace) :
    ∀ trace ∈ target, Behaviour.traps ∈ trace := by
  intro trace ht
  rcases h.1 trace ht with ⟨tail, trap⟩ | ⟨original, hs, rel⟩
  · rw [trap]
    exact List.mem_cons_self
  · exact rel.mem_traps (must original hs)

/-- A caught target trap may be followed by more embedder calls, while returned
observations before that trap still match the source. -/
theorem recovered_target_trap :
    TrapPrefix ([.returns [], .traps, .returns [99]] : List (Behaviour Nat))
      [.returns [], .returns [7], .returns [8]] :=
  .returns [] (.trap _)

/-- The trap license cannot justify an incorrect value produced before it. -/
theorem wrong_return_before_trap :
    ¬ TrapPrefix ([.returns [8], .traps] : List (Behaviour Nat)) [.returns [7]] := by
  intro h
  cases h

end Silmaril.Wasm.Optimization
