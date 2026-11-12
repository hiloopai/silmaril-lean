module

public import Silmaril.Raw.Semantics.Behaviour.Machine.Behaviour.Behaviours

/-!
# Composing behaviour sets: sequencing and signature morphisms

* `Observable.bind B K` runs `B` and, on a return `v`, continues with `K v`;
  the traces concatenate. Every other ending (exit, abort, fault, undefined
  behaviour, exhaustion, divergence) propagates. It is the set-level
  counterpart of `Outcome.bind` (`Silmaril/Machine/Behaviour/Compose.lean`).
* `Observable.Refines.bind`: **refinement is a congruence for sequencing**. If
  the first part refines and every continuation refines pointwise, the
  composite refines. This is the vertical, call-site form of compositionality
  that a function-by-function proof needs: replacing a callee by anything that
  refines it keeps the caller correct.
* `Observable.Refines.image_map`: refinement is preserved by every signature
  morphism (`Observable.map`): renaming payloads and mapping each event to a
  list of events (a projection of system calls to output bytes, say).
-/

@[expose] public section

open Silmaril.Machine.Behaviour

namespace Silmaril.Machine.Behaviour

namespace Ending

variable {V V' X T F : Type*}

/-- An ending that is not a return, at another return type. -/
def propagate : Ending V X T F → Option (Ending V' X T F)
  | .returned _ => none
  | .exited x => some (.exited x)
  | .aborted t => some (.aborted t)
  | .faulted f => some (.faulted f)
  | .undefined => some .undefined
  | .exhausted => some .exhausted
  | .diverges => some .diverges

@[simp] theorem propagate_undefined : (undefined : Ending V X T F).propagate =
    some (undefined : Ending V' X T F) := rfl

@[simp] theorem propagate_exhausted : (exhausted : Ending V X T F).propagate =
    some (exhausted : Ending V' X T F) := rfl

theorem propagate_eq_some_exhausted {e : Ending V X T F} :
    e.propagate = some (exhausted : Ending V' X T F) ↔ e = .exhausted := by
  cases e <;> simp [propagate]

theorem propagate_eq_some_undefined {e : Ending V X T F} :
    e.propagate = some (undefined : Ending V' X T F) ↔ e = .undefined := by
  cases e <;> simp [propagate]

/-- An ending is a return or propagates. -/
theorem returned_or_propagate (e : Ending V X T F) :
    (∃ v, e = .returned v) ∨ ∃ e' : Ending V' X T F, e.propagate = some e' := by
  cases e <;> simp [propagate]

end Ending

namespace Observable

variable {E V V' V'' X T F : Type*}

/-- Sequential composition: run `B`, and on a return `v` run `K v`. -/
def bind (B : Set (Observable E V X T F)) (K : V → Set (Observable E V' X T F)) :
    Set (Observable E V' X T F) :=
  {o | ∃ o₁ ∈ B,
    (∃ v, o₁.ending = .returned v ∧ ∃ o₂ ∈ K v, o = ⟨o₁.trace ++ o₂.trace, o₂.ending⟩) ∨
    (∃ e, o₁.ending.propagate = some e ∧ o = ⟨o₁.trace, e⟩)}

variable {B B' : Set (Observable E V X T F)} {K K' : V → Set (Observable E V' X T F)}

theorem mem_bind_returned {o₁ : Observable E V X T F} (h₁ : o₁ ∈ B) {v : V}
    (hv : o₁.ending = .returned v) {o₂ : Observable E V' X T F} (h₂ : o₂ ∈ K v) :
    (⟨o₁.trace ++ o₂.trace, o₂.ending⟩ : Observable E V' X T F) ∈ bind B K :=
  ⟨o₁, h₁, .inl ⟨v, hv, o₂, h₂, rfl⟩⟩

theorem mem_bind_propagate {o₁ : Observable E V X T F} (h₁ : o₁ ∈ B)
    {e : Ending V' X T F} (he : o₁.ending.propagate = some e) :
    (⟨o₁.trace, e⟩ : Observable E V' X T F) ∈ bind B K :=
  ⟨o₁, h₁, .inr ⟨e, he, rfl⟩⟩

theorem bind_mono (hB : B ⊆ B') (hK : ∀ v, K v ⊆ K' v) : bind B K ⊆ bind B' K' := by
  rintro o ⟨o₁, h₁, ⟨v, hv, o₂, h₂, rfl⟩ | ⟨e, he, rfl⟩⟩
  · exact mem_bind_returned (hB h₁) hv (hK v h₂)
  · exact mem_bind_propagate (hB h₁) he

/-- Undefined behaviour of the first part is undefined behaviour of the
composite. -/
theorem undefined_mem_bind {t : List E} (h : (⟨t, .undefined⟩ : Observable E V X T F) ∈ B) :
    (⟨t, .undefined⟩ : Observable E V' X T F) ∈ bind B K :=
  mem_bind_propagate (o₁ := ⟨t, .undefined⟩) h rfl

/-- **Refinement is a congruence for sequential composition.** Under the
exhaustion relaxation the source continuations must have a behaviour
(`htot`): a target that ran out of resources inside the first part must find
a source behaviour extending its trace. -/
theorem Refines.bind {x : Exhaustion} (hB : Refines x B B') (hK : ∀ v, Refines x (K v) (K' v))
    (htot : x = .allowed → ∀ v, (K' v).Nonempty) :
    Refines x (Observable.bind B K) (Observable.bind B' K') := by
  rintro o ⟨o₁, h₁, ⟨v, hv, o₂, h₂, rfl⟩ | ⟨e, he, rfl⟩⟩
  · rcases hB h₁ with h₁' | ⟨t, ht, hu⟩ | ⟨-, he₁, -⟩
    · rcases hK v h₂ with h₂' | ⟨t, ht, hu⟩ | ⟨hx, he₂, o₂', h₂', hp⟩
      · exact .inl (mem_bind_returned h₁' hv h₂')
      · exact .inr (.inl ⟨o₁.trace ++ t, List.prefix_append_right_inj _ |>.2 ht,
          mem_bind_returned (o₂ := ⟨t, .undefined⟩) h₁' hv hu⟩)
      · exact .inr (.inr ⟨hx, he₂, _, mem_bind_returned h₁' hv h₂',
          List.prefix_append_right_inj _ |>.2 hp⟩)
    · exact .inr (.inl ⟨t, ht.trans (List.prefix_append _ _), undefined_mem_bind hu⟩)
    · rw [hv] at he₁; cases he₁
  · rcases hB h₁ with h₁' | ⟨t, ht, hu⟩ | ⟨hx, he₁, o', h', hp⟩
    · exact .inl (mem_bind_propagate h₁' he)
    · exact .inr (.inl ⟨t, ht, undefined_mem_bind hu⟩)
    · rw [he₁] at he
      cases he
      refine .inr (.inr ⟨hx, rfl, ?_⟩)
      rcases o'.ending.returned_or_propagate (V' := V') with ⟨v, hv⟩ | ⟨e', he'⟩
      · obtain ⟨o₂, h₂⟩ := htot hx v
        exact ⟨_, mem_bind_returned h' hv h₂, hp.trans (List.prefix_append _ _)⟩
      · exact ⟨_, mem_bind_propagate h' he', hp⟩

/-! ## Signature morphisms -/

variable {E' V₂ X' T' F' : Type*}

/-- **Refinement is preserved by every signature morphism.** -/
theorem Refines.image_map {x : Exhaustion} {A B : Set (Observable E V X T F)}
    (fe : E → List E') (fv : V → V₂) (fx : X → X') (ft : T → T') (ff : F → F')
    (h : Refines x A B) :
    Refines x (map fe fv fx ft ff '' A) (map fe fv fx ft ff '' B) := by
  rintro _ ⟨o, ho, rfl⟩
  rcases h ho with ho' | ⟨t, ht, hu⟩ | ⟨hx, he, o', ho', hp⟩
  · exact .inl ⟨o, ho', rfl⟩
  · exact .inr (.inl ⟨t.flatMap fe, map_trace_prefix fe ht, ⟨_, hu, rfl⟩⟩)
  · refine .inr (.inr ⟨hx, ?_, _, ⟨o', ho', rfl⟩, map_trace_prefix fe hp⟩)
    simp [map, he, Ending.map]

/-- Safety is preserved by every signature morphism. -/
theorem Safe.image_map {A : Set (Observable E V X T F)} (fe : E → List E') (fv : V → V₂)
    (fx : X → X') (ft : T → T') (ff : F → F') (h : Safe A) :
    Safe (map fe fv fx ft ff '' A) := by
  rintro t ⟨o, ho, he⟩
  have : o.ending = .undefined := by
    have := congrArg Observable.ending he
    simpa [map] using this
  obtain ⟨t', e⟩ := o
  simp only at this
  subst this
  exact h t' ho

end Observable

end Silmaril.Machine.Behaviour
