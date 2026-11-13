module

public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Resource protocols for components: the protocol presentation of `noUseAfterDrop`

`nudProto_accepts_iff`: a trace is accepted by `nudProto d` iff every position satisfies the
position predicate of `noUseAfterDrop d`; hence `models_noUseAfterDrop_iff`: the two sentences
have the same models in every semantics. The state reached after a history is the list of
representations dropped in it (`nud_run_mem`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component

theorem mem_ownedReps {vs : List RVal} {r : ℕ} : r ∈ ownedReps vs ↔ (true, r) ∈ valsHandles vs := by
  simp only [ownedReps, List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, r'⟩, hp, h⟩
    cases b <;> simp_all
  · intro h
    exact ⟨(true, r), h, rfl⟩

/-- Position predicates hold everywhere on a longer word iff on the shorter one and at the new
position. -/
theorem everyPos_concat {α : Type} {P : List α → α → Prop} {t : List α} {e : α} :
    EveryPos P (t ++ [e]) ↔ EveryPos P t ∧ P t e := by
  constructor
  · intro h
    exact ⟨h.of_prefix (List.prefix_append t [e]), h t e [] rfl⟩
  · rintro ⟨ht, he⟩ h' e' r hr
    rcases List.eq_nil_or_concat r with rfl | ⟨r', x, rfl⟩
    · obtain ⟨rfl, h2⟩ := List.append_inj' hr rfl
      cases h2
      exact he
    · have : t ++ [e] = (h' ++ e' :: r') ++ [x] := by rw [hr]; simp
      obtain ⟨rfl, -⟩ := List.append_inj' this rfl
      exact ht h' e' r' rfl

variable {X : CIface} (d : X.Exp)

/-- When a step of `nudProto d` is rejected. -/
theorem nudStep_eq_none_iff (D : List ℕ) (e : CEvent X) :
    nudStep d D e = none ↔ ∃ j a, e = Event.call j a ∧ ∃ r ∈ valsReps a, r ∈ D := by
  rcases e with (_ | _) | (⟨j, a⟩ | ⟨j, b⟩) <;> simp [nudStep, List.any_eq_true]

/-- What a step of `nudProto d` adds: the owned representations of a call of `d`. -/
theorem nudStep_mem {D D' : List ℕ} {e : CEvent X} (h : nudStep d D e = some D') (r : ℕ) :
    r ∈ D' ↔ r ∈ D ∨ ∃ a₀, e = Event.call d a₀ ∧ (true, r) ∈ valsHandles a₀ := by
  rcases e with (_ | _) | (⟨j, a⟩ | ⟨j, b⟩)
  · simp_all [nudStep]
  · simp_all [nudStep]
  · by_cases hj : j = d
    · subst hj
      by_cases hany : ((valsReps a).any fun x => decide (x ∈ D)) = true
      · simp [nudStep, hany] at h
      · simp only [nudStep, hany, ite_true, Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        simp [mem_ownedReps, or_comm]
    · have hj' : d ≠ j := fun h => hj h.symm
      by_cases hany : ((valsReps a).any fun x => decide (x ∈ D)) = true
      · simp [nudStep, hany] at h
      · simp_all [nudStep]
  · simp_all [nudStep]

/-- The state of `nudProto d` after a history: the representations dropped in it. -/
theorem nud_run_mem {t : List (CEvent X)} {D : List ℕ} (h : (nudProto d).run [] t = some D) :
    ∀ r, r ∈ D ↔ ∃ a₀, Event.call d a₀ ∈ t ∧ (true, r) ∈ valsHandles a₀ := by
  induction t using List.reverseRecOn generalizing D with
  | nil => simp_all [Protocol.run]
  | append_singleton t e ih =>
    have hb : ((nudProto d).run [] t).bind (fun q => (nudProto d).step q e) = some D := by
      rw [← Protocol.run_concat]; exact h
    obtain ⟨D₀, hD₀, hstep⟩ := Option.bind_eq_some_iff.1 hb
    intro r
    rw [nudStep_mem d hstep r, ih hD₀ r]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (⟨a₀, ha, hr⟩ | ⟨a₀, rfl, hr⟩)
      · exact ⟨a₀, .inl ha, hr⟩
      · exact ⟨a₀, .inr rfl, hr⟩
    · rintro ⟨a₀, ha | ha, hr⟩
      · exact .inl ⟨a₀, ha, hr⟩
      · exact .inr ⟨a₀, ha.symm, hr⟩

/-- One more event: `nudProto d` accepts it iff the position predicate holds there. -/
theorem nud_step_iff {t : List (CEvent X)} {D : List ℕ} (hD : (nudProto d).run [] t = some D)
    (e : CEvent X) : (∃ D', nudStep d D e = some D') ↔ NoUseAfterDrop.pos d t e := by
  have hnone : ¬ (nudStep d D e = none) ↔ NoUseAfterDrop.pos d t e := by
    rw [nudStep_eq_none_iff]
    constructor
    · rintro hn j a rfl a₀ ha₀ r hr hra
      exact hn ⟨j, a, rfl, r, hra, (nud_run_mem d hD r).2 ⟨a₀, ha₀, hr⟩⟩
    · rintro hp ⟨j, a, rfl, r, hra, hrD⟩
      obtain ⟨a₀, ha₀, hr⟩ := (nud_run_mem d hD r).1 hrD
      exact hp j a rfl a₀ ha₀ r hr hra
  rw [← hnone, ← Option.ne_none_iff_exists']

/-- **`nudProto d` presents `noUseAfterDrop d`.** -/
theorem nudProto_accepts_iff (t : List (CEvent X)) :
    (nudProto d).Accepts t ↔ EveryPos (NoUseAfterDrop.pos d) t := by
  induction t using List.reverseRecOn with
  | nil => exact ⟨fun _ _ _ _ h => by simp at h, fun _ => rfl⟩
  | append_singleton t e ih =>
    rw [Protocol.accepts_concat_iff, everyPos_concat, ← ih, Protocol.accepts_iff_exists]
    constructor
    · rintro ⟨D, hD, hstep⟩
      exact ⟨⟨D, hD⟩, (nud_step_iff d hD e).1 hstep⟩
    · rintro ⟨⟨D, hD⟩, hpos⟩
      exact ⟨D, hD, (nud_step_iff d hD e).2 hpos⟩

/-- **`noUseAfterDrop d` and `nudProto d` have the same models**, in every semantics. -/
theorem models_noUseAfterDrop_iff (Sem : Semantics CFn (List RVal) Outcome) (p : Sem.Prog X) :
    Models noUseAfterDrop Sem p d ↔ Models (protoLogic CFn (List RVal) Outcome (List ℕ)) Sem p
      (nudProto d) := by
  rw [models_iff, models_protoLogic_iff]
  exact forall₂_congr fun t _ => (nudProto_accepts_iff d t).symm

end Silmaril.Wasm.Resource
