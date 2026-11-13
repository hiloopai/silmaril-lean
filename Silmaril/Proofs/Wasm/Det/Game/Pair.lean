module

public import Silmaril.Wasm.Det.Game.Defs

/-!
# Pairing preserves determinism modulo traps

A Proponent move of `σ₁.pair σ₂` is made in the round in progress, so it is a move of one side,
appended to that side's half (`Split.halves_concat`). The halves of a trap-free play are
trap-free (`trap_halves₁`, `trap_halves₂`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- A move of the left side as a move of the pairing. -/
def lift₁ : Move E F₁ → Move E (F₁ ⊕ₛ F₂)
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (Sum.inl q))
  | .inr (.ans q r) => .inr (.ans (Sum.inl q) r)

/-- A move of the right side as a move of the pairing. -/
def lift₂ : Move E F₂ → Move E (F₁ ⊕ₛ F₂)
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (Sum.inr q))
  | .inr (.ans q r) => .inr (.ans (Sum.inr q) r)

theorem ptrap_lift₁ {t₁ : Traps F₁} {t₂ : Traps F₂} {z : Move E F₁} (h : PTrap t₁ z) :
    PTrap (sumTraps t₁ t₂) (lift₁ z : Move E (F₁ ⊕ₛ F₂)) := by
  rcases z with e | (q | ⟨q, r⟩)
  · exact h.elim
  · exact h.elim
  · exact h

theorem ptrap_lift₂ {t₁ : Traps F₁} {t₂ : Traps F₂} {z : Move E F₂} (h : PTrap t₂ z) :
    PTrap (sumTraps t₁ t₂) (lift₂ z : Move E (F₁ ⊕ₛ F₂)) := by
  rcases z with e | (q | ⟨q, r⟩)
  · exact h.elim
  · exact h.elim
  · exact h

/-- A Proponent move of the left round. -/
theorem step_runL {q : F₁.Op} {m : Move E (F₁ ⊕ₛ F₂)} {y : Pos E (F₁ ⊕ₛ F₂)}
    (h : Step (.run (Sum.inl q)) m y) :
    ∃ z : Move E F₁, m = lift₁ z ∧ Split.halves false [m] = ([z], []) ∧ z.IsP := by
  cases h with
  | call _ e => exact ⟨.inl (.ask e), rfl, by simp [Split.halves], trivial⟩
  | ret _ r => exact ⟨.inr (.ans q r), rfl, by simp [Split.halves], trivial⟩

/-- A Proponent move of the right round. -/
theorem step_runR {q : F₂.Op} {m : Move E (F₁ ⊕ₛ F₂)} {y : Pos E (F₁ ⊕ₛ F₂)}
    (h : Step (.run (Sum.inr q)) m y) :
    ∃ z : Move E F₂, m = lift₂ z ∧ Split.halves true [m] = ([], [z]) ∧ z.IsP := by
  cases h with
  | call _ e => exact ⟨.inl (.ask e), rfl, by simp [Split.halves], trivial⟩
  | ret _ r => exact ⟨.inr (.ans q r), rfl, by simp [Split.halves], trivial⟩

/-- Traps in the left half come from traps of the play. -/
theorem trap_halves₁ {t₁ : Traps F₁} {t₂ : Traps F₂} {z : Move E F₁} (ht : PTrap t₁ z) :
    ∀ {p : List (Move E (F₁ ⊕ₛ F₂))} {b : Bool}, z ∈ (Split.halves b p).1 →
      ∃ m ∈ p, PTrap (sumTraps t₁ t₂) m
  | [], _, h => by simp [Split.halves] at h
  | m :: p, b, h => by
    have ih : ∀ b', z ∈ (Split.halves b' p).1 → ∃ m' ∈ m :: p, PTrap (sumTraps t₁ t₂) m' :=
      fun _ h' => let ⟨m', hm', ht'⟩ := trap_halves₁ ht h'; ⟨m', List.mem_cons_of_mem _ hm', ht'⟩
    rcases m with e | (q | ⟨q, r⟩)
    · cases b <;> simp only [Split.halves, List.mem_cons] at h
      · rcases h with rfl | h
        · exact (ht : False).elim
        · exact ih _ h
      · exact ih _ h
    · rcases q with q | q <;> simp only [Split.halves, List.mem_cons] at h
      · rcases h with rfl | h
        · exact (ht : False).elim
        · exact ih _ h
      · exact ih _ h
    · rcases q with q | q <;> simp only [Split.halves, List.mem_cons] at h
      · rcases h with rfl | h
        · exact ⟨_, List.mem_cons_self .., ht⟩
        · exact ih _ h
      · exact ih _ h

/-- Traps in the right half come from traps of the play. -/
theorem trap_halves₂ {t₁ : Traps F₁} {t₂ : Traps F₂} {z : Move E F₂} (ht : PTrap t₂ z) :
    ∀ {p : List (Move E (F₁ ⊕ₛ F₂))} {b : Bool}, z ∈ (Split.halves b p).2 →
      ∃ m ∈ p, PTrap (sumTraps t₁ t₂) m
  | [], _, h => by simp [Split.halves] at h
  | m :: p, b, h => by
    have ih : ∀ b', z ∈ (Split.halves b' p).2 → ∃ m' ∈ m :: p, PTrap (sumTraps t₁ t₂) m' :=
      fun _ h' => let ⟨m', hm', ht'⟩ := trap_halves₂ ht h'; ⟨m', List.mem_cons_of_mem _ hm', ht'⟩
    rcases m with e | (q | ⟨q, r⟩)
    · cases b <;> simp only [Split.halves, List.mem_cons] at h
      · exact ih _ h
      · rcases h with rfl | h
        · exact (ht : False).elim
        · exact ih _ h
    · rcases q with q | q <;> simp only [Split.halves, List.mem_cons] at h
      · exact ih _ h
      · rcases h with rfl | h
        · exact (ht : False).elim
        · exact ih _ h
    · rcases q with q | q <;> simp only [Split.halves, List.mem_cons] at h
      · exact ih _ h
      · rcases h with rfl | h
        · exact ⟨_, List.mem_cons_self .., ht⟩
        · exact ih _ h

/-- Two Proponent moves of the left round. -/
theorem pair_side₁ {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁} (h₁ : DetMod t₁ σ₁)
    {p : List (Move E (F₁ ⊕ₛ F₂))} {q : F₁.Op} {m₁ m₂ : Move E (F₁ ⊕ₛ F₂)}
    {y₁ y₂ : Pos E (F₁ ⊕ₛ F₂)} (hx₁ : Step (.run (Sum.inl q)) m₁ y₁)
    (hx₂ : Step (.run (Sum.inl q)) m₂ y₂)
    (ha₁ : (Split.halves false p).1 ++ (Split.halves false [m₁]).1 ∈ σ₁)
    (ha₂ : (Split.halves false p).1 ++ (Split.halves false [m₂]).1 ∈ σ₁)
    (hfree : TrapFree (sumTraps t₁ t₂) p) :
    m₁ = m₂ ∨ PTrap (sumTraps t₁ t₂) m₁ ∨ PTrap (sumTraps t₁ t₂) m₂ := by
  obtain ⟨z₁, rfl, hz₁, hzP₁⟩ := step_runL (F₂ := F₂) hx₁
  obtain ⟨z₂, rfl, hz₂, hzP₂⟩ := step_runL (F₂ := F₂) hx₂
  have hf : TrapFree t₁ (Split.halves false p).1 := fun z hz ht =>
    let ⟨m, hm, ht'⟩ := trap_halves₁ (t₂ := t₂) ht hz
    hfree m hm ht'
  have hb₁ : (Split.halves false p).1 ++ [z₁] ∈ σ₁ := by simpa [hz₁] using ha₁
  have hb₂ : (Split.halves false p).1 ++ [z₂] ∈ σ₁ := by simpa [hz₂] using ha₂
  rcases h₁ _ z₁ z₂ hb₁ hb₂ hzP₁ hzP₂ hf with h | h | h
  · exact .inl (congrArg lift₁ h)
  · exact .inr (.inl (ptrap_lift₁ h))
  · exact .inr (.inr (ptrap_lift₁ h))

/-- Two Proponent moves of the right round. -/
theorem pair_side₂ {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₂ : Strategy E F₂} (h₂ : DetMod t₂ σ₂)
    {p : List (Move E (F₁ ⊕ₛ F₂))} {q : F₂.Op} {m₁ m₂ : Move E (F₁ ⊕ₛ F₂)}
    {y₁ y₂ : Pos E (F₁ ⊕ₛ F₂)} (hx₁ : Step (.run (Sum.inr q)) m₁ y₁)
    (hx₂ : Step (.run (Sum.inr q)) m₂ y₂)
    (ha₁ : (Split.halves false p).2 ++ (Split.halves true [m₁]).2 ∈ σ₂)
    (ha₂ : (Split.halves false p).2 ++ (Split.halves true [m₂]).2 ∈ σ₂)
    (hfree : TrapFree (sumTraps t₁ t₂) p) :
    m₁ = m₂ ∨ PTrap (sumTraps t₁ t₂) m₁ ∨ PTrap (sumTraps t₁ t₂) m₂ := by
  obtain ⟨z₁, rfl, hz₁, hzP₁⟩ := step_runR (F₁ := F₁) hx₁
  obtain ⟨z₂, rfl, hz₂, hzP₂⟩ := step_runR (F₁ := F₁) hx₂
  have hf : TrapFree t₂ (Split.halves false p).2 := fun z hz ht =>
    let ⟨m, hm, ht'⟩ := trap_halves₂ (t₁ := t₁) ht hz
    hfree m hm ht'
  have hb₁ : (Split.halves false p).2 ++ [z₁] ∈ σ₂ := by simpa [hz₁] using ha₁
  have hb₂ : (Split.halves false p).2 ++ [z₂] ∈ σ₂ := by simpa [hz₂] using ha₂
  rcases h₂ _ z₁ z₂ hb₁ hb₂ hzP₁ hzP₂ hf with h | h | h
  · exact .inl (congrArg lift₂ h)
  · exact .inr (.inl (ptrap_lift₂ h))
  · exact .inr (.inr (ptrap_lift₂ h))

/-- **Pairing preserves determinism modulo traps.** -/
theorem detMod_pair {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁}
    {σ₂ : Strategy E F₂} (h₁ : DetMod t₁ σ₁) (h₂ : DetMod t₂ σ₂) :
    DetMod (sumTraps t₁ t₂) (σ₁.pair σ₂) := by
  intro p m₁ m₂ ⟨⟨_, hp₁⟩, ha₁, hb₁⟩ ⟨⟨_, hp₂⟩, ha₂, hb₂⟩ hP₁ hP₂ hfree
  obtain ⟨x, hx, hxm₁⟩ := Path.concat_iff.1 hp₁
  obtain ⟨x', hx', hxm₂⟩ := Path.concat_iff.1 hp₂
  have hxx : x' = x := Path.det hx' hx
  obtain ⟨y₁, y₂, -, -, hr⟩ := Split.halves_path hx (Split.Rel.idle false)
  have ha₁' : (Split.halves false p).1 ++ (Split.halves (Split.side false p) [m₁]).1 ∈ σ₁ :=
    (Split.halves_concat false p m₁).1 ▸ ha₁
  have hb₁' : (Split.halves false p).2 ++ (Split.halves (Split.side false p) [m₁]).2 ∈ σ₂ :=
    (Split.halves_concat false p m₁).2 ▸ hb₁
  have ha₂' : (Split.halves false p).1 ++ (Split.halves (Split.side false p) [m₂]).1 ∈ σ₁ :=
    (Split.halves_concat false p m₂).1 ▸ ha₂
  have hb₂' : (Split.halves false p).2 ++ (Split.halves (Split.side false p) [m₂]).2 ∈ σ₂ :=
    (Split.halves_concat false p m₂).2 ▸ hb₂
  generalize Split.side false p = b at hr ha₁' hb₁' ha₂' hb₂'
  cases hr with
  | idle =>
    cases hxm₁
    exact absurd hP₁ id
  | waitL =>
    cases hxm₁
    exact absurd hP₁ id
  | waitR =>
    cases hxm₁
    exact absurd hP₁ id
  | runL q => exact pair_side₁ h₁ hxm₁ (hxx ▸ hxm₂) ha₁' ha₂' hfree
  | runR q => exact pair_side₂ h₂ hxm₁ (hxx ▸ hxm₂) hb₁' hb₂' hfree

end Silmaril.Proofs.Wasm.Det.Game
