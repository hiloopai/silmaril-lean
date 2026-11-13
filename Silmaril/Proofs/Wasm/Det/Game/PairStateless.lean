module

public import Silmaril.Proofs.Wasm.Det.Game.Pair

/-!
# Pairing preserves statelessness modulo traps

After a history of `σ₁.pair σ₂` that ends idle, the halves of the rest of the play do not
depend on the side bit (`halves_idle`, the next move asks a question, which fixes the side), so
the halves of `h ++ c` are the halves of `h` followed by the halves of `c` (`halves_after_idle`).
The halves of an idle history are idle histories of the parts, and statelessness of each part
compares the two continuations on the side of the round in progress.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- The halves of a concatenation. -/
theorem halves_append (b : Bool) (p q : List (Move E (F₁ ⊕ₛ F₂))) :
    (Split.halves b (p ++ q)).1 = (Split.halves b p).1 ++ (Split.halves (Split.side b p) q).1 ∧
    (Split.halves b (p ++ q)).2 = (Split.halves b p).2 ++ (Split.halves (Split.side b p) q).2 := by
  induction p generalizing b with
  | nil => simp [Split.halves, Split.side]
  | cons x p ih =>
    rcases x with e | (q | ⟨q, r⟩)
    · cases b <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]
    · rcases q with q | q <;> simp [Split.halves, Split.side, ih]

/-- From idle, the halves do not depend on the side bit. -/
theorem halves_idle {c : List (Move E (F₁ ⊕ₛ F₂))} {y : Pos E (F₁ ⊕ₛ F₂)}
    (h : Path .idle c y) (b : Bool) : Split.halves b c = Split.halves false c := by
  cases h with
  | nil => rfl
  | cons hs _ =>
    cases hs with
    | ask q => rcases q with q | q <;> rfl

/-- After an idle history, the halves split along the concatenation. -/
theorem halves_after_idle {h c : List (Move E (F₁ ⊕ₛ F₂))} {y : Pos E (F₁ ⊕ₛ F₂)}
    (hc : Path .idle c y) :
    (Split.halves false (h ++ c)).1 = (Split.halves false h).1 ++ (Split.halves false c).1 ∧
    (Split.halves false (h ++ c)).2 = (Split.halves false h).2 ++ (Split.halves false c).2 := by
  rw [(halves_append false h c).1, (halves_append false h c).2, halves_idle hc]
  exact ⟨rfl, rfl⟩

/-- The halves of an idle history are idle histories. -/
theorem halves_idle_idle {h : List (Move E (F₁ ⊕ₛ F₂))} (hi : Path .idle h .idle) :
    Path .idle (Split.halves false h).1 .idle ∧ Path .idle (Split.halves false h).2 .idle := by
  obtain ⟨y₁, y₂, h₁, h₂, hr⟩ := Split.halves_path hi (Split.Rel.idle false)
  cases hr
  exact ⟨h₁, h₂⟩

/-- A trap-free play has trap-free halves. -/
theorem trapFree_halves {t₁ : Traps F₁} {t₂ : Traps F₂} {c : List (Move E (F₁ ⊕ₛ F₂))}
    (hfree : TrapFree (sumTraps t₁ t₂) c) :
    TrapFree t₁ (Split.halves false c).1 ∧ TrapFree t₂ (Split.halves false c).2 :=
  ⟨fun _ hz ht => let ⟨m, hm, ht'⟩ := trap_halves₁ (t₂ := t₂) ht hz; hfree m hm ht',
    fun _ hz ht => let ⟨m, hm, ht'⟩ := trap_halves₂ (t₁ := t₁) ht hz; hfree m hm ht'⟩

/-- The halves of a continuation after an idle history, with the position it reaches. -/
theorem pair_after {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} {h c : List (Move E (F₁ ⊕ₛ F₂))}
    {m : Move E (F₁ ⊕ₛ F₂)} (hi : Path .idle h .idle) (hm : h ++ c ++ [m] ∈ σ₁.pair σ₂) :
    ∃ x y, Path .idle c x ∧ Step x m y ∧
      (Split.halves false h).1 ++ (Split.halves false c).1 ++
        (Split.halves (Split.side false c) [m]).1 ∈ σ₁ ∧
      (Split.halves false h).2 ++ (Split.halves false c).2 ++
        (Split.halves (Split.side false c) [m]).2 ∈ σ₂ := by
  obtain ⟨⟨z, hp⟩, ha, hb⟩ := hm
  obtain ⟨x, hx, hxm⟩ := Path.concat_iff.1 hp
  obtain ⟨w, hw, hwc⟩ := Path.of_append hx
  cases Path.det hw hi
  have hcm : Path .idle (c ++ [m]) z := hwc.append (.single hxm)
  have e₁ := halves_after_idle (h := h) hcm
  rw [List.append_assoc] at ha hb
  rw [e₁.1, (Split.halves_concat false c m).1] at ha
  rw [e₁.2, (Split.halves_concat false c m).2] at hb
  exact ⟨x, z, hwc, hxm, by simpa using ha, by simpa using hb⟩

/-- Two Proponent moves of a left round after idle histories. -/
theorem stateless_runL {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁}
    (h₁ : StatelessMod t₁ σ₁) {A₁ A₂ C : List (Move E F₁)} (hA₁ : A₁ ∈ σ₁) (hA₂ : A₂ ∈ σ₁)
    (hi₁ : Path .idle A₁ .idle) (hi₂ : Path .idle A₂ .idle) (hC : TrapFree t₁ C) {q : F₁.Op}
    {m₁ m₂ : Move E (F₁ ⊕ₛ F₂)} {y₁ y₂ : Pos E (F₁ ⊕ₛ F₂)} (hx₁ : Step (.run (Sum.inl q)) m₁ y₁)
    (hx₂ : Step (.run (Sum.inl q)) m₂ y₂) (ha₁ : A₁ ++ C ++ (Split.halves false [m₁]).1 ∈ σ₁)
    (ha₂ : A₂ ++ C ++ (Split.halves false [m₂]).1 ∈ σ₁) :
    m₁ = m₂ ∨ PTrap (sumTraps t₁ t₂) m₁ ∨ PTrap (sumTraps t₁ t₂) m₂ := by
  obtain ⟨z₁, rfl, hz₁, hzP₁⟩ := step_runL (F₂ := F₂) hx₁
  obtain ⟨z₂, rfl, hz₂, hzP₂⟩ := step_runL (F₂ := F₂) hx₂
  rw [hz₁] at ha₁
  rw [hz₂] at ha₂
  rcases h₁ _ _ hA₁ hA₂ hi₁ hi₂ C z₁ z₂ ha₁ ha₂ hzP₁ hzP₂ hC with h | h | h
  · exact .inl (congrArg lift₁ h)
  · exact .inr (.inl (ptrap_lift₁ h))
  · exact .inr (.inr (ptrap_lift₁ h))

/-- Two Proponent moves of a right round after idle histories. -/
theorem stateless_runR {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₂ : Strategy E F₂}
    (h₂ : StatelessMod t₂ σ₂) {A₁ A₂ C : List (Move E F₂)} (hA₁ : A₁ ∈ σ₂) (hA₂ : A₂ ∈ σ₂)
    (hi₁ : Path .idle A₁ .idle) (hi₂ : Path .idle A₂ .idle) (hC : TrapFree t₂ C) {q : F₂.Op}
    {m₁ m₂ : Move E (F₁ ⊕ₛ F₂)} {y₁ y₂ : Pos E (F₁ ⊕ₛ F₂)} (hx₁ : Step (.run (Sum.inr q)) m₁ y₁)
    (hx₂ : Step (.run (Sum.inr q)) m₂ y₂) (ha₁ : A₁ ++ C ++ (Split.halves true [m₁]).2 ∈ σ₂)
    (ha₂ : A₂ ++ C ++ (Split.halves true [m₂]).2 ∈ σ₂) :
    m₁ = m₂ ∨ PTrap (sumTraps t₁ t₂) m₁ ∨ PTrap (sumTraps t₁ t₂) m₂ := by
  obtain ⟨z₁, rfl, hz₁, hzP₁⟩ := step_runR (F₁ := F₁) hx₁
  obtain ⟨z₂, rfl, hz₂, hzP₂⟩ := step_runR (F₁ := F₁) hx₂
  rw [hz₁] at ha₁
  rw [hz₂] at ha₂
  rcases h₂ _ _ hA₁ hA₂ hi₁ hi₂ C z₁ z₂ ha₁ ha₂ hzP₁ hzP₂ hC with h | h | h
  · exact .inl (congrArg lift₂ h)
  · exact .inr (.inl (ptrap_lift₂ h))
  · exact .inr (.inr (ptrap_lift₂ h))

/-- **Pairing preserves statelessness modulo traps.** -/
theorem statelessMod_pair {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁}
    {σ₂ : Strategy E F₂} (h₁ : StatelessMod t₁ σ₁) (h₂ : StatelessMod t₂ σ₂) :
    StatelessMod (sumTraps t₁ t₂) (σ₁.pair σ₂) := by
  intro H₁ H₂ hH₁ hH₂ hi₁ hi₂ c m₁ m₂ hm₁ hm₂ hP₁ hP₂ hfree
  obtain ⟨x, y₁, hx, hxm₁, ha₁, hb₁⟩ := pair_after hi₁ hm₁
  obtain ⟨x', y₂, hx', hxm₂, ha₂, hb₂⟩ := pair_after hi₂ hm₂
  cases Path.det hx' hx
  obtain ⟨u₁, u₂, -, -, hr⟩ := Split.halves_path hx (Split.Rel.idle false)
  have hf := trapFree_halves hfree
  have hI₁ := halves_idle_idle hi₁
  have hI₂ := halves_idle_idle hi₂
  generalize Split.side false c = b at hr ha₁ hb₁ ha₂ hb₂
  cases hr with
  | idle => cases hxm₁; exact absurd hP₁ id
  | waitL => cases hxm₁; exact absurd hP₁ id
  | waitR => cases hxm₁; exact absurd hP₁ id
  | runL q => exact stateless_runL h₁ hH₁.2.1 hH₂.2.1 hI₁.1 hI₂.1 hf.1 hxm₁ hxm₂ ha₁ ha₂
  | runR q => exact stateless_runR h₂ hH₁.2.2 hH₂.2.2 hI₁.2 hI₂.2 hf.2 hxm₁ hxm₂ hb₁ hb₂

/-- The two moves after a lower answer: the history reaches a waiting position, the answer
resumes the round, the next move is a Proponent move of the round. -/
theorem after_answer {s : List (Move E (F₁ ⊕ₛ F₂))} {m : E.Op} {n : E.Ar m}
    {b : Move E (F₁ ⊕ₛ F₂)} {z : Pos E (F₁ ⊕ₛ F₂)} (hp : Path .idle (s ++ [.inl (.ans m n), b]) z) :
    ∃ x y, Path .idle s x ∧ Step x (.inl (.ans m n)) y ∧ Step y b z := by
  obtain ⟨x, hx, hrest⟩ := Path.of_append hp
  cases hrest with
  | cons hs₁ hr =>
    cases hr with
    | cons hs₂ hr =>
      cases hr
      exact ⟨x, _, hx, hs₁, hs₂⟩

/-- **Pairing preserves trap strictness.** -/
theorem strict_pair {tE : Traps E} {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁}
    {σ₂ : Strategy E F₂} (h₁ : Strict tE t₁ σ₁) (h₂ : Strict tE t₂ σ₂) :
    Strict tE (sumTraps t₁ t₂) (σ₁.pair σ₂) := by
  intro s m n b ⟨⟨z, hp⟩, ha, hb⟩ ht
  obtain ⟨x, y, hx, hs₁, hs₂⟩ := after_answer hp
  obtain ⟨u₁, u₂, -, -, hrel⟩ := Split.halves_path hx (Split.Rel.idle false)
  rw [(halves_append false s _).1] at ha
  rw [(halves_append false s _).2] at hb
  generalize Split.side false s = c at hrel ha hb
  cases hs₁ with
  | reply q m n =>
    cases hrel with
    | waitL q m =>
      obtain ⟨z₁, rfl, hz₁, -⟩ := step_runL (F₂ := F₂) hs₂
      have ha' : (Split.halves false s).1 ++ [.inl (.ans m n), z₁] ∈ σ₁ := by
        simpa [Split.halves, hz₁] using ha
      exact ptrap_lift₁ (h₁ _ m n z₁ ha' ht)
    | waitR q m =>
      obtain ⟨z₂, rfl, hz₂, -⟩ := step_runR (F₁ := F₁) hs₂
      have hb' : (Split.halves false s).2 ++ [.inl (.ans m n), z₂] ∈ σ₂ := by
        simpa [Split.halves, hz₂] using hb
      exact ptrap_lift₂ (h₂ _ m n z₂ hb' ht)

end Silmaril.Proofs.Wasm.Det.Game
