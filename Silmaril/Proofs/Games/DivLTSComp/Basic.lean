module

public import Silmaril.Games.DivLTSComp.Defs

/-!
# Runs of composite transition systems

Elementary facts about `LTS.comp` and `Zip` used by the proof that the
divergence-observing strategy of a composite system is the composite of the
divergence-observing strategies (`Silmaril.Games.DivLTSComp.Thms`).

* `comp_run`, `run_comp`: a run of `L₁.comp L₂` is an interleaving (`Zip`) of a
  run of `L₁` and a run of `L₂`, and conversely. Restated with the proofs of
  `Silmaril.Proofs.Games.LTS.Comp` (this topic may not import another topic's
  proofs).
* `zip_append`, `zip_drop`: interactions concatenate, and the increments of
  nested interactions interact. Restated with the proofs of
  `Silmaril.Proofs.Games.DivComp.ZipChain`.
* `silent_of_run_nil`, `run_nil_of_silent`: a run without visible moves is a
  sequence of silent steps.
* `compStep_silent_cases`: a silent step of the composite is a silent step of
  one side or a hidden synchronisation.
* `transGen_of_zip_nil`: a run of the composite that hides a non-empty
  exchange performs at least one silent step.
-/

public section

namespace Silmaril.Proofs.Games.DivLTSComp

open Silmaril.Games

universe u u₁ u₂ u₃

section Zip

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃}

theorem zip_append {s s' : List (α ⊕ β)} {t t' : List (β ⊕ γ)} {p p' : List (α ⊕ γ)}
    (h : Zip s t p) (h' : Zip s' t' p') : Zip (s ++ s') (t ++ t') (p ++ p') := by
  induction h with
  | nil => simpa using h'
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

private theorem drop_left {a : α} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip (.inl a :: S) T (.inl a :: P)) : Zip S T P := by
  obtain ⟨cs, t', p', ht, hp, h'⟩ := Zip.inl_left h
  cases cs with
  | nil =>
    have hp' : P = p' := (List.cons.inj hp).2
    rw [ht, hp']
    exact h'
  | cons c cs => simp at hp

private theorem drop_right {c : γ} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip S (.inr c :: T) (.inr c :: P)) : Zip S T P := by
  obtain ⟨as, s', p', hs, hp, h'⟩ := Zip.inr_right h
  cases as with
  | nil =>
    have hp' : P = p' := (List.cons.inj hp).2
    rw [hs, hp']
    exact h'
  | cons a as => simp at hp

private theorem drop_sync {b : β} {S : List (α ⊕ β)} {T : List (β ⊕ γ)} {P : List (α ⊕ γ)}
    (h : Zip (.inr b :: S) (.inl b :: T) P) : Zip S T P := by
  obtain ⟨cs, t', p', ht, hp, h'⟩ := Zip.inr_left h
  cases cs with
  | nil =>
    have ht' : T = t' := (List.cons.inj ht).2
    rw [ht', hp]
    exact h'
  | cons c cs => simp at ht

theorem zip_drop {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    ∀ {ds dt dp}, Zip (s ++ ds) (t ++ dt) (p ++ dp) → Zip ds dt dp := by
  induction h with
  | nil => exact fun h => by simpa using h
  | left a _ ih => exact fun h => ih (drop_left h)
  | right c _ ih => exact fun h => ih (drop_right h)
  | sync b _ ih => exact fun h => ih (drop_sync h)

/-- The visible trace of an interaction is no longer than the two traces together. -/
theorem zip_length {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.length ≤ s.length + t.length := by
  induction h with
  | nil => exact le_refl _
  | left a _ ih => simp only [List.length_cons]; omega
  | right c _ ih => simp only [List.length_cons]; omega
  | sync b _ ih => simp only [List.length_cons]; omega

end Zip

variable {E F G : Sig.{u}}

/-- A run without visible moves is a sequence of silent steps. -/
theorem silent_of_run_nil {L : LTS E F} {x y : L.State} {p : List (Move E F)}
    (h : L.Run x p y) (hp : p = []) : Relation.ReflTransGen L.Silent x y := by
  induction h with
  | nil x => exact .refl
  | tau hs _ ih => exact .head hs (ih hp)
  | vis _ _ _ => cases hp

/-- A sequence of silent steps is a run without visible moves. -/
theorem run_nil_of_silent {L : LTS E F} {x y : L.State}
    (h : Relation.ReflTransGen L.Silent x y) : L.Run x [] y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .nil _
  | head hs _ ih => exact .tau hs ih

theorem comp_run {L₁ : LTS E F} {L₂ : LTS F G} {z z' : (L₁.comp L₂).State}
    {p : List (Move E G)} (h : (L₁.comp L₂).Run z p z') :
    ∃ s t, L₁.Run z.1 s z'.1 ∧ L₂.Run z.2 t z'.2 ∧ Zip s t p := by
  induction h with
  | nil => exact ⟨[], [], .nil _, .nil _, .nil⟩
  | tau hs _ ih =>
    obtain ⟨s, t, h₁, h₂, hz⟩ := ih
    cases hs with
    | tau₁ hs => exact ⟨s, t, .tau hs h₁, h₂, hz⟩
    | tau₂ hs => exact ⟨s, t, h₁, .tau hs h₂, hz⟩
    | sync f hs ht => exact ⟨_, _, .vis hs h₁, .vis ht h₂, .sync f hz⟩
  | vis hs _ ih =>
    obtain ⟨s, t, h₁, h₂, hz⟩ := ih
    cases hs with
    | left e hs => exact ⟨_, t, .vis hs h₁, h₂, .left e hz⟩
    | right g hs => exact ⟨s, _, h₁, .vis hs h₂, .right g hz⟩

theorem run_comp {L₁ : LTS E F} {L₂ : LTS F G} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} (hz : Zip s t p) :
    ∀ {x x' y y'}, L₁.Run x s x' → L₂.Run y t y' → (L₁.comp L₂).Run (x, y) p (x', y') := by
  induction hz with
  | nil =>
    intro x x' y y' h₁ h₂
    simpa using (LTS.comp_taus₁ y h₁).append (LTS.comp_taus₂ x' h₂)
  | left e _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨x₁, x₂, ht, hs, hr⟩ := h₁.cons_inv
    simpa using (LTS.comp_taus₁ y ht).append (.vis (LTS.CompStep.left e hs) (ih hr h₂))
  | right g _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨y₁, y₂, ht, hs, hr⟩ := h₂.cons_inv
    simpa using (LTS.comp_taus₂ x ht).append (.vis (LTS.CompStep.right g hs) (ih h₁ hr))
  | sync f _ ih =>
    intro x x' y y' h₁ h₂
    obtain ⟨x₁, x₂, ht₁, hs₁, hr₁⟩ := h₁.cons_inv
    obtain ⟨y₁, y₂, ht₂, hs₂, hr₂⟩ := h₂.cons_inv
    simpa using (LTS.comp_taus₁ y ht₁).append ((LTS.comp_taus₂ x₁ ht₂).append
      (.tau (LTS.CompStep.sync f hs₁ hs₂) (ih hr₁ hr₂)))

/-- A silent step of the composite: a silent step of one side, or a hidden synchronisation. -/
theorem compStep_silent_cases {L₁ : LTS E F} {L₂ : LTS F G} {z z' : (L₁.comp L₂).State}
    (h : (L₁.comp L₂).step z none z') :
    (L₁.step z.1 none z'.1 ∧ z'.2 = z.2) ∨ (L₂.step z.2 none z'.2 ∧ z'.1 = z.1) ∨
      ∃ b, L₁.step z.1 (some (.inr b)) z'.1 ∧ L₂.step z.2 (some (.inl b)) z'.2 := by
  cases h with
  | tau₁ hs => exact .inl ⟨hs, rfl⟩
  | tau₂ hs => exact .inr (.inl ⟨hs, rfl⟩)
  | sync b hs ht => exact .inr (.inr ⟨b, hs, ht⟩)

/-- A run of the composite hiding a non-empty exchange performs a silent step. -/
theorem transGen_of_zip_nil {L₁ : LTS E F} {L₂ : LTS F G} {s : List (Move E F)}
    {t : List (Move F G)} (hz : Zip s t []) (hne : s ≠ [] ∨ t ≠ []) {x x' : L₁.State}
    {y y' : L₂.State} (h₁ : L₁.Run x s x') (h₂ : L₂.Run y t y') :
    Relation.TransGen (L₁.comp L₂).Silent (x, y) (x', y') := by
  cases hz with
  | nil => simp at hne
  | sync b hz' =>
    obtain ⟨x₁, x₂, ht₁, hs₁, hr₁⟩ := h₁.cons_inv
    obtain ⟨y₁, y₂, ht₂, hs₂, hr₂⟩ := h₂.cons_inv
    have hpre : Relation.ReflTransGen (L₁.comp L₂).Silent (x, y) (x₁, y₁) :=
      silent_of_run_nil ((LTS.comp_taus₁ y ht₁).append (LTS.comp_taus₂ x₁ ht₂)) rfl
    have hpost : Relation.ReflTransGen (L₁.comp L₂).Silent (x₂, y₂) (x', y') :=
      silent_of_run_nil (run_comp hz' hr₁ hr₂) rfl
    have hsync : (L₁.comp L₂).Silent (x₁, y₁) (x₂, y₂) := LTS.CompStep.sync b hs₁ hs₂
    exact Relation.TransGen.trans_right hpre (Relation.TransGen.head' hsync hpost)
