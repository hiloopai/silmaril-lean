module

public import Silmaril.Games.Zip.Defs

/-!
# Parallel interaction with hiding: proofs

Proofs for `Silmaril.Games.Zip.Thms`. The associativity argument is the usual
one for synchronised shuffles.
-/

public section

namespace Silmaril.Proofs.Games.Zip

open Silmaril.Games

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

theorem prepend_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (as : List α) :
    Zip (as.map .inl ++ s) t (as.map .inl ++ p) := by
  induction as with
  | nil => exact h
  | cons a as ih => exact .left a ih

theorem prepend_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (cs : List γ) :
    Zip s (cs.map .inr ++ t) (cs.map .inr ++ p) := by
  induction cs with
  | nil => exact h
  | cons c cs ih => exact .right c ih

theorem nil_right_iff {s : List (α ⊕ β)} {p : List (α ⊕ γ)} :
    Zip s ([] : List (β ⊕ γ)) p ↔ ∃ as : List α, s = as.map .inl ∧ p = as.map .inl := by
  constructor
  · intro h
    generalize ht : ([] : List (β ⊕ γ)) = t at h
    induction h with
    | nil => exact ⟨[], rfl, rfl⟩
    | left a _ ih =>
      obtain ⟨as, rfl, rfl⟩ := ih ht
      exact ⟨a :: as, rfl, rfl⟩
    | right => cases ht
    | sync => cases ht
  · rintro ⟨as, rfl, rfl⟩
    simpa using prepend_left (Zip.nil (α := α) (β := β) (γ := γ)) as

theorem nil_left_iff {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} :
    Zip ([] : List (α ⊕ β)) t p ↔ ∃ cs : List γ, t = cs.map .inr ∧ p = cs.map .inr := by
  constructor
  · intro h
    generalize hs : ([] : List (α ⊕ β)) = s at h
    induction h with
    | nil => exact ⟨[], rfl, rfl⟩
    | right c _ ih =>
      obtain ⟨cs, rfl, rfl⟩ := ih hs
      exact ⟨c :: cs, rfl, rfl⟩
    | left => cases hs
    | sync => cases hs
  · rintro ⟨cs, rfl, rfl⟩
    simpa using prepend_right (Zip.nil (α := α) (β := β) (γ := γ)) cs

/-- A visible left move at the head of the left trace is preceded only by
visible moves of the right trace. -/
theorem inl_left {a : α} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip (.inl a :: s) t p) :
    ∃ (cs : List γ) (t' : List (β ⊕ γ)) (p' : List (α ⊕ γ)),
      t = cs.map .inr ++ t' ∧ p = cs.map .inr ++ .inl a :: p' ∧ Zip s t' p' := by
  generalize hS : (.inl a :: s : List (α ⊕ β)) = S at h
  induction h with
  | nil => cases hS
  | left a' h _ =>
    cases hS
    exact ⟨[], _, _, rfl, rfl, h⟩
  | right c _ ih =>
    obtain ⟨cs, t', p', rfl, rfl, h⟩ := ih hS
    exact ⟨c :: cs, t', p', rfl, rfl, h⟩
  | sync => cases hS

/-- A shared event at the head of the left trace is preceded only by visible
moves of the right trace. -/
theorem inr_left {b : β} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip (.inr b :: s) t p) :
    ∃ (cs : List γ) (t' : List (β ⊕ γ)) (p' : List (α ⊕ γ)),
      t = cs.map .inr ++ .inl b :: t' ∧ p = cs.map .inr ++ p' ∧ Zip s t' p' := by
  generalize hS : (.inr b :: s : List (α ⊕ β)) = S at h
  induction h with
  | nil => cases hS
  | left => cases hS
  | right c _ ih =>
    obtain ⟨cs, t', p', rfl, rfl, h⟩ := ih hS
    exact ⟨c :: cs, t', p', rfl, rfl, h⟩
  | sync b' h _ =>
    cases hS
    exact ⟨[], _, _, rfl, rfl, h⟩

/-- A shared event at the head of the right trace is preceded only by visible
moves of the left trace. -/
theorem inl_right {b : β} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s (.inl b :: t) p) :
    ∃ (as : List α) (s' : List (α ⊕ β)) (p' : List (α ⊕ γ)),
      s = as.map .inl ++ .inr b :: s' ∧ p = as.map .inl ++ p' ∧ Zip s' t p' := by
  generalize hT : (.inl b :: t : List (β ⊕ γ)) = T at h
  induction h with
  | nil => cases hT
  | left a _ ih =>
    obtain ⟨as, s', p', rfl, rfl, h⟩ := ih hT
    exact ⟨a :: as, s', p', rfl, rfl, h⟩
  | right => cases hT
  | sync b' h _ =>
    cases hT
    exact ⟨[], _, _, rfl, rfl, h⟩

/-- A visible move at the head of the right trace is preceded only by visible
moves of the left trace. -/
theorem inr_right {c : γ} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s (.inr c :: t) p) :
    ∃ (as : List α) (s' : List (α ⊕ β)) (p' : List (α ⊕ γ)),
      s = as.map .inl ++ s' ∧ p = as.map .inl ++ .inr c :: p' ∧ Zip s' t p' := by
  generalize hT : (.inr c :: t : List (β ⊕ γ)) = T at h
  induction h with
  | nil => cases hT
  | left a _ ih =>
    obtain ⟨as, s', p', rfl, rfl, h⟩ := ih hT
    exact ⟨a :: as, s', p', rfl, rfl, h⟩
  | right c' h _ =>
    cases hT
    exact ⟨[], _, _, rfl, rfl, h⟩
  | sync => cases hT

theorem assoc_mp {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {u : List (α ⊕ γ)}
    {r : List (γ ⊕ δ)} {p : List (α ⊕ δ)} (h₁ : Zip s t u) (h₂ : Zip u r p) :
    ∃ v, Zip t r v ∧ Zip s v p := by
  induction h₁ generalizing r p with
  | nil =>
    obtain ⟨cs, rfl, rfl⟩ := nil_left_iff.1 h₂
    exact ⟨cs.map .inr, nil_left_iff.2 ⟨cs, rfl, rfl⟩, nil_left_iff.2 ⟨cs, rfl, rfl⟩⟩
  | left a _ ih =>
    obtain ⟨ds, r', p', rfl, rfl, h⟩ := inl_left h₂
    obtain ⟨v, hv₁, hv₂⟩ := ih h
    exact ⟨ds.map .inr ++ v, prepend_right hv₁ ds, prepend_right (.left a hv₂) ds⟩
  | right c _ ih =>
    obtain ⟨ds, r', p', rfl, rfl, h⟩ := inr_left h₂
    obtain ⟨v, hv₁, hv₂⟩ := ih h
    exact ⟨ds.map .inr ++ v, prepend_right (.sync c hv₁) ds, prepend_right hv₂ ds⟩
  | sync b _ ih =>
    obtain ⟨v, hv₁, hv₂⟩ := ih h₂
    exact ⟨.inl b :: v, .left b hv₁, .sync b hv₂⟩

theorem assoc_mpr {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {v : List (β ⊕ δ)}
    {r : List (γ ⊕ δ)} {p : List (α ⊕ δ)} (h₁ : Zip t r v) (h₂ : Zip s v p) :
    ∃ u, Zip s t u ∧ Zip u r p := by
  induction h₁ generalizing s p with
  | nil =>
    obtain ⟨as, rfl, rfl⟩ := nil_right_iff.1 h₂
    exact ⟨as.map .inl, nil_right_iff.2 ⟨as, rfl, rfl⟩, nil_right_iff.2 ⟨as, rfl, rfl⟩⟩
  | left b _ ih =>
    obtain ⟨as, s', p', rfl, rfl, h⟩ := inl_right h₂
    obtain ⟨u, hu₁, hu₂⟩ := ih h
    exact ⟨as.map .inl ++ u, prepend_left (.sync b hu₁) as, prepend_left hu₂ as⟩
  | right d _ ih =>
    obtain ⟨as, s', p', rfl, rfl, h⟩ := inr_right h₂
    obtain ⟨u, hu₁, hu₂⟩ := ih h
    exact ⟨as.map .inl ++ u, prepend_left hu₁ as, prepend_left (.right d hu₂) as⟩
  | sync c _ ih =>
    obtain ⟨u, hu₁, hu₂⟩ := ih h₂
    exact ⟨.inr c :: u, .right c hu₁, .sync c hu₂⟩

end Silmaril.Proofs.Games.Zip
