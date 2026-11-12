module

public import Silmaril.Games.Zip.Defs
import Silmaril.Proofs.Games.Zip.Basic

/-!
# Parallel interaction with hiding: theorems

The main result is `Zip.assoc`: interacting `s` with `t` and then with `r`
yields the same visible traces as interacting `t` with `r` first. The other
results are inversion and extension lemmas used by game composition. Proofs
live in `Silmaril.Proofs.Games.Zip.Basic`.
-/

public section

namespace Silmaril.Games.Zip

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}

/-- Prepend visible moves of the left trace. -/
theorem prepend_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (as : List α) : Zip (as.map .inl ++ s) t (as.map .inl ++ p) :=
  Silmaril.Proofs.Games.Zip.prepend_left h as

/-- Prepend visible moves of the right trace. -/
theorem prepend_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (cs : List γ) : Zip s (cs.map .inr ++ t) (cs.map .inr ++ p) :=
  Silmaril.Proofs.Games.Zip.prepend_right h cs

/-- Append a visible move of the left trace. -/
theorem append_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (a : α) : Zip (s ++ [.inl a]) t (p ++ [.inl a]) :=
  Silmaril.Proofs.Games.Zip.append_left h a

/-- Append a visible move of the right trace. -/
theorem append_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (c : γ) : Zip s (t ++ [.inr c]) (p ++ [.inr c]) :=
  Silmaril.Proofs.Games.Zip.append_right h c

/-- Interacting with the empty right trace: the left trace may only make
visible moves. -/
theorem nil_right_iff {s : List (α ⊕ β)} {p : List (α ⊕ γ)} :
    Zip s ([] : List (β ⊕ γ)) p ↔ ∃ as : List α, s = as.map .inl ∧ p = as.map .inl :=
  Silmaril.Proofs.Games.Zip.nil_right_iff

/-- Interacting with the empty left trace: the right trace may only make
visible moves. -/
theorem nil_left_iff {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} :
    Zip ([] : List (α ⊕ β)) t p ↔ ∃ cs : List γ, t = cs.map .inr ∧ p = cs.map .inr :=
  Silmaril.Proofs.Games.Zip.nil_left_iff

/-- Inversion when the left trace starts with a visible move. -/
theorem inl_left {a : α} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip (.inl a :: s) t p) :
    ∃ (cs : List γ) (t' : List (β ⊕ γ)) (p' : List (α ⊕ γ)),
      t = cs.map .inr ++ t' ∧ p = cs.map .inr ++ .inl a :: p' ∧ Zip s t' p' :=
  Silmaril.Proofs.Games.Zip.inl_left h

/-- Inversion when the left trace starts with a shared event. -/
theorem inr_left {b : β} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip (.inr b :: s) t p) :
    ∃ (cs : List γ) (t' : List (β ⊕ γ)) (p' : List (α ⊕ γ)),
      t = cs.map .inr ++ .inl b :: t' ∧ p = cs.map .inr ++ p' ∧ Zip s t' p' :=
  Silmaril.Proofs.Games.Zip.inr_left h

/-- Inversion when the right trace starts with a shared event. -/
theorem inl_right {b : β} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s (.inl b :: t) p) :
    ∃ (as : List α) (s' : List (α ⊕ β)) (p' : List (α ⊕ γ)),
      s = as.map .inl ++ .inr b :: s' ∧ p = as.map .inl ++ p' ∧ Zip s' t p' :=
  Silmaril.Proofs.Games.Zip.inl_right h

/-- Inversion when the right trace starts with a visible move. -/
theorem inr_right {c : γ} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s (.inr c :: t) p) :
    ∃ (as : List α) (s' : List (α ⊕ β)) (p' : List (α ⊕ γ)),
      s = as.map .inl ++ s' ∧ p = as.map .inl ++ .inr c :: p' ∧ Zip s' t p' :=
  Silmaril.Proofs.Games.Zip.inr_right h

/-- Every prefix of the visible trace comes from prefixes of the two traces. -/
theorem of_prefix {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p q : List (α ⊕ γ)}
    (h : Zip s t p) (hq : q <+: p) : ∃ s' t', s' <+: s ∧ t' <+: t ∧ Zip s' t' q :=
  Silmaril.Proofs.Games.Zip.of_prefix h hq

/-- Associativity of interaction with hiding. -/
theorem assoc {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {r : List (γ ⊕ δ)} {p : List (α ⊕ δ)} :
    (∃ u, Zip s t u ∧ Zip u r p) ↔ (∃ v, Zip t r v ∧ Zip s v p) :=
  ⟨fun ⟨_, h₁, h₂⟩ => Silmaril.Proofs.Games.Zip.assoc_mp h₁ h₂,
    fun ⟨_, h₁, h₂⟩ => Silmaril.Proofs.Games.Zip.assoc_mpr h₁ h₂⟩

end Silmaril.Games.Zip
