module

public import Silmaril.Wasm.Abstract.Outcome.Defs

/-!
# Wasm call behaviours as outcome tags: theorems

* `toTag_injective`: reading a behaviour as a tag loses nothing.
* `trapDiv_iff`: the existing `Behaviour.TrapDiv` is exactly equality after
  `collapse`.
* `tagEquiv_iff` and `coarseEquiv_iff`: on behaviour sets, the tagged and the
  trap ≈ divergence equivalences are exactly the existing two-sided demonic
  liftings `Behaviours.Equiv Eq` and `Behaviours.Equiv TrapDiv`.
* `TagEquiv.coarse`, and `trap_diverges_coarse_not_tag`: `{traps}` and
  `{diverges}` are coarse-equivalent but not tag-equivalent.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games.Abstract

universe u

variable {V : Type u}

theorem toTag_injective : Function.Injective (toTag (V := V)) := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [toTag]

theorem trapDiv_iff {b b' : Behaviour V} :
    Behaviour.TrapDiv b b' ↔ (toTag b).collapse = (toTag b').collapse := by
  cases b <;> cases b' <;> simp [Behaviour.TrapDiv, Behaviour.NoResult, toTag, Tag.collapse]

/-- For a relation that is the kernel of `κ`, the two-sided lifting is equality
of images. -/
theorem equiv_iff_image {β : Type u} (κ : Behaviour V → β) {R : Behaviour V → Behaviour V → Prop}
    (hR : ∀ b b', R b b' ↔ κ b = κ b') {s t : Set (Behaviour V)} :
    Behaviours.Equiv R s t ↔ κ '' s = κ '' t := by
  constructor
  · rintro ⟨h₁, h₂⟩
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨b', hb', h⟩ := h₁ b hb
      exact ⟨b', hb', ((hR b b').1 h).symm⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨b', hb', h⟩ := h₂ b hb
      exact ⟨b', hb', (hR b' b).1 h⟩
  · intro h
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨b', hb', he⟩ : κ b ∈ κ '' t := h ▸ ⟨b, hb, rfl⟩
      exact ⟨b', hb', (hR b b').2 he.symm⟩
    · obtain ⟨b', hb', he⟩ : κ b ∈ κ '' s := h ▸ ⟨b, hb, rfl⟩
      exact ⟨b', hb', (hR b' b).2 he⟩

/-- Tagged equivalence of behaviour sets is `Behaviours.Equiv Eq`. -/
theorem tagEquiv_iff {s t : Set (Behaviour V)} : TagEquiv s t ↔ Behaviours.Equiv Eq s t :=
  (equiv_iff_image toTag fun _ _ => toTag_injective.eq_iff.symm).symm

/-- Trap ≈ divergence equivalence of behaviour sets is
`Behaviours.Equiv TrapDiv`. -/
theorem coarseEquiv_iff {s t : Set (Behaviour V)} :
    CoarseEquiv s t ↔ Behaviours.Equiv Behaviour.TrapDiv s t :=
  (equiv_iff_image (fun b => (toTag b).collapse) fun _ _ => trapDiv_iff).symm

/-- Tagged equivalence implies trap ≈ divergence equivalence. -/
theorem TagEquiv.coarse {s t : Set (Behaviour V)} (h : TagEquiv s t) : CoarseEquiv s t := by
  unfold CoarseEquiv
  rw [show (fun b : Behaviour V => (toTag b).collapse) = Tag.collapse ∘ toTag from rfl,
    Set.image_comp, Set.image_comp, h]

/-- A call that traps and a call that diverges. -/
theorem trap_diverges_coarse_not_tag :
    CoarseEquiv ({.traps} : Set (Behaviour V)) {.diverges} ∧
      ¬ TagEquiv ({.traps} : Set (Behaviour V)) {.diverges} := by
  refine ⟨by simp [CoarseEquiv, toTag, Tag.collapse], fun h => ?_⟩
  have : toTag (V := V) .traps ∈ toTag '' {.diverges} := h ▸ ⟨_, rfl, rfl⟩
  simp [toTag] at this

end Silmaril.Wasm.Abstract
