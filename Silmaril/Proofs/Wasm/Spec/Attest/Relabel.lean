module

public import Silmaril.Wasm.Spec.Attest.Relabel.Defs
public import Silmaril.Games.Strategy.Defs

/-!
# Relabelled plays

The image of a play under a relabelling of the lower interface (`Relabel.move`) follows the
image of its positions (`path_map`), prefixes of images are images of prefixes
(`prefix_map`), and an Opponent move after an image is the image of an Opponent move
(`receptive_map`). These are the strategy laws of `Strategy.relabel`
(`Silmaril.Wasm.Spec.Attest.Defs`).

New proofs (no source).
-/

public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Spec.Attest

universe u

variable {E E' F : Sig.{u}} (ι : Relabel E E')

/-- A step of the automaton is a step of the relabelled automaton. -/
theorem step_map {x y : Pos E F} {o : Move E F} (h : Step x o y) :
    Step (ι.pos x) (ι.move o) (ι.pos y) := by
  cases h with
  | ask q => exact .ask q
  | call q m => exact .call q (ι.op m)
  | reply q m n => exact .reply q (ι.op m) ((ι.ar m).symm n)
  | ret q r => exact .ret q r

/-- A path is a path of the relabelled automaton. -/
theorem path_map {x y : Pos E F} {q : List (Move E F)} (h : Path x q y) :
    Path (ι.pos x) (q.map ι.move) (ι.pos y) := by
  induction h with
  | nil x => exact .nil _
  | cons hs _ ih => exact .cons (step_map ι hs) ih

/-- Prefixes of an image are images of prefixes. -/
theorem prefix_map {α β : Type u} (f : α → β) :
    ∀ {s : List β} {q : List α}, s <+: q.map f → ∃ q', q' <+: q ∧ s = q'.map f
  | [], _, _ => ⟨[], List.nil_prefix, rfl⟩
  | b :: s, a :: q, h => by
    have hb : b = f a ∧ s <+: q.map f := List.cons_prefix_cons.1 h
    obtain ⟨q', hq', rfl⟩ := prefix_map f hb.2
    exact ⟨a :: q', List.cons_prefix_cons.2 ⟨rfl, hq'⟩, by rw [hb.1]; rfl⟩
  | _ :: _, [], h => absurd (List.eq_nil_of_prefix_nil h) (List.cons_ne_nil _ _)

/-- **An Opponent move after an image is the image of an Opponent move** from the preimage
position. -/
theorem receptive_map {x₀ : Pos E F} {x y : Pos E' F} {o : Move E' F} (hx : ι.pos x₀ = x)
    (hxy : Step x o y) (ho : o.IsO) :
    ∃ o₀ y₀, Step x₀ o₀ y₀ ∧ o₀.IsO ∧ ι.move o₀ = o := by
  cases hxy with
  | ask q =>
    show ∃ o₀ y₀, Step x₀ o₀ y₀ ∧ o₀.IsO ∧ ι.move o₀ = .inr (.ask q)
    have hx₀ : x₀ = .idle := by cases x₀ <;> first | rfl | cases hx
    exact ⟨.inr (.ask q), .run q, hx₀ ▸ .ask q, trivial, rfl⟩
  | reply q m n =>
    show ∃ o₀ y₀, Step x₀ o₀ y₀ ∧ o₀.IsO ∧ ι.move o₀ = .inl (.ans m n)
    obtain ⟨m₀, rfl, rfl⟩ : ∃ m₀, x₀ = .wait q m₀ ∧ ι.op m₀ = m := by
      cases x₀ with
      | idle => cases hx
      | run _ => cases hx
      | wait q₀ m₀ =>
        have hw : Pos.wait q₀ (ι.op m₀) = (.wait q m : Pos E' F) := hx
        cases hw
        exact ⟨m₀, rfl, rfl⟩
    refine ⟨.inl (.ans m₀ (ι.ar m₀ n)), .run q, .reply q m₀ _, trivial, ?_⟩
    simp only [Relabel.move, Sum.map_inl, Relabel.ev, Equiv.symm_apply_apply]
  | call q m => exact ho.elim
  | ret q r => exact ho.elim

end Silmaril.Proofs.Wasm.Spec.Attest
