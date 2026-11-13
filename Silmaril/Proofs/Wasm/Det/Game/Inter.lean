module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Games.Composition.Defs

/-!
# Interactions of two strategies as interleavings

An interaction of `σ : E ↠ F` with `τ : F ↠ G` (a derivation of `Zip s t p`) is presented as a
single list of letters `Ev E ⊕ Ev F ⊕ Ev G`: `L w` is `σ`'s play, `R w` is `τ`'s play and `V w`
the visible play (`zip_inter`). Along an interaction the positions of the two plays are
coherent (`Coh`, `coh_path`): at every point exactly one of Opponent, `σ` and `τ` is to move.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F G : Sig.{u}}

/-- A letter of an interaction of `σ : E ↠ F` with `τ : F ↠ G`. -/
abbrev Letter (E F G : Sig.{u}) : Type u := Ev E ⊕ Ev F ⊕ Ev G

/-- The part of a letter seen by `σ`. -/
def lv : Letter E F G → Option (Move E F)
  | .inl a => some (.inl a)
  | .inr (.inl b) => some (.inr b)
  | .inr (.inr _) => none

/-- The part of a letter seen by `τ`. -/
def rv : Letter E F G → Option (Move F G)
  | .inl _ => none
  | .inr (.inl b) => some (.inl b)
  | .inr (.inr c) => some (.inr c)

/-- The visible part of a letter. -/
def vv : Letter E F G → Option (Move E G)
  | .inl a => some (.inl a)
  | .inr (.inl _) => none
  | .inr (.inr c) => some (.inr c)

/-- `σ`'s play. -/
def L (w : List (Letter E F G)) : List (Move E F) := w.filterMap lv

/-- `τ`'s play. -/
def R (w : List (Letter E F G)) : List (Move F G) := w.filterMap rv

/-- The visible play. -/
def V (w : List (Letter E F G)) : List (Move E G) := w.filterMap vv

@[simp] theorem L_append (u w : List (Letter E F G)) : L (u ++ w) = L u ++ L w :=
  List.filterMap_append

@[simp] theorem R_append (u w : List (Letter E F G)) : R (u ++ w) = R u ++ R w :=
  List.filterMap_append

@[simp] theorem V_append (u w : List (Letter E F G)) : V (u ++ w) = V u ++ V w :=
  List.filterMap_append

@[simp] theorem L_nil : L ([] : List (Letter E F G)) = [] := rfl
@[simp] theorem R_nil : R ([] : List (Letter E F G)) = [] := rfl
@[simp] theorem V_nil : V ([] : List (Letter E F G)) = [] := rfl

@[simp] theorem L_cons (x : Letter E F G) (w : List (Letter E F G)) :
    L (x :: w) = (lv x).toList ++ L w := by
  cases h : lv x <;> simp [L, h]

@[simp] theorem R_cons (x : Letter E F G) (w : List (Letter E F G)) :
    R (x :: w) = (rv x).toList ++ R w := by
  cases h : rv x <;> simp [R, h]

@[simp] theorem V_cons (x : Letter E F G) (w : List (Letter E F G)) :
    V (x :: w) = (vv x).toList ++ V w := by
  cases h : vv x <;> simp [V, h]

/-- Every interaction is an interleaving. -/
theorem zip_inter {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∃ w : List (Letter E F G), L w = s ∧ R w = t ∧ V w = p := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | left a _ ih =>
    obtain ⟨w, h₁, h₂, h₃⟩ := ih
    exact ⟨.inl a :: w, by simp [lv, h₁], by simp [rv, h₂], by simp [vv, h₃]⟩
  | right c _ ih =>
    obtain ⟨w, h₁, h₂, h₃⟩ := ih
    exact ⟨.inr (.inr c) :: w, by simp [lv, h₁], by simp [rv, h₂], by simp [vv, h₃]⟩
  | sync b _ ih =>
    obtain ⟨w, h₁, h₂, h₃⟩ := ih
    exact ⟨.inr (.inl b) :: w, by simp [lv, h₁], by simp [rv, h₂], by simp [vv, h₃]⟩

/-- The letter of a move of `σ`. -/
def ofL : Move E F → Letter E F G
  | .inl a => .inl a
  | .inr b => .inr (.inl b)

/-- The letter of a move of `τ`. -/
def ofR : Move F G → Letter E F G
  | .inl b => .inr (.inl b)
  | .inr c => .inr (.inr c)

/-- The letter of a visible move. -/
def ofV : Move E G → Letter E F G
  | .inl a => .inl a
  | .inr c => .inr (.inr c)

theorem lv_eq {x : Letter E F G} {z : Move E F} (h : lv x = some z) : x = ofL z := by
  rcases x with a | b | c <;> simp only [lv, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

theorem rv_eq {x : Letter E F G} {y : Move F G} (h : rv x = some y) : x = ofR y := by
  rcases x with a | b | c <;> simp only [rv, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

theorem vv_eq {x : Letter E F G} {o : Move E G} (h : vv x = some o) : x = ofV o := by
  rcases x with a | b | c <;> simp only [vv, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

theorem lv_inj {x₁ x₂ : Letter E F G} {z : Move E F} (h₁ : lv x₁ = some z)
    (h₂ : lv x₂ = some z) : x₁ = x₂ := by
  rw [lv_eq h₁, lv_eq h₂]

theorem rv_inj {x₁ x₂ : Letter E F G} {y : Move F G} (h₁ : rv x₁ = some y)
    (h₂ : rv x₂ = some y) : x₁ = x₂ := by
  rw [rv_eq h₁, rv_eq h₂]

theorem vv_inj {x₁ x₂ : Letter E F G} {o : Move E G} (h₁ : vv x₁ = some o)
    (h₂ : vv x₂ = some o) : x₁ = x₂ := by
  rw [vv_eq h₁, vv_eq h₂]

/-- A trap of `τ` is visible. -/
theorem rv_ptrap {tG : Traps G} {x : Letter E F G} {y : Move F G} (h : rv x = some y)
    (ht : PTrap tG y) : ∃ y' : Move E G, vv x = some y' ∧ PTrap tG y' := by
  rw [rv_eq h]
  rcases y with b | (c | ⟨q, r⟩)
  · exact ht.elim
  · exact ht.elim
  · exact ⟨.inr (.ans q r), rfl, ht⟩

/-- A trap of `σ` is a hidden answer. -/
theorem lv_ptrap {tF : Traps F} {x : Letter E F G} {z : Move E F} (h : lv x = some z)
    (ht : PTrap tF z) : ∃ m n, x = .inr (.inl (.ans m n)) ∧ tF m n := by
  rw [lv_eq h]
  rcases z with a | (b | ⟨m, n⟩)
  · exact ht.elim
  · exact ht.elim
  · exact ⟨m, n, rfl, ht⟩

/-! ## Coherent positions -/

/-- The positions of the two plays of an interaction. -/
inductive Coh : Pos E F → Pos F G → Prop
  | idle : Coh .idle .idle
  | run (q : G.Op) : Coh .idle (.run q)
  | sub (q : G.Op) (m : F.Op) : Coh (.run m) (.wait q m)
  | wait (q : G.Op) (m : F.Op) (e : E.Op) : Coh (.wait m e) (.wait q m)

theorem path_single {x y : Pos E F} {o : Move E F} (h : Path x [o] y) : Step x o y := by
  cases h with
  | cons hs hp => cases hp; exact hs

theorem path_nil {x y : Pos E F} (h : Path x [] y) : x = y := by
  cases h; rfl

theorem coh_E {x x' : Pos E F} {y : Pos F G} {a : Ev E} (hc : Coh x y)
    (hs : Step x (.inl a) x') : Coh x' y := by
  cases hs <;> cases hc <;> constructor

theorem coh_F {x x' : Pos E F} {y y' : Pos F G} {b : Ev F} (hc : Coh x y)
    (h₁ : Step x (.inr b) x') (h₂ : Step y (.inl b) y') : Coh x' y' := by
  cases h₁ <;> cases h₂ <;> cases hc <;> constructor

theorem coh_G {x : Pos E F} {y y' : Pos F G} {c : Ev G} (hc : Coh x y)
    (hs : Step y (.inr c) y') : Coh x y' := by
  cases hs <;> cases hc <;> constructor

/-- One letter keeps the positions coherent. -/
theorem coh_step {x x' : Pos E F} {y y' : Pos F G} (hc : Coh x y) (a : Letter E F G)
    (hx : Path x (lv a).toList x') (hy : Path y (rv a).toList y') : Coh x' y' := by
  rcases a with a | b | c
  · have hy' : y = y' := path_nil hy
    exact hy' ▸ coh_E hc (path_single hx)
  · exact coh_F hc (path_single hx) (path_single hy)
  · have hx' : x = x' := path_nil hx
    exact hx' ▸ coh_G hc (path_single hy)

/-- Positions stay coherent along an interaction. -/
theorem coh_path {x x' : Pos E F} {y y' : Pos F G} (hc : Coh x y) (w : List (Letter E F G))
    (hx : Path x (L w) x') (hy : Path y (R w) y') : Coh x' y' := by
  induction w generalizing x y with
  | nil => rw [path_nil hx, path_nil hy] at hc; exact hc
  | cons a w ih =>
    rw [L_cons] at hx
    rw [R_cons] at hy
    obtain ⟨x₁, hx₁, hx₂⟩ := Path.of_append hx
    obtain ⟨y₁, hy₁, hy₂⟩ := Path.of_append hy
    exact ih (coh_step hc a hx₁ hy₁) hx₂ hy₂

end Silmaril.Proofs.Wasm.Det.Game
