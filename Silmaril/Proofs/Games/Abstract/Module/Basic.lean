module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Abstract modules: proofs

Closing is monotone and a fixpoint of resolution; a module with no internal
calls closes to itself; closing does not commute with joins.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Module

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

theorem resolve_mono {m m' : sh.OpenMod} (h : m ≤ m') : resolve m ≤ resolve m' :=
  fun _ _ _ _ _ ⟨x, hx, hs⟩ => ⟨x, h _ _ _ hx, hs⟩

theorem close_mono {m m' : sh.OpenMod} (h : m ≤ m') : close m ≤ close m' :=
  OrderHom.lfp.monotone (resolve_mono h)

theorem resolve_close (m : sh.OpenMod) : resolve m (close m) = close m := OrderHom.map_lfp _

theorem sup_close_le (m m' : sh.OpenMod) : close m ⊔ close m' ≤ close (m ⊔ m') :=
  sup_le (close_mono le_sup_left) (close_mono le_sup_right)

/-- Without internal calls, resolution is the identity. -/
theorem subst_inl_iff {d : sh.ClosedMod} {R : Type u} (cs : List (Call sh.E)) (e : End sh.S R)
    (z : CallBeh sh.E sh.S R) :
    Subst d (cs.map fun x => (⟨.inl x.1, x.2⟩ : Call (sh.E ⊕ₛ sh.self))) e z ↔ z = (cs, e) := by
  induction cs generalizing z with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .nil e
  | cons x cs ih =>
    obtain ⟨m, n⟩ := x
    constructor
    · intro h
      cases h with
      | ext h' =>
        rename_i y
        obtain rfl := (ih y).1 h'
        rfl
    · rintro rfl
      exact .ext ((ih (cs, e)).2 rfl)

theorem resolve_lift (c d : sh.ClosedMod) : resolve (lift c) d = c := by
  funext f s a
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hs⟩
    obtain rfl := (subst_inl_iff y.1 y.2 z).1 hs
    exact hy
  · intro hz
    exact ⟨_, ⟨z, hz, rfl⟩, (subst_inl_iff z.1 z.2 z).2 rfl⟩

theorem close_lift (c : sh.ClosedMod) : close (lift c) = c :=
  le_antisymm (OrderHom.lfp_le _ (le_of_eq (resolve_lift c c)))
    (OrderHom.le_lfp _ fun b hb => (resolve_lift c b) ▸ hb)

/-! ## Closing does not commute with joins -/

/-- Two functions (`true` calls `false`), unit arguments, results and state, no
imports. -/
abbrev sh₀ : Shape.{0} := ⟨Sig.empty, PUnit, Bool, fun _ => PUnit, fun _ => PUnit⟩

/-- The internal call of `false`. -/
def callG : Call (sh₀.E ⊕ₛ sh₀.self) := ⟨.inr ⟨false, (⟨⟩, ⟨⟩)⟩, (⟨⟩, ⟨⟩)⟩

/-- `true` calls `false` and returns; `false` has no behaviour. -/
def m₁ : sh₀.OpenMod
  | true => fun _ _ => {([callG], .ret ⟨⟩ ⟨⟩)}
  | false => fun _ _ => ∅

/-- `false` returns; `true` has no behaviour. -/
def m₂ : sh₀.OpenMod
  | true => fun _ _ => ∅
  | false => fun _ _ => {([], .ret ⟨⟩ ⟨⟩)}

theorem close_m₁ : close m₁ = ⊥ := by
  refine le_antisymm (OrderHom.lfp_le _ ?_) bot_le
  rintro f s a y ⟨x, hx, hs⟩
  cases f with
  | false => exact hx.elim
  | true =>
    obtain rfl : x = ([callG], .ret ⟨⟩ ⟨⟩) := hx
    cases hs with
    | int hc _ => exact hc
    | intTrap hc => exact hc
    | intDiv hc => exact hc

theorem close_m₂_true (s : PUnit) (a : PUnit) : close m₂ true s a = ∅ := by
  rw [← resolve_close]
  ext y
  simp [resolve, m₂]

theorem close_sup_true :
    (([], .ret ⟨⟩ ⟨⟩) : CallBeh sh₀.E sh₀.S PUnit) ∈ close (m₁ ⊔ m₂) true ⟨⟩ ⟨⟩ := by
  have hg : (([], .ret ⟨⟩ ⟨⟩) : CallBeh sh₀.E sh₀.S PUnit) ∈ close (m₁ ⊔ m₂) false ⟨⟩ ⟨⟩ := by
    rw [← resolve_close]
    exact ⟨([], .ret ⟨⟩ ⟨⟩), .inr (by simp [m₂]), .nil _⟩
  rw [← resolve_close]
  have := Subst.int (rest := []) (e := (.ret ⟨⟩ ⟨⟩ : End sh₀.S PUnit)) (R := PUnit) hg (.nil _)
  exact ⟨([callG], .ret ⟨⟩ ⟨⟩), .inl (by simp [m₁]), this⟩

theorem close_not_sup : close m₁ ⊔ close m₂ ≠ close (m₁ ⊔ m₂) := by
  intro h
  have := close_sup_true
  rw [← h] at this
  rcases this with h₁ | h₂
  · rw [close_m₁] at h₁; exact h₁
  · rw [close_m₂_true] at h₂; exact h₂

end Silmaril.Proofs.Games.Abstract.Module
