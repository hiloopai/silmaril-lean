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

/-! ## Unbounded recursion: least fixpoint against divergence -/

/-- The internal call of `true` (itself). -/
def callF : Call (sh₀.E ⊕ₛ sh₀.self) := ⟨.inr ⟨true, (⟨⟩, ⟨⟩)⟩, (⟨⟩, ⟨⟩)⟩

/-- `true` calls itself, then returns; `false` has no behaviour. -/
def m₃ : sh₀.OpenMod
  | true => fun _ _ => {([callF], .ret ⟨⟩ ⟨⟩)}
  | false => fun _ _ => ∅

theorem close_m₃ : close m₃ = ⊥ := by
  refine le_antisymm (OrderHom.lfp_le _ ?_) bot_le
  rintro f s a y ⟨x, hx, hs⟩
  cases f with
  | false => exact hx.elim
  | true =>
    obtain rfl : x = ([callF], .ret ⟨⟩ ⟨⟩) := hx
    cases hs with
    | int hc _ => exact hc
    | intTrap hc => exact hc
    | intDiv hc => exact hc

theorem div_mem_closeD_m₃ :
    (([], .div) : CallBeh sh₀.E sh₀.S PUnit) ∈ closeD m₃ true ⟨⟩ ⟨⟩ := by
  refine .inr ⟨rfl, fun _ => ⟨true, (⟨⟩, ⟨⟩)⟩, fun _ => [], 0, rfl, (fun _ => ?_),
    (fun _ _ => rfl), rfl⟩
  exact ⟨([callF], .ret ⟨⟩ ⟨⟩), rfl, [], (⟨⟩, ⟨⟩), [], rfl, .nil⟩

theorem close_le_closeD (m : sh.OpenMod) : close m ≤ closeD m := fun _ _ _ _ h => .inl h

theorem closeD_lift (c : sh.ClosedMod) : closeD (lift c) = c := by
  funext f s a
  ext y
  constructor
  · rintro (h | ⟨-, g, q, N, h0, hd, -, -⟩)
    · rwa [close_lift] at h
    · obtain ⟨z, ⟨w, -, rfl⟩, u, ans, rest, he, -⟩ := hd 0
      have h1 : (⟨.inr (g (0 + 1)), ans⟩ : Call (sh.E ⊕ₛ sh.self)) ∈
          u ++ ⟨.inr (g (0 + 1)), ans⟩ :: rest := List.mem_append_right _ List.mem_cons_self
      rw [← he] at h1
      obtain ⟨x, -, hx⟩ := List.mem_map.1 h1
      injection hx with h
      cases h
  · intro h
    exact .inl (by rw [close_lift]; exact h)

end Silmaril.Proofs.Games.Abstract.Module
