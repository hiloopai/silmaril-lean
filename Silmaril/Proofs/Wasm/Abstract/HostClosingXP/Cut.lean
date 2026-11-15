module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Games.Abstract.Module.Thms
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic

/-!
# Cut calls (proofs)

* `wasmHOpenXP_ne_div`, `close_ne_div`: no open behaviour and no closed behaviour ends in `div`
  (the logged relation is inductive, its logs finite; `Shape.close` adds `div` only from a
  diverging callee);
* `subst_cut`: against any closed module whose functions return at most their result arity and
  never diverge, a resolution of a log containing a **cut call** (an answer of more values than
  the callee's result arity) is a trap, made by `Shape.Subst.intTrap` at a call at or before the
  cut call, its log the resolved prefix and that callee's trapping log. Nothing after the trapping
  call is resolved;
* `close_cut`: so in the closure `Shape.close wasmHOpenXP` (`close_ret_len`, `close_ne_div`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem endOfFlow_ne_div {fl : Flow} {s : Store H} : endOfFlow fl s ≠ .div := by
  rcases fl <;> simp [endOfFlow]

theorem tailAns_ne_div {m n : Nat} {b : List Val ⊕ Nat} {s : Store H} :
    tailAns m n b s ≠ .div := by
  unfold tailAns
  split
  · exact endOfFlow_ne_div
  · exact nofun

/-- **No open behaviour diverges.** -/
theorem wasmHOpenXP_ne_div {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) : x.2 ≠ .div := by
  rcases hx with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩
  · exact endOfFlow_ne_div
  · exact tailAns_ne_div
  · exact endOfFlow_ne_div

universe u

/-- A resolution against a module with no diverging behaviour, of an open behaviour that does not
diverge, does not diverge. -/
theorem subst_ne_div {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    (hc : ∀ g s a (c₁ : List (Call sh.E)), (c₁, .div) ∉ c g s a)
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) (he : e ≠ .div) : y.2 ≠ .div := by
  induction h with
  | nil => exact he
  | ext _ ih => exact ih he
  | int _ _ ih => exact ih he
  | intTrap _ => exact nofun
  | intDiv hm => exact absurd hm (hc _ _ _ _)

/-- **No closed behaviour diverges.** -/
theorem close_ne_div {a : Nat} {s : Store H} {vs : List Val} {c₁ : List (Call (wasmHostSig H))} :
    (c₁, .div) ∉ Shape.close wasmHOpenXP a s vs := by
  have key : Shape.close (wasmHOpenXP (H := H)) ≤ fun _ _ _ => {y | y.2 ≠ .div} := by
    refine OrderHom.lfp_le _ ?_
    rintro a s vs y ⟨x, hx, hS⟩
    exact subst_ne_div (c := fun _ _ _ => {y | y.2 ≠ .div}) (fun _ _ _ _ h => h rfl) hS
      (wasmHOpenXP_ne_div hx)
  exact fun h => key a s vs h rfl

/-- **A cut call is resolved only by a trapping callee** (`Shape.Subst.intTrap`), at it or at an
earlier call, against any closed module whose functions return at most their result arity and
never diverge: the resolved behaviour traps, with the resolved prefix's log and the trapping
callee's log. -/
theorem subst_cut {c : (wasmHShape H).ClosedMod}
    (hret : ∀ g (s : Store H) (a : List Val) (c₁ : List (Call (wasmHostSig H))) (ws : List Val)
      (s' : Store H), (c₁, .ret (.inl ws) s') ∈ c g s a →
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[g]? = some fi ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length)
    (hdiv : ∀ g (s : Store H) (a : List Val) (c₁ : List (Call (wasmHostSig H))),
      (c₁, .div) ∉ c g s a)
    {g : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s₁.funcs[g]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hws : rs.length < ws.length)
    {e : End (Store H) (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} :
    ∀ {u w : List (HCall H)},
      Shape.Subst c (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w) e y →
      y.2 = .trap ∧ ∃ (k : Nat) (q c₁ : List (Call (wasmHostSig H))) (g' : Nat) (a' : List Val)
        (s' : Store H) (ans : (List Val ⊕ Nat) × Store H),
        k ≤ u.length ∧
        (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop k =
          ⟨.inr ⟨g', (a', s')⟩, ans⟩ ::
            (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop (k + 1) ∧
        Shape.SubstPre c ((u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).take k) q ∧
        (c₁, .trap) ∈ c g' s' a' ∧ y.1 = q ++ c₁
  | [], w, h => by
    cases h with
    | int hm _ =>
      obtain ⟨fi', ps', rs', hfi', hty', hle⟩ := hret _ _ _ _ _ _ hm
      obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
      omega
    | intTrap hm => exact ⟨rfl, 0, [], _, g, args, s₁, _, le_refl _, rfl, .nil, hm, rfl⟩
    | intDiv hm => exact absurd hm (hdiv _ _ _ _)
  | ⟨.inl m, n⟩ :: u, w, h => by
    cases h with
    | ext h =>
      obtain ⟨ht, k, q, c₁, g', a', s', ans, hk, hd, hp, hm, hy⟩ := subst_cut hret hdiv hfi hty hws h
      refine ⟨ht, k + 1, ⟨m, n⟩ :: q, c₁, g', a', s', ans, Nat.succ_le_succ hk, hd,
        Shape.SubstPre.ext hp, hm, by simp [hy]⟩
  | ⟨.inr ⟨g₀, (a₀, s₀)⟩, (b₀, s₀')⟩ :: u, w, h => by
    cases h with
    | int hm₀ h =>
      obtain ⟨ht, k, q, c₁, g', a', s', ans, hk, hd, hp, hm, hy⟩ := subst_cut hret hdiv hfi hty hws h
      refine ⟨ht, k + 1, _ ++ q, c₁, g', a', s', ans, Nat.succ_le_succ hk, hd,
        Shape.SubstPre.int hm₀ hp, hm, by simp [hy]⟩
    | intTrap hm => exact ⟨rfl, 0, [], _, g₀, a₀, s₀, _, Nat.zero_le _, rfl, .nil, hm, rfl⟩
    | intDiv hm => exact absurd hm (hdiv _ _ _ _)

/-- **In the closure a cut call is resolved only by a trapping callee**, at it or at an earlier
call: never by a return. -/
theorem close_cut {g : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s₁.funcs[g]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hws : rs.length < ws.length)
    {e : End (Store H) (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    {u w : List (HCall H)}
    (h : Shape.Subst (Shape.close wasmHOpenXP)
      (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w) e y) :
    y.2 = .trap ∧ ∃ (k : Nat) (q c₁ : List (Call (wasmHostSig H))) (g' : Nat) (a' : List Val)
        (s' : Store H) (ans : (List Val ⊕ Nat) × Store H),
        k ≤ u.length ∧
        (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop k =
          ⟨.inr ⟨g', (a', s')⟩, ans⟩ ::
            (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop (k + 1) ∧
        Shape.SubstPre (Shape.close wasmHOpenXP)
          ((u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).take k) q ∧
        (c₁, .trap) ∈ Shape.close wasmHOpenXP g' s' a' ∧ y.1 = q ++ c₁ :=
  subst_cut (fun _ _ _ _ _ _ hm => close_ret_len hm) (fun _ _ _ _ => close_ne_div) hfi hty hws h

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
