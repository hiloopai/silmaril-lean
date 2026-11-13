module

public import Silmaril.Proofs.Wasm.Models.V2Core.InFeat

/-!
# Valid 2.0 constant expressions are single instructions

`Expr_ok_const` (`wasm-2.0/6-typing:564`) types a constant expression at one value type, and
every constant instruction pushes exactly one value onto an unchanged stack, so a valid constant
expression is a single constant instruction (`exprOkConst_single`). Its Core image is then a
Wasm 1.0/2.0 constant expression of `v20` (`constExpr_v20`), with no need for extended
constants.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Models

/-- A constant instruction consumes nothing and produces one value. -/
theorem instrConst_type {C : Context} {i : Silmaril.Wasm.V2.Instr} {u : InstrType}
    (hc : InstrConst C i) (hu : InstrOk C i u) : u.params = [] ∧ u.results.length = 1 := by
  cases hc <;> cases hu <;> exact ⟨rfl, rfl⟩

/-- A weakening of a type with no parameters and one result adds one entry to the stack. -/
theorem weaken_len {u : InstrType} {t₁ t₂ : CResultType} (hp : u.params = [])
    (hr : u.results.length = 1) (hw : InstrType.Weaken u ⟨t₁, t₂⟩) :
    t₂.length = t₁.length + 1 := by
  obtain ⟨ts, h₁, h₂⟩ := hw
  have e₁ : t₁.length = ts.length := by
    simpa [hp] using (List.Forall₂.length_eq h₁)
  have e₂ : (ts ++ u.results).length = t₂.length := List.Forall₂.length_eq h₂
  simp only [List.length_append, hr] at e₂
  omega

/-- A sequence of constant instructions adds one stack entry per instruction. -/
theorem constLen {C : Context} :
    ∀ {is : List Silmaril.Wasm.V2.Instr} {t₁ t₃ : CResultType},
      (∀ i ∈ is, InstrConst C i) → InstrsOk C is ⟨t₁, t₃⟩ →
        t₃.length = t₁.length + is.length
  | [], t₁, t₃, _, h => by
    have e : t₁.length = t₃.length := List.Forall₂.length_eq (InstrsOk.nil_inv h)
    simp [e]
  | i :: is, t₁, t₃, hc, h => by
    obtain ⟨t₂, u, hu, hw, hrest⟩ := InstrsOk.cons_inv h
    have hi : InstrConst C i := hc i (by simp)
    obtain ⟨hp, hr⟩ := instrConst_type hi hu
    have e₁ : t₂.length = t₁.length + 1 := weaken_len hp hr hw
    have e₂ : t₃.length = t₂.length + is.length :=
      constLen (fun j hj => hc j (by simp [hj])) hrest
    simp only [List.length_cons]
    omega

/-- **A valid 2.0 constant expression is a single constant instruction.** -/
theorem exprOkConst_single {C : Context} {e : Silmaril.Wasm.V2.Expr}
    {t : Silmaril.Wasm.V2.ValType} (h : ExprOkConst C e t) :
    ∃ i, e = [i] ∧ InstrConst C i := by
  have hl : 1 = 0 + e.length := constLen h.const h.typed
  match e, hl with
  | [i], _ => exact ⟨i, rfl, h.const i (by simp)⟩

/-- The Core image of a constant instruction is a simple constant. -/
theorem simpleConst_image {C : Context} {i : Silmaril.Wasm.V2.Instr}
    (hi : InstrConst C i) {ce : Silmaril.Wasm.Expr}
    (h : Silmaril.Wasm.V2.Expr.toCore [i] = some ce) : simpleConst ce = true := by
  cases hi <;> simp [Silmaril.Wasm.V2.Expr.toCore, Silmaril.Wasm.V2.Instr.toCore] at h <;>
    (subst h; rfl)

/-- **The image of a valid 2.0 constant expression is a constant expression of `v20`.** -/
theorem constExpr_v20 {C : Context} {e : Silmaril.Wasm.V2.Expr}
    {t : Silmaril.Wasm.V2.ValType} (h : ExprOkConst C e t) {ce : Silmaril.Wasm.Expr}
    (hc : Silmaril.Wasm.V2.Expr.toCore e = some ce) : constExprB v20 ce = true := by
  obtain ⟨i, rfl, hi⟩ := exprOkConst_single h
  simp [constExprB, expr_inFeat _ hc, simpleConst_image hi hc]

end Silmaril.Proofs.Wasm.Models.V2Core
