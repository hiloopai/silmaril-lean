module

public import Silmaril.Wasm.SSA.Native.Defs

/-!
# Native adequacy, forward direction: basics

Values and conditions agree between `WVal` and silmaril's Core values;
inversions of the recogniser `ofBExpr?`/`ofInstr?`; the flat instruction of a
recognised operator computes `Op.eval` on the stack.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType Catch)
open Silmaril.Wasm.Binaryen (BExpr)
open Silmaril.Wasm.Execution.Core (Val)
open Silmaril.Wasm.SSA

/-! ## Values -/

theorem asInt_toVal (t : IntType) (v : WVal) : Silmaril.Wasm.Binaryen.asInt t v.toVal = v.asInt t := by
  cases t <;> cases v <;> rfl

theorem ofInt_toVal (t : IntType) (x : BitVec t.width) : Silmaril.Wasm.Binaryen.ofInt t x = (WVal.ofInt t x).toVal := by
  cases t <;> rfl

theorem truthy_toVal (v : WVal) : Silmaril.Wasm.Binaryen.truthy v.toVal = v.truthy := by
  cases v <;> rfl

theorem ofVal?_toVal (v : WVal) : WVal.ofVal? v.toVal = some v := by
  cases v <;> rfl

/-! ## The recogniser -/

theorem ofBExprs?_nil {bs : List BExpr} (h : ofBExprs? bs = some []) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      simp only [ofBExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, h⟩ := h
      cases h

theorem ofBExprs?_cons {bs : List BExpr} {e : Expr} {es : List Expr}
    (h : ofBExprs? bs = some (e :: es)) :
    ∃ b bs', bs = b :: bs' ∧ ofBExpr? b = some e ∧ ofBExprs? bs' = some es := by
  cases bs with
  | nil => simp [ofBExprs?] at h
  | cons b bs =>
      simp only [ofBExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', h₁, es', h₂, h⟩ := h
      cases h
      exact ⟨b, bs, rfl, h₁, h₂⟩

/-- The `if` case of `ofBExpr?_inv`: a recognised `if` has exactly one condition. -/
private theorem ofBExpr?_if_inv {bt : BlockType} {c tb eb : List BExpr} {e : Expr}
    (h : ofBExpr? (.if_ bt c tb eb) = some e) :
    ∃ cb ty c' t el, c = [cb] ∧ ofBlockType? bt = some ty ∧
      ofBExpr? cb = some c' ∧ ofBExprs? tb = some t ∧ ofBExprs? eb = some el ∧
      e = .if_ ty c' t el := by
  match c, h with
  | [cb], h =>
      obtain ⟨ty, h₁, c', h₂, t', h₃, e', h₄, he⟩ : ∃ ty, ofBlockType? bt = some ty ∧
          ∃ c', ofBExpr? cb = some c' ∧ ∃ t', ofBExprs? tb = some t' ∧
          ∃ e', ofBExprs? eb = some e' ∧ Expr.if_ ty c' t' e' = e := by
        simpa only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] using h
      exact ⟨cb, ty, c', t', e', rfl, h₁, h₂, h₃, h₄, he.symm⟩
  | [], h => nomatch h
  | _ :: _ :: _, h => nomatch h

/-- The shapes of recognised trees. -/
theorem ofBExpr?_inv {b : BExpr} {e : Expr} (h : ofBExpr? b = some e) :
    (∃ i bargs args, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ ofInstr? i args = some e) ∨
    (∃ bt body ty body', b = .block bt body ∧ ofBlockType? bt = some ty ∧
      ofBExprs? body = some body' ∧ e = .block ty body') ∨
    (∃ bt body ty body', b = .loop bt body ∧ ofBlockType? bt = some ty ∧
      ofBExprs? body = some body' ∧ e = .loop ty body') ∨
    (∃ bt cb tb eb ty c t el, b = .if_ bt [cb] tb eb ∧ ofBlockType? bt = some ty ∧
      ofBExpr? cb = some c ∧ ofBExprs? tb = some t ∧ ofBExprs? eb = some el ∧
      e = .if_ ty c t el) := by
  cases b with
  | op i bargs =>
      obtain ⟨args, h₁, h₂⟩ : ∃ args, ofBExprs? bargs = some args ∧ ofInstr? i args = some e := by
        simpa only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] using h
      exact .inl ⟨i, bargs, args, rfl, h₁, h₂⟩
  | block bt body =>
      obtain ⟨ty, h₁, body', h₂, he⟩ : ∃ ty, ofBlockType? bt = some ty ∧
          ∃ body', ofBExprs? body = some body' ∧ Expr.block ty body' = e := by
        simpa only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] using h
      exact .inr (.inl ⟨bt, body, ty, body', rfl, h₁, h₂, he.symm⟩)
  | loop bt body =>
      obtain ⟨ty, h₁, body', h₂, he⟩ : ∃ ty, ofBlockType? bt = some ty ∧
          ∃ body', ofBExprs? body = some body' ∧ Expr.loop ty body' = e := by
        simpa only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] using h
      exact .inr (.inr (.inl ⟨bt, body, ty, body', rfl, h₁, h₂, he.symm⟩))
  | if_ bt c tb eb =>
      obtain ⟨cb, ty, c', t, el, hc, h₁, h₂, h₃, h₄, he⟩ := ofBExpr?_if_inv h
      exact .inr (.inr (.inr ⟨bt, cb, tb, eb, ty, c', t, el, by rw [hc], h₁, h₂, h₃, h₄, he⟩))
  | tryTable => nomatch h

theorem ofInstr?_not_block {i : Instr} {args : List Expr} {ty : Option IntType} {body : List Expr}
    (h : ofInstr? i args = some (.block ty body)) : False := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h

theorem ofInstr?_not_loop {i : Instr} {args : List Expr} {ty : Option IntType} {body : List Expr}
    (h : ofInstr? i args = some (.loop ty body)) : False := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h

theorem ofInstr?_not_if {i : Instr} {args : List Expr} {ty : Option IntType} {c : Expr}
    {t e : List Expr} (h : ofInstr? i args = some (.if_ ty c t e)) : False := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h

theorem ofBExpr?_block {b : BExpr} {ty : Option IntType} {body : List Expr}
    (h : ofBExpr? b = some (.block ty body)) :
    ∃ bt bbody, b = .block bt bbody ∧ ofBlockType? bt = some ty ∧ ofBExprs? bbody = some body := by
  rcases ofBExpr?_inv h with h' | h' | h' | h'
  · obtain ⟨_, _, _, _, _, h'⟩ := h'; exact (ofInstr?_not_block h').elim
  · obtain ⟨bt, bb, ty', b', rfl, h₁, h₂, he⟩ := h'
    cases he; exact ⟨bt, bb, rfl, h₁, h₂⟩
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; cases he
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := h'; cases he

theorem ofBExpr?_loop {b : BExpr} {ty : Option IntType} {body : List Expr}
    (h : ofBExpr? b = some (.loop ty body)) :
    ∃ bt bbody, b = .loop bt bbody ∧ ofBlockType? bt = some ty ∧ ofBExprs? bbody = some body := by
  rcases ofBExpr?_inv h with h' | h' | h' | h'
  · obtain ⟨_, _, _, _, _, h'⟩ := h'; exact (ofInstr?_not_loop h').elim
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; cases he
  · obtain ⟨bt, bb, ty', b', rfl, h₁, h₂, he⟩ := h'
    cases he; exact ⟨bt, bb, rfl, h₁, h₂⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := h'; cases he

theorem ofBExpr?_if {b : BExpr} {ty : Option IntType} {c : Expr} {t el : List Expr}
    (h : ofBExpr? b = some (.if_ ty c t el)) :
    ∃ bt cb tb eb, b = .if_ bt [cb] tb eb ∧ ofBlockType? bt = some ty ∧ ofBExpr? cb = some c ∧
      ofBExprs? tb = some t ∧ ofBExprs? eb = some el := by
  rcases ofBExpr?_inv h with h' | h' | h' | h'
  · obtain ⟨_, _, _, _, _, h'⟩ := h'; exact (ofInstr?_not_if h').elim
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; cases he
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; cases he
  · obtain ⟨bt, cb, tb, eb, _, _, _, _, rfl, h₁, h₂, h₃, h₄, he⟩ := h'
    cases he; exact ⟨bt, cb, tb, eb, rfl, h₁, h₂, h₃, h₄⟩

/-- A recognised non-structured expression comes from a flat instruction. -/
theorem ofBExpr?_flat {b : BExpr} {e : Expr} (h : ofBExpr? b = some e)
    (hs : ∀ ty body, e ≠ .block ty body) (hl : ∀ ty body, e ≠ .loop ty body)
    (hi : ∀ ty c t el, e ≠ .if_ ty c t el) :
    ∃ i bargs args, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ ofInstr? i args = some e := by
  rcases ofBExpr?_inv h with h' | h' | h' | h'
  · exact h'
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; exact (hs _ _ he).elim
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := h'; exact (hl _ _ he).elim
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := h'; exact (hi _ _ _ _ he).elim

/-! ## Flat instructions -/

theorem ofInstr?_localGet {i : Instr} {args : List Expr} {j : Nat}
    (h : ofInstr? i args = some (.localGet j)) : ∃ x, i = .localGet x ∧ args = [] ∧ j = x.toNat := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  rename_i x; exact ⟨x, rfl, rfl, h.symm⟩

theorem ofInstr?_localSet {i : Instr} {args : List Expr} {j : Nat} {e : Expr}
    (h : ofInstr? i args = some (.localSet j e)) :
    ∃ x, i = .localSet x ∧ args = [e] ∧ j = x.toNat := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, rfl⟩

theorem ofInstr?_localTee {i : Instr} {args : List Expr} {j : Nat} {e : Expr}
    (h : ofInstr? i args = some (.localTee j e)) :
    ∃ x, i = .localTee x ∧ args = [e] ∧ j = x.toNat := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, rfl⟩

theorem ofInstr?_drop {i : Instr} {args : List Expr} {e : Expr}
    (h : ofInstr? i args = some (.drop e)) : i = .drop ∧ args = [e] := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  subst h; exact ⟨rfl, rfl⟩

theorem ofInstr?_nop {i : Instr} {args : List Expr} (h : ofInstr? i args = some .nop) :
    i = .nop ∧ args = [] := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  exact ⟨rfl, rfl⟩

theorem ofInstr?_unreachable {i : Instr} {args : List Expr}
    (h : ofInstr? i args = some .unreachable) : i = .unreachable ∧ args = [] := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  exact ⟨rfl, rfl⟩

theorem ofInstr?_br {i : Instr} {args args' : List Expr} {l : Nat}
    (h : ofInstr? i args = some (.br l args')) : ∃ x, i = .br x ∧ args' = args ∧ l = x.toNat := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, rfl⟩

theorem ofInstr?_brIf {i : Instr} {args args' : List Expr} {l : Nat}
    (h : ofInstr? i args = some (.brIf l args')) : ∃ x, i = .brIf x ∧ args' = args ∧ l = x.toNat := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl, rfl⟩

theorem ofInstr?_return {i : Instr} {args args' : List Expr}
    (h : ofInstr? i args = some (.return_ args')) : i = .return_ ∧ args' = args := by
  unfold ofInstr? at h; split at h <;> (try split at h) <;> simp at h
  subst h; exact ⟨rfl, rfl⟩

end Silmaril.Proofs.Wasm.SSA.Native
