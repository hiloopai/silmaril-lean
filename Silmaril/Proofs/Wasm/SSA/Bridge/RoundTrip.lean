module

public import Silmaril.Wasm.SSA.Bridge.Defs

/-! # Recognising lowered fragment trees gives them back -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Bridge

open Silmaril.Wasm (IntType Instr Idx)
open Silmaril.Wasm.Binaryen (BExpr)
open Silmaril.Wasm.SSA

theorem ofBlockType_toBlockType (ty : Option IntType) : ofBlockType? (toBlockType ty) = some ty := by
  cases ty <;> rfl

theorem ofInt_bits (v : WVal) : WVal.ofInt v.type v.bits = v := by cases v <;> rfl

/-- A constant lowers to `intConst` and takes no arguments. -/
private theorem ofInstr_const {v : WVal} {i : Instr} (h : (Op.const v).toInstr? = some i)
    {args : List Expr} (hl : args.length = (Op.const v).arity) :
    ofInstr? i args = some (.op (.const v) args) := by
  have hi : i = .intConst v.type v.bits := by
    simpa only [Op.toInstr?, Option.some.injEq] using h.symm
  have ha : args = [] := List.eq_nil_of_length_eq_zero (by simpa only [Op.arity] using hl)
  rw [hi, ha]
  simp [ofInstr?, ofInt_bits]

/-- An integer unary operator lowers only when it is valid at its type, and the
same validity check lets it be recognised again. -/
private theorem ofInstr_unInt {t : IntType} {op : Silmaril.Wasm.IntUnOp} {i : Instr} {a : Expr}
    (h : (Op.un (.int t op)).toInstr? = some i) :
    ofInstr? i [a] = some (.op (.un (.int t op)) [a]) := by
  by_cases hv : op.valid t = true
  · have hi : i = .intUnOp t op := by simpa [Op.toInstr?, hv] using h.symm
    rw [hi]
    simp [ofInstr?, hv]
  · simp [Op.toInstr?, hv] at h

theorem ofInstr_toInstr {o : Op} {i : Instr} (h : o.toInstr? = some i) {args : List Expr}
    (hl : args.length = o.arity) : ofInstr? i args = some (.op o args) := by
  cases o with
  | const v => exact ofInstr_const h hl
  | un u =>
    match args, hl with
    | [a], _ =>
      cases u with
      | int t op => exact ofInstr_unInt h
      | test t => cases h; rfl
      | wrap => cases h; rfl
      | extend s => cases h; rfl
  | bin b =>
    match args, hl with
    | [a, c], _ => cases b <;> (cases h; rfl)
  | select =>
    match args, hl with
    | [a, c, d], _ => cases h; rfl

theorem idx_toNat {k} {i : Nat} {x : Idx k} (h : Idx.ofNat? i = some x) : x.toNat = i :=
  ((Idx.ofNat?_eq_some_iff i x).1 h).symm

mutual
theorem ofBExpr_toBExpr : ∀ (e : Expr) {b : BExpr}, toBExpr? e = some b → ofBExpr? b = some e
  | .op o args, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, hg, i, hi, bs, hbs, rfl⟩ := h
    simp only [Option.guard_eq_some'] at hg
    simp [ofBExpr?, ofBExprs_toBExprs args hbs, ofInstr_toInstr hi hg]
  | .localGet i, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [ofBExpr?, ofBExprs?, ofInstr?, idx_toNat hx]
  | .localSet i e, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, b', hb, rfl⟩ := h
    simp [ofBExpr?, ofBExprs?, ofInstr?, idx_toNat hx, ofBExpr_toBExpr e hb]
  | .localTee i e, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, b', hb, rfl⟩ := h
    simp [ofBExpr?, ofBExprs?, ofInstr?, idx_toNat hx, ofBExpr_toBExpr e hb]
  | .drop e, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp [ofBExpr?, ofBExprs?, ofInstr?, ofBExpr_toBExpr e hb]
  | .nop, b, h => by
    simp only [toBExpr?, Option.some.injEq] at h; subst h; rfl
  | .unreachable, b, h => by
    simp only [toBExpr?, Option.some.injEq] at h; subst h; rfl
  | .block ty body, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨bs, hbs, rfl⟩ := h
    simp [ofBExpr?, ofBlockType_toBlockType, ofBExprs_toBExprs body hbs]
  | .loop ty body, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨bs, hbs, rfl⟩ := h
    simp [ofBExpr?, ofBlockType_toBlockType, ofBExprs_toBExprs body hbs]
  | .if_ ty c t e, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨bc, hc, bt, ht, be, he, rfl⟩ := h
    simp [ofBExpr?, ofBlockType_toBlockType, ofBExpr_toBExpr c hc, ofBExprs_toBExprs t ht,
      ofBExprs_toBExprs e he]
  | .br l args, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, hg, x, hx, bs, hbs, rfl⟩ := h
    simp only [Option.guard_eq_some'] at hg
    simp [ofBExpr?, ofBExprs_toBExprs args hbs, ofInstr?, idx_toNat hx, hg]
  | .brIf l args, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, hg, x, hx, bs, hbs, rfl⟩ := h
    simp only [Option.guard_eq_some'] at hg
    simp [ofBExpr?, ofBExprs_toBExprs args hbs, ofInstr?, idx_toNat hx, hg]
  | .return_ args, b, h => by
    simp only [toBExpr?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, hg, bs, hbs, rfl⟩ := h
    simp only [Option.guard_eq_some'] at hg
    simp [ofBExpr?, ofBExprs_toBExprs args hbs, ofInstr?, hg]
theorem ofBExprs_toBExprs : ∀ (es : List Expr) {bs : List BExpr},
    toBExprs? es = some bs → ofBExprs? bs = some es
  | [], bs, h => by simp only [toBExprs?, Option.some.injEq] at h; subst h; rfl
  | e :: es, bs, h => by
    simp only [toBExprs?, bind, pure] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    simp [ofBExprs?, ofBExpr_toBExpr e hb, ofBExprs_toBExprs es hbs]
end

theorem mapM_ofValType (ts : List IntType) :
    (ts.map fun t => Silmaril.Wasm.ValType.num (.int t)).mapM ofValType? = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ofValType?, ih]

theorem mapM_ofValType_comp (ts : List IntType) :
    ts.mapM (ofValType? ∘ fun t => Silmaril.Wasm.ValType.num (.int t)) = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ofValType?, ih]

theorem ofBFunc_toBFunc {ty : Silmaril.Wasm.TypeIdx} {f : FragFunc} {bf : Silmaril.Wasm.Binaryen.BFunc}
    (h : toBFunc? ty f = some bf) {ft : Silmaril.Wasm.FuncType}
    (hp : ft.params = f.params.map fun t => .num (.int t)) (hr : ft.results = resultTypes f.result) :
    ofBFunc? ft bf = some f := by
  simp only [toBFunc?, bind, pure] at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  obtain ⟨params, locals, result, body⟩ := f
  cases result <;>
    simp [ofBFunc?, hp, hr, resultTypes, mapM_ofValType_comp, ofBExprs_toBExprs _ hbs, ofValType?]

end Silmaril.Proofs.Wasm.SSA.Bridge
