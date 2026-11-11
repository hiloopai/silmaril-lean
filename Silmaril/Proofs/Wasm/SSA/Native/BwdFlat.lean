module

public import Silmaril.Proofs.Wasm.SSA.Native.BwdBasic

/-!
# Native adequacy, backward: flat instructions

One flat instruction applied to recognised, typed operands: an interpreter
step from the operands' values is a fragment step of the recognised
expression (`flat_step`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native.Bwd

open Silmaril.Wasm hiding Expr
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

/-- The fragment step after an operator's operands. -/
def StepOK {H : Type} (L : List Ar) (R : Ar) (n : Nat) (s : Store H) (mi : ModuleInst)
    (stk : List Val) (e : Expr) (o : Out (Option WVal)) (x : Store H × Frame × Flow) : Prop :=
  match o with
  | .ok ls₂ r => x = (s, frameOf mi ls₂, .normal (r.toList.map WVal.toVal ++ stk)) ∧
      tyE L R n e = some (some (arR r))
  | o => CorrA L R s mi o x

theorem args_nil_inv {ls ls₁ : List WVal} {P : List WVal} (h : Args ls [] (.ok ls₁ P)) :
    ls₁ = ls ∧ P = [] := by
  cases h; exact ⟨rfl, rfl⟩

theorem args_cons_inv {ls ls₂ : List WVal} {e : Expr} {es : List Expr} {P : List WVal}
    (h : Args ls (e :: es) (.ok ls₂ P)) :
    ∃ ls₁ w vs, Exec ls e (.ok ls₁ (some w)) ∧ Args ls₁ es (.ok ls₂ vs) ∧ P = w :: vs := by
  generalize ho : (Out.ok ls₂ P : Out (List WVal)) = o at h
  cases h with
  | cons he ha => cases ho; exact ⟨_, _, _, he, ha, rfl⟩
  | @head_abrupt _ _ _ out _ _ => cases out <;> simp [Out.cast] at ho
  | tail_abrupt _ _ hab => subst ho; exact absurd hab id

theorem args_one_inv {ls ls₁ : List WVal} {a : Expr} {P : List WVal} (h : Args ls [a] (.ok ls₁ P)) :
    ∃ w, Exec ls a (.ok ls₁ (some w)) ∧ P = [w] := by
  obtain ⟨_, w, vs, he, hr, rfl⟩ := args_cons_inv h
  obtain ⟨rfl, rfl⟩ := args_nil_inv hr
  exact ⟨w, he, rfl⟩

theorem args_two_inv {ls ls₂ : List WVal} {a b : Expr} {P : List WVal}
    (h : Args ls [a, b] (.ok ls₂ P)) :
    ∃ ls₁ wa wb, Exec ls a (.ok ls₁ (some wa)) ∧ Exec ls₁ b (.ok ls₂ (some wb)) ∧ P = [wa, wb] := by
  obtain ⟨ls₁, wa, vs, he, hr, rfl⟩ := args_cons_inv h
  obtain ⟨wb, he', rfl⟩ := args_one_inv hr
  exact ⟨ls₁, wa, wb, he, he', rfl⟩

theorem args_three_inv {ls ls₃ : List WVal} {a b c : Expr} {P : List WVal}
    (h : Args ls [a, b, c] (.ok ls₃ P)) :
    ∃ wa wb wc, P = [wa, wb, wc] := by
  obtain ⟨_, wa, vs, -, hr, rfl⟩ := args_cons_inv h
  obtain ⟨_, wb, wc, -, -, rfl⟩ := args_two_inv hr
  exact ⟨wa, wb, wc, rfl⟩

theorem len_le_one {P : List WVal} (h : P.length ≤ 1) : P = [] ∨ ∃ a, P = [a] := by
  match P, h with
  | [], _ => exact .inl rfl
  | [a], _ => exact .inr ⟨a, rfl⟩

theorem args_len {ls ls₁ : List WVal} {as : List Expr} {P : List WVal}
    (h : Args ls as (.ok ls₁ P)) : P.length = as.length := by
  induction as generalizing ls P with
  | nil => obtain ⟨-, rfl⟩ := args_nil_inv h; rfl
  | cons a as ih =>
      obtain ⟨_, w, vs, -, hr, rfl⟩ := args_cons_inv h
      simp [ih hr]

theorem stk1 {w : WVal} {stk : List Val} :
    ([w].map WVal.toVal).reverse ++ stk = WVal.toVal w :: stk := rfl

theorem stk2 {a b : WVal} {stk : List Val} :
    ([a, b].map WVal.toVal).reverse ++ stk = WVal.toVal b :: WVal.toVal a :: stk := rfl

theorem stk3 {a b c : WVal} {stk : List Val} :
    ([a, b, c].map WVal.toVal).reverse ++ stk =
      WVal.toVal c :: WVal.toVal b :: WVal.toVal a :: stk := rfl

theorem tyE_br {L : List Ar} {R : Ar} {n l : Nat} {as : List Expr} {x : Option Ar}
    (h : tyE L R n (.br l as) = some x) :
    tyArgs L R n as = true ∧ L[l]? = some (if as.length = 1 then .one else .none) ∧ as.length ≤ 1 := by
  rw [tyE] at h
  by_cases hc : (tyArgs L R n as && L[l]? == some (if as.length == 1 then .one else .none) &&
      decide (as.length ≤ 1)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    refine ⟨hc.1.1, ?_, hc.2⟩
    rw [hc.1.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h
theorem tyE_brIf {L : List Ar} {R : Ar} {n l : Nat} {as : List Expr} {x : Option Ar}
    (h : tyE L R n (.brIf l as) = some x) :
    tyArgs L R n as = true ∧ (as.length = 1 ∨ as.length = 2) ∧
      L[l]? = some (if as.length = 2 then .one else .none) ∧
      x = some (if as.length = 2 then .one else .none) := by
  rw [tyE] at h
  by_cases hc : (tyArgs L R n as && (as.length == 1 || as.length == 2) &&
      L[l]? == some (if as.length == 2 then .one else .none)) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
    refine ⟨hc.1.1, hc.1.2, ?_, ?_⟩
    · rw [hc.2]
    · cases h; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h
theorem tyE_return {L : List Ar} {R : Ar} {n : Nat} {as : List Expr} {x : Option Ar}
    (h : tyE L R n (.return_ as) = some x) :
    tyArgs L R n as = true ∧ as.length ≤ 1 ∧ R = (if as.length = 1 then .one else .none) := by
  rw [tyE] at h
  by_cases hc : (tyArgs L R n as && decide (as.length ≤ 1) &&
      R == (if as.length == 1 then .one else .none)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    refine ⟨hc.1.1, hc.1.2, ?_⟩
    rw [hc.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h


section FlatCases

variable {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s : Store H} {mi : ModuleInst}
  {e : Expr} {x : Option Ar} {ls ls₁ : List WVal} {P : List WVal} {stk : List Val}
  {r : Store H × Frame × Flow}

private theorem flat_intConst {t : IntType} {b : BitVec t.width}
    (hr : some (Expr.op (.const (.ofInt t b)) []) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.intConst t b) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨rfl, rfl⟩ := args_nil_inv hargs
  simp only [evalFlat, List.map_nil, List.reverse_nil, List.nil_append, Option.some.injEq] at hflat
  subst hflat
  refine ⟨.ok ls₁ (some (WVal.ofInt t b)), .op hargs rfl, by simp [ofInt_toVal], ?_⟩
  simp only [tyE] at hty ⊢; split at hty <;> simp_all

private theorem flat_localGet {xi : LocalIdx}
    (hr : some (Expr.localGet xi.toNat) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.localGet xi) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨rfl, rfl⟩ := args_nil_inv hargs
  simp only [evalFlat, List.map_nil, List.reverse_nil, List.nil_append, frameOf_local,
    Option.map_map, Option.map_eq_some_iff] at hflat
  obtain ⟨w, hw, rfl⟩ := hflat
  exact ⟨.ok ls₁ (some w), .localGet hw, rfl,
    by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

private theorem flat_localSet {xi : LocalIdx} {a : Expr}
    (hr : some (Expr.localSet xi.toNat a) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.localSet xi) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨w, he, rfl⟩ := args_one_inv hargs
  simp only [stk1, evalFlat, Option.some.injEq, frameOf_setLocal] at hflat
  subst hflat
  exact ⟨_, .localSet he, rfl, by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

private theorem flat_localTee {xi : LocalIdx} {a : Expr}
    (hr : some (Expr.localTee xi.toNat a) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.localTee xi) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨w, he, rfl⟩ := args_one_inv hargs
  simp only [stk1, evalFlat, Option.some.injEq, frameOf_setLocal] at hflat
  subst hflat
  exact ⟨_, .localTee he, rfl, by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

private theorem flat_intUnOp {t : IntType} {op : IntUnOp} {a : Expr}
    (hr : (if op.valid t then some (Expr.op (.un (.int t op)) [a]) else none) = some e)
    (hty : tyE L R n e = some x) (hargs : Args ls [a] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.intUnOp t op) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  have he : Expr.op (.un (.int t op)) [a] = e := by
    split at hr
    · exact Option.some.inj hr
    · cases hr
  cases he
  obtain ⟨w, he, rfl⟩ := args_one_inv hargs
  simp only [stk1, evalFlat, asInt_toVal, Option.map_eq_some_iff] at hflat
  obtain ⟨v, hv, rfl⟩ := hflat
  exact ⟨.ok ls₁ (some (WVal.ofInt t (Numerics.intUnOp t op v))),
    .op hargs (by simp [Op.eval, UnOp.eval, hv]), by simp [ofInt_toVal],
    by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

private theorem flat_intTestOp {t : IntType} {a : Expr}
    (hr : some (Expr.op (.un (.test t)) [a]) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk)
      (.intTestOp t .eqz) = some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨w, he, rfl⟩ := args_one_inv hargs
  simp only [stk1, evalFlat, asInt_toVal, Option.map_eq_some_iff] at hflat
  obtain ⟨v, hv, rfl⟩ := hflat
  exact ⟨.ok ls₁ (some (.i32 (Numerics.intTestOp t .eqz v))),
    .op hargs (by simp [Op.eval, UnOp.eval, hv]), by simp; rfl,
    by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

/-- `wrap` and `extend` are recognised but rejected by the native check. -/
private theorem flat_convert {u : UnOp} {a : Expr} (hu : u = .wrap ∨ ∃ sg, u = .extend sg)
    (hr : some (Expr.op (.un u) [a]) = some e) (hty : tyE L R n e = some x) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  rcases hu with rfl | ⟨sg, rfl⟩ <;> simp [tyE, Op.native] at hty

private theorem flat_intBinOp {t : IntType} {op : IntBinOp} {a b : Expr}
    (hr : some (Expr.op (.bin (.int t op)) [a, b]) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a, b] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.intBinOp t op) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨ls₁', wa, wb, -, -, rfl⟩ := args_two_inv hargs
  simp only [stk2, evalFlat, asInt_toVal] at hflat
  cases ha : WVal.asInt t wa with
  | none => simp [ha] at hflat
  | some xa =>
    cases hb : WVal.asInt t wb with
    | none => simp [ha, hb] at hflat
    | some xb =>
      simp only [ha, hb, bind, Option.bind] at hflat
      split at hflat
      · rename_i z hz
        cases hflat
        exact ⟨.ok ls₁ (some (WVal.ofInt t z)),
          .op hargs (by simp [Op.eval, BinOp.eval, ha, hb, hz]), by simp [ofInt_toVal],
          by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩
      · rename_i _ hz
        cases hflat
        exact ⟨_, .op_trap hargs (by simp [Op.eval, BinOp.eval, ha, hb, hz]), _, rfl⟩

private theorem flat_intRelOp {t : IntType} {op : IntRelOp} {a b : Expr}
    (hr : some (Expr.op (.bin (.rel t op)) [a, b]) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a, b] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.intRelOp t op) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨ls₁', wa, wb, -, -, rfl⟩ := args_two_inv hargs
  simp only [stk2, evalFlat, asInt_toVal] at hflat
  cases ha : WVal.asInt t wa with
  | none => simp [ha] at hflat
  | some xa =>
    cases hb : WVal.asInt t wb with
    | none => simp [ha, hb] at hflat
    | some xb =>
      simp only [ha, hb, bind, Option.bind, Option.some.injEq] at hflat
      subst hflat
      exact ⟨.ok ls₁ (some (.i32 (Numerics.intRelOp t op xa xb))),
        .op hargs (by simp [Op.eval, BinOp.eval, ha, hb]), by simp; rfl,
        by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

/-- Both recognised `select` forms; the interpreter ignores the annotation. -/
private theorem flat_select {sel : Option (List ValType)} {a b c : Expr}
    (hr : some (Expr.op .select [a, b, c]) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a, b, c] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.select sel) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨wa, wb, wc, rfl⟩ := args_three_inv hargs
  simp only [stk3, evalFlat, truthy_toVal, Option.map_eq_some_iff] at hflat
  obtain ⟨tb, htb, rfl⟩ := hflat
  refine ⟨.ok ls₁ (some (if tb then wa else wb)),
    .op hargs (by simp [Op.eval, htb]), ?_, by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩
  cases tb <;> rfl

private theorem flat_drop {a : Expr}
    (hr : some (Expr.drop a) = some e) (hty : tyE L R n e = some x)
    (hargs : Args ls [a] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) .drop = some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨w, he, rfl⟩ := args_one_inv hargs
  simp only [stk1, evalFlat, Option.some.injEq] at hflat
  subst hflat
  exact ⟨_, .drop he, rfl, by simp only [tyE] at hty ⊢; split at hty <;> simp_all⟩

private theorem flat_nop (hr : some Expr.nop = some e) (hargs : Args ls [] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) .nop = some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  obtain ⟨hls, hP⟩ : ls₁ = ls ∧ P = [] := args_nil_inv hargs
  have hr : r = (s, frameOf mi ls, .normal stk) := by
    simpa only [hls, hP, evalFlat, List.map_nil, List.reverse_nil, List.nil_append,
      Option.some.injEq, eq_comm] using hflat
  exact ⟨_, .nop, hr, rfl⟩

private theorem flat_unreachable (hr : some Expr.unreachable = some e)
    (hargs : Args ls [] (.ok ls₁ P))
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) .unreachable =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  cases hr
  have hls : ls₁ = ls := (args_nil_inv hargs).1
  have hr : r = (s, frameOf mi ls, .trap) := by
    simpa only [hls, evalFlat, Option.some.injEq, eq_comm] using hflat
  exact ⟨_, .unreachable, _, hr⟩

/-- The arity of at most one operand value. -/
private theorem arR_head {as : List Expr} (hlen : P.length = as.length) (hle : as.length ≤ 1) :
    (if as.length = 1 then Ar.one else .none) = arR P.head? := by
  rcases len_le_one (by omega : P.length ≤ 1) with rfl | ⟨w, rfl⟩
  · have h0 : as.length = 0 := by simpa using hlen.symm
    simp [h0, arR]
  · have h1 : as.length = 1 := by simpa using hlen.symm
    simp [h1, arR]

private theorem flat_br {lab : LabelIdx} {as : List Expr}
    (hr : (if as.length ≤ 1 then some (Expr.br lab.toNat as) else none) = some e)
    (hty : tyE L R n e = some x) (hargs : Args ls as (.ok ls₁ P))
    (hlen : P.length = as.length)
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.br lab) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  have he : Expr.br lab.toNat as = e := by
    split at hr
    · exact Option.some.inj hr
    · cases hr
  cases he
  have hr : r = (s, frameOf mi ls₁, .brk lab.toNat ((P.map WVal.toVal).reverse ++ stk)) := by
    simpa only [evalFlat, Option.some.injEq, eq_comm] using hflat
  obtain ⟨-, hlab, hle⟩ := tyE_br hty
  refine ⟨_, .br hargs, stk, ?_, ?_⟩
  · rw [hr]
    rcases len_le_one (by omega : P.length ≤ 1) with rfl | ⟨w, rfl⟩ <;> simp
  · rw [hlab, arR_head hlen hle]

private theorem flat_brIf_one {lab : LabelIdx} {as : List Expr} {wc : WVal}
    (hargs : Args ls as (.ok ls₁ [wc])) (h1 : as.length = 1)
    (hlab : L[lab.toNat]? = some (if as.length = 2 then .one else .none))
    (hty : tyE L R n (.brIf lab.toNat as) = some (some (if as.length = 2 then .one else .none)))
    (hflat : evalFlat s (frameOf mi ls₁) (([wc].map WVal.toVal).reverse ++ stk) (.brIf lab) =
      some r) :
    ∃ o, Exec ls (.brIf lab.toNat as) o ∧ StepOK L R n s mi stk (.brIf lab.toNat as) o r := by
  simp only [stk1, evalFlat, truthy_toVal, Option.map_eq_some_iff] at hflat
  obtain ⟨b, hb, rfl⟩ := hflat
  refine ⟨_, .brIf hargs rfl hb, ?_⟩
  cases b
  · refine ⟨by simp, ?_⟩
    rw [hty, h1]; rfl
  · refine ⟨stk, by simp, ?_⟩
    rw [hlab, h1]; rfl

private theorem flat_brIf_two {lab : LabelIdx} {as : List Expr} {wv wc : WVal}
    (hargs : Args ls as (.ok ls₁ [wv, wc])) (h2 : as.length = 2)
    (hlab : L[lab.toNat]? = some (if as.length = 2 then .one else .none))
    (hty : tyE L R n (.brIf lab.toNat as) = some (some (if as.length = 2 then .one else .none)))
    (hflat : evalFlat s (frameOf mi ls₁) (([wv, wc].map WVal.toVal).reverse ++ stk) (.brIf lab) =
      some r) :
    ∃ o, Exec ls (.brIf lab.toNat as) o ∧ StepOK L R n s mi stk (.brIf lab.toNat as) o r := by
  simp only [stk2, evalFlat, truthy_toVal, Option.map_eq_some_iff] at hflat
  obtain ⟨b, hb, rfl⟩ := hflat
  refine ⟨_, .brIf hargs rfl hb, ?_⟩
  cases b
  · refine ⟨by simp, ?_⟩
    rw [hty, h2]; rfl
  · refine ⟨WVal.toVal wv :: stk |>.drop 1, by simp, ?_⟩
    rw [hlab, h2]; rfl

private theorem flat_brIf {lab : LabelIdx} {as : List Expr}
    (hr : (if 1 ≤ as.length ∧ as.length ≤ 2 then some (Expr.brIf lab.toNat as) else none) =
      some e)
    (hty : tyE L R n e = some x) (hargs : Args ls as (.ok ls₁ P))
    (hlen : P.length = as.length)
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) (.brIf lab) =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  have he : Expr.brIf lab.toNat as = e := by
    split at hr
    · exact Option.some.inj hr
    · cases hr
  cases he
  obtain ⟨-, hlen12, hlab, hx⟩ := tyE_brIf hty
  rcases hlen12 with h1 | h2
  · obtain ⟨wc, rfl⟩ : ∃ wc, P = [wc] := List.length_eq_one_iff.mp (hlen.trans h1)
    exact flat_brIf_one hargs h1 hlab (hty.trans (congrArg some hx)) hflat
  · obtain ⟨wv, wc, rfl⟩ : ∃ wv wc, P = [wv, wc] := List.length_eq_two.mp (hlen.trans h2)
    exact flat_brIf_two hargs h2 hlab (hty.trans (congrArg some hx)) hflat

private theorem flat_return {as : List Expr}
    (hr : (if as.length ≤ 1 then some (Expr.return_ as) else none) = some e)
    (hty : tyE L R n e = some x) (hargs : Args ls as (.ok ls₁ P))
    (hlen : P.length = as.length)
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) .return_ =
      some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  have he : Expr.return_ as = e := by
    split at hr
    · exact Option.some.inj hr
    · cases hr
  cases he
  have hr : r = (s, frameOf mi ls₁, .ret ((P.map WVal.toVal).reverse ++ stk)) := by
    simpa only [evalFlat, Option.some.injEq, eq_comm] using hflat
  obtain ⟨-, hle, hR⟩ := tyE_return hty
  refine ⟨_, .return_ hargs, frameOf mi ls₁, stk, ?_, ?_⟩
  · rw [hr]
    rcases len_le_one (by omega : P.length ≤ 1) with rfl | ⟨w, rfl⟩ <;> simp
  · rw [hR, arR_head hlen hle]

end FlatCases

/-- One recognised flat instruction after its operands. -/
theorem flat_step {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s : Store H} {mi : ModuleInst}
    {i : Instr} {as : List Expr} {e : Expr} (hr : ofInstr? i as = some e)
    {x : Option Ar} (hty : tyE L R n e = some x)
    {ls ls₁ : List WVal} {P : List WVal} (hargs : Args ls as (.ok ls₁ P))
    {stk : List Val} {r : Store H × Frame × Flow}
    (hflat : evalFlat s (frameOf mi ls₁) ((P.map WVal.toVal).reverse ++ stk) i = some r) :
    ∃ o, Exec ls e o ∧ StepOK L R n s mi stk e o r := by
  have hlen : P.length = as.length := args_len hargs
  revert hr
  unfold ofInstr?
  split
  · exact (flat_intConst · hty hargs hflat)
  · exact (flat_localGet · hty hargs hflat)
  · exact (flat_localSet · hty hargs hflat)
  · exact (flat_localTee · hty hargs hflat)
  · exact (flat_intUnOp · hty hargs hflat)
  · exact (flat_intTestOp · hty hargs hflat)
  · exact (flat_convert (.inl rfl) · hty)
  · exact (flat_convert (.inr ⟨_, rfl⟩) · hty)
  · exact (flat_intBinOp · hty hargs hflat)
  · exact (flat_intRelOp · hty hargs hflat)
  · exact (flat_select · hty hargs hflat)
  · exact (flat_select · hty hargs hflat)
  · exact (flat_drop · hty hargs hflat)
  · exact (flat_nop · hargs hflat)
  · exact (flat_unreachable · hargs hflat)
  · exact (flat_br · hty hargs hlen hflat)
  · exact (flat_brIf · hty hargs hlen hflat)
  · exact (flat_return · hty hargs hlen hflat)
  · exact nofun

end Silmaril.Proofs.Wasm.SSA.Native.Bwd
