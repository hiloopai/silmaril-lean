module

public import Silmaril.Proofs.Wasm.SSA.Native.BwdFlat

/-!
# Native adequacy, backward: structured constructs

Inverting `Corr`, and the outcomes of a typed block, `if` arm or loop body.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native.Bwd

open Silmaril.Wasm hiding Expr
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

theorem corr_flow {H : Type} {L : List Ar} {R : Ar} {s s' : Store H} {mi : ModuleInst}
    {stk : List Val} {o : Out (List WVal)} {f' : Frame} {fl : Flow}
    (h : Corr L R s mi stk o (s', f', fl)) :
    (∃ ls' P, o = .ok ls' P ∧ s' = s ∧ f' = frameOf mi ls' ∧
      fl = .normal ((P.map WVal.toVal).reverse ++ stk)) ∨
    (∃ l ls' r junk, o = .brk l ls' r ∧ s' = s ∧ f' = frameOf mi ls' ∧
      fl = .brk l (r.toList.map WVal.toVal ++ junk) ∧ L[l]? = some (arR r)) ∨
    (∃ r junk, o = .ret r ∧ s' = s ∧ fl = .ret (r.toList.map WVal.toVal ++ junk) ∧ R = arR r) ∨
    (o = .trap ∧ s' = s ∧ fl = .trap) := by
  cases o with
  | ok ls P =>
      simp only [Corr, Prod.mk.injEq] at h
      exact .inl ⟨ls, P, rfl, h.1, h.2.1, h.2.2⟩
  | brk l ls r =>
      obtain ⟨junk, hx, hl⟩ := h
      simp only [Prod.mk.injEq] at hx
      exact .inr (.inl ⟨l, ls, r, junk, rfl, hx.1, hx.2.1, hx.2.2, hl⟩)
  | ret r =>
      obtain ⟨fr, junk, hx, hR⟩ := h
      simp only [Prod.mk.injEq] at hx
      exact .inr (.inr (.inl ⟨r, junk, rfl, hx.1, hx.2.2, hR⟩))
  | trap =>
      obtain ⟨fr, hx⟩ := h
      simp only [Prod.mk.injEq] at hx
      exact .inr (.inr (.inr ⟨rfl, hx.1, hx.2.2⟩))

theorem arFits_some {a : Ar} {b : Option (Option Ar)} (h : arFits a b = true) :
    ∃ c, b = some c := by
  match b, h with
  | some c, _ => exact ⟨c, rfl⟩

theorem arFits_eq {a b : Ar} (h : arFits a (some (some b)) = true) : a = b := by
  simpa [arFits] using h

theorem take_toList {ty : Option IntType} {r : Option WVal} (hok : BlockOk ty r)
    (hfit : arR r = arOf ty ∨ ty = none) (junk : List Val) :
    (r.toList.map WVal.toVal ++ junk).take (if ty.isSome then 1 else 0) =
      (blockRes ty r).toList.map WVal.toVal := by
  cases ty with
  | none => simp [blockRes]
  | some t =>
      obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hok rfl)
      simp [blockRes]

theorem arR_blockRes {ty : Option IntType} {r : Option WVal} (hok : BlockOk ty r) :
    arR (blockRes ty r) = arOf ty := by
  cases ty with
  | none => simp [blockRes, arOf]
  | some t =>
      obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hok rfl)
      simp [blockRes, arOf]

theorem blockOk_of {ty : Option IntType} {r : Option WVal} (h : arR r = arOf ty) : BlockOk ty r := by
  intro hs
  cases ty with
  | none => simp at hs
  | some t => cases r <;> simp_all [arR, arOf]

/-- A typed block body that completes: its values fit the block type. -/
private theorem blk_vals_ok {ty : Option IntType} {a : Option Ar} {ls₁ P : List WVal}
    (hfit : arFits (arOf ty) (some a) = true)
    (hP : ∃ b, a = some b ∧ (P = [] ∧ b = .none ∨ ∃ w, P = [w] ∧ b = .one)) :
    ∃ r, BlockExit ty (toOpt (.ok ls₁ P)) (.ok ls₁ (blockRes ty r)) ∧ BlockOk ty r ∧
      ((P.map WVal.toVal).reverse ++ []).take (if ty.isSome then 1 else 0) =
        (blockRes ty r).toList.map WVal.toVal := by
  obtain ⟨b, rfl, hb⟩ := hP
  have hab : arOf ty = b := arFits_eq hfit
  rcases hb with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩
  · have hok : BlockOk ty none := blockOk_of (by simpa [arR] using hab.symm)
    exact ⟨none, .ok hok, hok, by simp [blockRes]⟩
  · have hok : BlockOk ty (some w) := blockOk_of (by simpa [arR] using hab.symm)
    refine ⟨some w, .ok hok, hok, ?_⟩
    simpa using take_toList hok (.inl (by simpa [arR] using hab.symm)) []

/-- A typed block body that completes or branches to its own label. -/
theorem blk_vals {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s s₁ : Store H} {mi : ModuleInst}
    {ty : Option IntType} {ls : List WVal} {body : List Expr} {ob : Out (List WVal)} {f₁ : Frame}
    {fl : Flow} {vs : List Val} {a : Option Ar}
    (hT : ExecT (arOf ty :: L) R n ls body ob) (hty : tySeq (arOf ty :: L) R n body = some a)
    (hfit : arFits (arOf ty) (some a) = true)
    (hc : Corr (arOf ty :: L) R s mi [] ob (s₁, f₁, fl)) (hvs : fl.blockVals = some vs) :
    ∃ ls₁ r, Seq ls none body (toOpt ob) ∧ BlockExit ty (toOpt ob) (.ok ls₁ (blockRes ty r)) ∧
      BlockOk ty r ∧ s₁ = s ∧ f₁ = frameOf mi ls₁ ∧
      vs.take (if ty.isSome then 1 else 0) = (blockRes ty r).toList.map WVal.toVal := by
  obtain ⟨hseq, hP⟩ := execT_seq hty hT
  rcases corr_flow hc with ⟨ls₁, P, rfl, rfl, rfl, rfl⟩ | ⟨l, ls₁, r, junk, rfl, rfl, rfl, rfl, hl⟩ |
      ⟨r, junk, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl⟩
  · have hv : vs = (P.map WVal.toVal).reverse ++ [] := by
      simpa only [Flow.blockVals, Option.some.injEq] using hvs.symm
    obtain ⟨r, hex, hok, htake⟩ := blk_vals_ok (ls₁ := ls₁) hfit (hP _ _ rfl)
    exact ⟨ls₁, r, hseq, hex, hok, rfl, rfl, hv ▸ htake⟩
  · cases l with
    | succ => simp [Flow.blockVals] at hvs
    | zero =>
        have hv : vs = r.toList.map WVal.toVal ++ junk := by
          simpa only [Flow.blockVals, Option.some.injEq] using hvs.symm
        have hok : BlockOk ty r := blockOk_of (by simpa using hl.symm)
        exact ⟨ls₁, r, hseq, .brk0 hok, hok, rfl, rfl,
          hv ▸ take_toList hok (.inl (by simpa using hl.symm)) junk⟩
  · simp [Flow.blockVals] at hvs
  · simp [Flow.blockVals] at hvs

/-- A typed block body that branches out of the block or escapes. -/
theorem blk_out {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s s₁ : Store H} {mi : ModuleInst}
    {ty : Option IntType} {ls : List WVal} {body : List Expr} {ob : Out (List WVal)} {f₁ : Frame}
    {fl fl' : Flow} {a : Option Ar}
    (hT : ExecT (arOf ty :: L) R n ls body ob) (hty : tySeq (arOf ty :: L) R n body = some a)
    (hc : Corr (arOf ty :: L) R s mi [] ob (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ o, Seq ls none body (toOpt ob) ∧ BlockExit ty (toOpt ob) o ∧ CorrA L R s mi o (s₁, f₁, fl') := by
  obtain ⟨hseq, -⟩ := execT_seq hty hT
  rcases corr_flow hc with ⟨ls₁, P, rfl, rfl, rfl, rfl⟩ | ⟨l, ls₁, r, junk, rfl, rfl, rfl, rfl, hl⟩ |
      ⟨r, junk, rfl, rfl, rfl, hR⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨h, -⟩
    · cases h
    · exact h.elim
  · rcases hfl with ⟨k, vs, h, rfl⟩ | ⟨h, -⟩
    · simp only [Flow.brk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, hseq, .brk, junk, rfl, by simpa using hl⟩
    · exact h.elim
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact ⟨_, hseq, .ret, _, junk, rfl, hR⟩
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact ⟨_, hseq, .trap, _, rfl⟩

/-- A loop body that completes. -/
theorem loop_vals {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s s₁ : Store H} {mi : ModuleInst}
    {ty : Option IntType} {ls : List WVal} {body : List Expr} {ob : Out (List WVal)} {f₁ : Frame}
    {vs : List Val} {a : Option Ar}
    (hT : ExecT (.none :: L) R n ls body ob) (hty : tySeq (.none :: L) R n body = some a)
    (hfit : arFits (arOf ty) (some a) = true)
    (hc : Corr (.none :: L) R s mi [] ob (s₁, f₁, .normal vs)) :
    ∃ ls₁ r, Seq ls none body (toOpt ob) ∧ LoopExit ty (toOpt ob) (.ok ls₁ (blockRes ty r)) ∧
      BlockOk ty r ∧ s₁ = s ∧ f₁ = frameOf mi ls₁ ∧
      vs.take (if ty.isSome then 1 else 0) = (blockRes ty r).toList.map WVal.toVal := by
  obtain ⟨hseq, hP⟩ := execT_seq hty hT
  rcases corr_flow hc with ⟨ls₁, P, rfl, rfl, rfl, hv⟩ | ⟨l, ls₁, r, junk, rfl, -, -, h, -⟩ |
      ⟨r, junk, rfl, -, h, -⟩ | ⟨rfl, -, h⟩
  · obtain ⟨b, rfl, hb⟩ := hP _ _ rfl
    have hab := arFits_eq hfit
    simp only [Flow.normal.injEq, List.append_nil] at hv
    subst hv
    rcases hb with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩
    · have hok : BlockOk ty none := blockOk_of (by simpa [arR] using hab.symm)
      exact ⟨ls₁, none, hseq, .ok hok, hok, rfl, rfl, by simp [blockRes]⟩
    · have hok : BlockOk ty (some w) := blockOk_of (by simpa [arR] using hab.symm)
      refine ⟨ls₁, some w, hseq, .ok hok, hok, rfl, rfl, ?_⟩
      have := take_toList hok (.inl (by simpa [arR] using hab.symm)) []
      simpa using this
  · cases h
  · cases h
  · cases h

/-- A loop body that branches back to the loop. -/
theorem loop_back {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s s₁ : Store H} {mi : ModuleInst}
    {ls : List WVal} {body : List Expr} {ob : Out (List WVal)} {f₁ : Frame}
    {vs : List Val} {a : Option Ar}
    (hT : ExecT (.none :: L) R n ls body ob) (hty : tySeq (.none :: L) R n body = some a)
    (hc : Corr (.none :: L) R s mi [] ob (s₁, f₁, .brk 0 vs)) :
    ∃ ls₁, Seq ls none body (.brk 0 ls₁ none) ∧ s₁ = s ∧ f₁ = frameOf mi ls₁ := by
  obtain ⟨hseq, -⟩ := execT_seq hty hT
  rcases corr_flow hc with ⟨ls₁, P, rfl, -, -, h⟩ | ⟨l, ls₁, r, junk, rfl, rfl, rfl, h, hl⟩ |
      ⟨r, junk, rfl, -, h, -⟩ | ⟨rfl, -, h⟩
  · cases h
  · simp only [Flow.brk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have : r = none := by cases r <;> simp_all [arR]
    subst this
    exact ⟨ls₁, hseq, rfl, rfl⟩
  · cases h
  · cases h

/-- A loop body that branches out of the loop or escapes. -/
theorem loop_out {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s s₁ : Store H} {mi : ModuleInst}
    {ty : Option IntType} {ls : List WVal} {body : List Expr} {ob : Out (List WVal)} {f₁ : Frame}
    {fl fl' : Flow} {a : Option Ar}
    (hT : ExecT (.none :: L) R n ls body ob) (hty : tySeq (.none :: L) R n body = some a)
    (hc : Corr (.none :: L) R s mi [] ob (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ o, Seq ls none body (toOpt ob) ∧ LoopExit ty (toOpt ob) o ∧ CorrA L R s mi o (s₁, f₁, fl') := by
  obtain ⟨hseq, -⟩ := execT_seq hty hT
  rcases corr_flow hc with ⟨ls₁, P, rfl, rfl, rfl, rfl⟩ | ⟨l, ls₁, r, junk, rfl, rfl, rfl, rfl, hl⟩ |
      ⟨r, junk, rfl, rfl, rfl, hR⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨h, -⟩
    · cases h
    · exact h.elim
  · rcases hfl with ⟨k, vs, h, rfl⟩ | ⟨h, -⟩
    · simp only [Flow.brk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, hseq, .brk, junk, rfl, by simpa using hl⟩
    · exact h.elim
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact ⟨_, hseq, .ret, _, junk, rfl, hR⟩
  · rcases hfl with ⟨k, vs, h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact ⟨_, hseq, .trap, _, rfl⟩

/-! ## The typing of structured constructs -/

theorem tyE_block {L : List Ar} {R : Ar} {n : Nat} {ty : Option IntType} {body : List Expr}
    {x : Option Ar} (h : tyE L R n (.block ty body) = some x) :
    ∃ a, tySeq (arOf ty :: L) R n body = some a ∧ arFits (arOf ty) (some a) = true ∧
      x = some (arOf ty) := by
  rw [tyE] at h
  by_cases hc : arFits (arOf ty) (tySeq (arOf ty :: L) R n body) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    obtain ⟨a, ha⟩ := arFits_some hc
    rw [ha] at hc
    exact ⟨a, ha, hc, (Option.some.inj h).symm⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

theorem tyE_loop {L : List Ar} {R : Ar} {n : Nat} {ty : Option IntType} {body : List Expr}
    {x : Option Ar} (h : tyE L R n (.loop ty body) = some x) :
    ∃ a, tySeq (.none :: L) R n body = some a ∧ arFits (arOf ty) (some a) = true ∧
      x = some (arOf ty) := by
  rw [tyE] at h
  by_cases hc : arFits (arOf ty) (tySeq (.none :: L) R n body) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    obtain ⟨a, ha⟩ := arFits_some hc
    rw [ha] at hc
    exact ⟨a, ha, hc, (Option.some.inj h).symm⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

theorem tyE_if {L : List Ar} {R : Ar} {n : Nat} {ty : Option IntType} {c : Expr}
    {t e : List Expr} {x : Option Ar} (h : tyE L R n (.if_ ty c t e) = some x) :
    tyE L R n c = some (some .one) ∧
    (∃ a, tySeq (arOf ty :: L) R n t = some a ∧ arFits (arOf ty) (some a) = true) ∧
    (∃ a, tySeq (arOf ty :: L) R n e = some a ∧ arFits (arOf ty) (some a) = true) ∧
      x = some (arOf ty) := by
  rw [tyE] at h
  by_cases hc : (tyE L R n c == some (some .one) && arFits (arOf ty) (tySeq (arOf ty :: L) R n t) &&
      arFits (arOf ty) (tySeq (arOf ty :: L) R n e)) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨a, ha⟩ := arFits_some h2
    obtain ⟨b, hb⟩ := arFits_some h3
    rw [ha] at h2; rw [hb] at h3
    exact ⟨h1, ⟨a, ha, h2⟩, ⟨b, hb, h3⟩, (Option.some.inj h).symm⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

/-- Recognised operands are typed operands. -/
theorem args_typed {L : List Ar} {R : Ar} {n : Nat} {i : Instr} {as : List Expr} {e : Expr}
    (hr : ofInstr? i as = some e) {x : Option Ar} (hty : tyE L R n e = some x) :
    tyArgs L R n as = true := by
  unfold ofInstr? at hr
  split at hr <;> (try split at hr) <;> (cases hr)
  all_goals first
    | rfl
    | exact (tyE_br hty).1
    | exact (tyE_brIf hty).1
    | exact (tyE_return hty).1
    | (simp only [tyE] at hty; split at hty <;> simp_all [tyArgs])

/-- No operands never end abruptly. -/
private theorem args_nil_not_abrupt {ls : List WVal} {oa : Out (List WVal)} (h : Args ls [] oa)
    (hab : oa.Abrupt) : False := by
  cases h
  exact absurd hab id

/-- One operand ends abruptly exactly when its expression does. -/
private theorem args_one_abrupt {ls : List WVal} {oa : Out (List WVal)} {a : Expr}
    (h : Args ls [a] oa) (hab : oa.Abrupt) : ∃ o, Exec ls a o ∧ o.Abrupt ∧ oa = o.cast := by
  generalize hl : [a] = l at h
  cases h with
  | nil => cases hl
  | cons _ _ => exact absurd hab id
  | head_abrupt he hab' => cases hl; exact ⟨_, he, hab', rfl⟩
  | tail_abrupt _ hr' hab' =>
      cases hl
      generalize hn : ([] : List Expr) = l' at hr'
      cases hr' with
      | nil => exact absurd hab' id
      | _ => cases hn

/-- Abrupt operands make the recognised expression abrupt, at the same exit. -/
theorem abrupt_lift {i : Instr} {as : List Expr} {e : Expr} (hr : ofInstr? i as = some e)
    {ls : List WVal} {oa : Out (List WVal)} (ha : Args ls as oa) (hab : oa.Abrupt) :
    ∃ o, Exec ls e o ∧ o.Abrupt ∧ oa = o.cast := by
  unfold ofInstr? at hr
  split at hr <;> (try split at hr) <;> (cases hr)
  all_goals first
    | exact (args_nil_not_abrupt ha hab).elim
    | exact ⟨_, .op_abrupt ha hab, Out.cast_abrupt _ hab, (Out.cast_cast _ hab).symm⟩
    | exact ⟨_, .br_abrupt ha hab, Out.cast_abrupt _ hab, (Out.cast_cast _ hab).symm⟩
    | exact ⟨_, .brIf_abrupt ha hab, Out.cast_abrupt _ hab, (Out.cast_cast _ hab).symm⟩
    | exact ⟨_, .return_abrupt ha hab, Out.cast_abrupt _ hab, (Out.cast_cast _ hab).symm⟩
    | (obtain ⟨o, he, hab', rfl⟩ := args_one_abrupt ha hab; exact ⟨o, .localSet_abrupt he hab', hab', rfl⟩)
    | (obtain ⟨o, he, hab', rfl⟩ := args_one_abrupt ha hab; exact ⟨o, .localTee_abrupt he hab', hab', rfl⟩)
    | (obtain ⟨o, he, hab', rfl⟩ := args_one_abrupt ha hab; exact ⟨o, .drop_abrupt he hab', hab', rfl⟩)

end Silmaril.Proofs.Wasm.SSA.Native.Bwd
