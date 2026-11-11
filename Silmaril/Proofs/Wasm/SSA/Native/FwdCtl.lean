module

public import Silmaril.Proofs.Wasm.SSA.Native.FwdCases

/-! # Native adequacy, forward direction: control, operands and bodies -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType)
open Silmaril.Wasm.Binaryen (BExpr evalFlat Flow Eval arity Next)
open Silmaril.Wasm.Execution.Core (Val Store Frame ModuleInst)
open Silmaril.Wasm.SSA

variable {H : Type} {s : Store H} {mi : ModuleInst}

/-! ## Blocks and loops -/

/-- How a block-like construct `c` (a block or an `if`) completes, given how its
body `Body` evaluates: the outcome `o` of `BlockExit` corresponds. -/
private theorem block_exit {ty : Option IntType} {out o : Out (Option WVal)} {L : List Ar}
    {R : Ar} {f : Frame} {stk : List Val} {c : BExpr} {x : Store H × Frame × Flow}
    {Body : Store H × Frame × Flow → Prop} (hbody : Body x)
    (hok : ∀ {s₁ f₁ fl vs}, Body (s₁, f₁, fl) → fl.blockVals = some vs →
      Eval s f stk [c] (s₁, f₁, .normal (vs.take (if ty.isSome then 1 else 0) ++ stk)))
    (hbrk : ∀ {s₁ f₁ k vs}, Body (s₁, f₁, .brk (k + 1) vs) → Eval s f stk [c] (s₁, f₁, .brk k vs))
    (hesc : ∀ {s₁ f₁ fl}, Body (s₁, f₁, fl) → fl.Escapes → Eval s f stk [c] (s₁, f₁, fl))
    (hx : BlockExit ty out o) (hcorr : Corr s mi vOf (arOf ty :: L) R [] out x) :
    ∃ y, Eval s f stk [c] y ∧ Corr s mi vOf L R stk o y ∧ ArOK (some (arOf ty)) o := by
  cases hx with
  | @ok ls r hok' =>
      obtain rfl : x = (s, frameOf mi ls, .normal (vOf r ++ [])) := hcorr
      refine ⟨_, hok hbody rfl, ?_, by simp [ArOK, arOf_blockRes hok']⟩
      show _ = (s, frameOf mi ls, Flow.normal (vOf (blockRes ty r) ++ stk))
      rw [take_vOf hok']
  | @brk0 ls r hok' =>
      obtain ⟨junk, rfl, -⟩ : ∃ junk, x = (s, frameOf mi ls, .brk 0 (vOf r ++ junk)) ∧
          (arOf ty :: L)[0]? = some (arR r) := hcorr
      refine ⟨_, hok hbody rfl, ?_, by simp [ArOK, arOf_blockRes hok']⟩
      show _ = (s, frameOf mi ls, Flow.normal (vOf (blockRes ty r) ++ stk))
      rw [take_vOf hok']
  | @brk l ls r =>
      obtain ⟨junk, rfl, hl⟩ : ∃ junk, x = (s, frameOf mi ls, .brk (l + 1) (vOf r ++ junk)) ∧
          (arOf ty :: L)[l + 1]? = some (arR r) := hcorr
      exact ⟨_, hbrk hbody, ⟨junk, rfl, by simpa only [List.getElem?_cons_succ] using hl⟩, trivial⟩
  | @ret r =>
      obtain ⟨fr, junk, rfl, hR⟩ : ∃ fr junk, x = (s, fr, .ret (vOf r ++ junk)) ∧ R = arR r := hcorr
      exact ⟨_, hesc hbody trivial, ⟨fr, junk, rfl, hR⟩, trivial⟩
  | trap =>
      obtain ⟨fr, rfl⟩ : ∃ fr, x = (s, fr, .trap) := hcorr
      exact ⟨_, hesc hbody trivial, ⟨fr, rfl⟩, trivial⟩

theorem fe_block {ls : List WVal} {ty : Option IntType} {body : List Expr}
    {out o : Out (Option WVal)} (hs : FS s mi ls none body out) (hx : BlockExit ty out o) :
    FE s mi ls (.block ty body) o := by
  intro L R n b stk ta hb hty
  obtain ⟨bt, bbody, hbe, hbt, hbb⟩ := ofBExpr?_block hb
  obtain ⟨hc, hta⟩ := ite_some_inv (c := arFits (arOf ty) (tySeq (arOf ty :: L) R n body)) hty
  obtain ⟨tb, htb, -⟩ := arFits_inv hc
  obtain ⟨x, hx', hcorr, -⟩ := hs rfl (arOf ty :: L) R n bbody [] tb hbb htb
  have hari : arity (frameOf mi ls) bt = some (0, if ty.isSome then 1 else 0) := arity_of hbt
  show ∃ y, Eval s (frameOf mi ls) stk [b] y ∧ Corr s mi vOf L R stk o y ∧ ArOK ta o
  rw [hbe, hta]
  exact block_exit (Body := Eval s (frameOf mi ls) [] bbody) hx'
    (fun hb hvs => .blockOk hari hb hvs .nil) (fun hb => .blockBrk hari hb)
    (fun hb hfl => .blockEsc hari hb hfl) hx hcorr

/-- How a loop `c` completes, except by a branch back to its own label, given how
its body `Body` evaluates: the outcome `o` of `LoopExit` corresponds. -/
private theorem loop_exit {ty : Option IntType} {out o : Out (Option WVal)} {L : List Ar}
    {R : Ar} {f : Frame} {stk : List Val} {c : BExpr} {x : Store H × Frame × Flow}
    {Body : Store H × Frame × Flow → Prop} (hbody : Body x)
    (hok : ∀ {s₁ f₁ vs}, Body (s₁, f₁, .normal vs) →
      Eval s f stk [c] (s₁, f₁, .normal (vs.take (if ty.isSome then 1 else 0) ++ stk)))
    (hbrk : ∀ {s₁ f₁ k vs}, Body (s₁, f₁, .brk (k + 1) vs) → Eval s f stk [c] (s₁, f₁, .brk k vs))
    (hesc : ∀ {s₁ f₁ fl}, Body (s₁, f₁, fl) → fl.Escapes → Eval s f stk [c] (s₁, f₁, fl))
    (hx : LoopExit ty out o) (hcorr : Corr s mi vOf (.none :: L) R [] out x) :
    ∃ y, Eval s f stk [c] y ∧ Corr s mi vOf L R stk o y ∧ ArOK (some (arOf ty)) o := by
  cases hx with
  | @ok ls r hok' =>
      obtain rfl : x = (s, frameOf mi ls, .normal (vOf r ++ [])) := hcorr
      refine ⟨_, hok hbody, ?_, by simp [ArOK, arOf_blockRes hok']⟩
      show _ = (s, frameOf mi ls, Flow.normal (vOf (blockRes ty r) ++ stk))
      rw [take_vOf hok']
  | @brk l ls r =>
      obtain ⟨junk, rfl, hl⟩ : ∃ junk, x = (s, frameOf mi ls, .brk (l + 1) (vOf r ++ junk)) ∧
          (Ar.none :: L)[l + 1]? = some (arR r) := hcorr
      exact ⟨_, hbrk hbody, ⟨junk, rfl, by simpa only [List.getElem?_cons_succ] using hl⟩, trivial⟩
  | @ret r =>
      obtain ⟨fr, junk, rfl, hR⟩ : ∃ fr junk, x = (s, fr, .ret (vOf r ++ junk)) ∧ R = arR r := hcorr
      exact ⟨_, hesc hbody trivial, ⟨fr, junk, rfl, hR⟩, trivial⟩
  | trap =>
      obtain ⟨fr, rfl⟩ : ∃ fr, x = (s, fr, .trap) := hcorr
      exact ⟨_, hesc hbody trivial, ⟨fr, rfl⟩, trivial⟩

theorem fe_loop {ls : List WVal} {ty : Option IntType} {body : List Expr}
    {out o : Out (Option WVal)} (hs : FS s mi ls none body out) (hx : LoopExit ty out o) :
    FE s mi ls (.loop ty body) o := by
  intro L R n b stk ta hb hty
  obtain ⟨bt, bbody, hbe, hbt, hbb⟩ := ofBExpr?_loop hb
  obtain ⟨hc, hta⟩ := ite_some_inv (c := arFits (arOf ty) (tySeq (.none :: L) R n body)) hty
  obtain ⟨tb, htb, -⟩ := arFits_inv hc
  obtain ⟨x, hx', hcorr, -⟩ := hs rfl (.none :: L) R n bbody [] tb hbb htb
  have hari : arity (frameOf mi ls) bt = some (0, if ty.isSome then 1 else 0) := arity_of hbt
  show ∃ y, Eval s (frameOf mi ls) stk [b] y ∧ Corr s mi vOf L R stk o y ∧ ArOK ta o
  rw [hbe, hta]
  exact loop_exit (Body := Eval s (frameOf mi ls) [] bbody) hx'
    (fun hb => .loopOk hari hb .nil) (fun hb => .loopBrk hari hb)
    (fun hb hfl => .loopEsc hari hb hfl) hx hcorr

theorem fe_loop_back {ls ls' : List WVal} {ty : Option IntType} {body : List Expr}
    {r : Option WVal} {o : Out (Option WVal)} (hs : FS s mi ls none body (.brk 0 ls' r))
    (hr : FE s mi ls' (.loop ty body) o) : FE s mi ls (.loop ty body) o := by
  intro L R n b stk ta hb hty
  obtain ⟨y, hy, hc', har'⟩ := hr L R n b stk ta hb hty
  obtain ⟨bt, bbody, rfl, hbt, hbb⟩ := ofBExpr?_loop hb
  unfold tyE at hty
  obtain ⟨hc, rfl⟩ := ite_some_inv hty
  obtain ⟨tb, htb, -⟩ := arFits_inv hc
  obtain ⟨x, hx', hcorr, -⟩ := hs rfl (.none :: L) R n bbody [] tb hbb htb
  obtain ⟨junk, rfl, -⟩ := hcorr
  have hari := arity_of (f := frameOf mi ls) hbt
  exact ⟨y, .loopBack hari hx' hy, hc', har'⟩

/-! ## `if` -/

/-- Unfold the check of a typed `if`. -/
private theorem tyE_if_inv {L : List Ar} {R : Ar} {n : Nat} {ty : Option IntType} {c : Expr}
    {t e : List Expr} {ta : Option Ar} (h : tyE L R n (.if_ ty c t e) = some ta) :
    tyE L R n c = some (some .one) ∧ arFits (arOf ty) (tySeq (arOf ty :: L) R n t) = true ∧
      arFits (arOf ty) (tySeq (arOf ty :: L) R n e) = true ∧ ta = some (arOf ty) := by
  obtain ⟨hcd, hta⟩ := ite_some_inv h
  have hcd' : (tyE L R n c = some (some .one) ∧ arFits (arOf ty) (tySeq (arOf ty :: L) R n t) = true) ∧
      arFits (arOf ty) (tySeq (arOf ty :: L) R n e) = true := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hcd
  exact ⟨hcd'.1.1, hcd'.1.2, hcd'.2, hta⟩

theorem fe_if {ls ls₁ : List WVal} {ty : Option IntType} {c : Expr} {t e : List Expr} {cv : WVal}
    {bb : Bool} {out o : Out (Option WVal)} (hc : FE s mi ls c (.ok ls₁ (some cv)))
    (hb : cv.truthy = some bb) (hs : FS s mi ls₁ none (if bb then t else e) out)
    (hx : BlockExit ty out o) : FE s mi ls (.if_ ty c t e) o := by
  intro L R n b stk ta hb' hty
  obtain ⟨bt, cb, tb, eb, hbe, hbt, hcb, htb, heb⟩ := ofBExpr?_if hb'
  obtain ⟨htc, hft, hfe, hta⟩ := tyE_if_inv hty
  obtain ⟨y, hy, hyc, -⟩ := hc L R n cb stk _ hcb htc
  have hcond : Eval s (frameOf mi ls) stk [cb] (s, frameOf mi ls₁, .normal (cv.toVal :: stk)) :=
    hyc ▸ hy
  have harm : ofBExprs? (if bb then tb else eb) = some (if bb then t else e) := by
    cases bb <;> assumption
  have harf : arFits (arOf ty) (tySeq (arOf ty :: L) R n (if bb then t else e)) = true := by
    cases bb <;> assumption
  obtain ⟨tb', htb', -⟩ := arFits_inv harf
  obtain ⟨x, hx', hcorr, -⟩ := hs rfl (arOf ty :: L) R n _ [] tb' harm htb'
  have hari : arity (frameOf mi ls₁) bt = some (0, if ty.isSome then 1 else 0) := arity_of hbt
  have htr : Silmaril.Wasm.Binaryen.truthy cv.toVal = some bb := by rw [truthy_toVal]; exact hb
  show ∃ y, Eval s (frameOf mi ls) stk [b] y ∧ Corr s mi vOf L R stk o y ∧ ArOK ta o
  rw [hbe, hta]
  exact block_exit (Body := Eval s (frameOf mi ls₁) [] (if bb then tb else eb)) hx'
    (fun hb hvs => .ifOk hcond htr hari hb hvs .nil) (fun hb => .ifBrk hcond htr hari hb)
    (fun hb hfl => .ifEsc hcond htr hari hb hfl) hx hcorr

theorem fe_if_abrupt {ls : List WVal} {ty : Option IntType} {c : Expr} {t e : List Expr}
    {out : Out (Option WVal)} (hc : FE s mi ls c out) (hab : out.Abrupt) :
    FE s mi ls (.if_ ty c t e) out := by
  intro L R n b stk ta hb' hty
  obtain ⟨bt, cb, tb, eb, rfl, hbt, hcb, htb, heb⟩ := ofBExpr?_if hb'
  unfold tyE at hty
  obtain ⟨hcd, -⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq] at hcd
  obtain ⟨⟨htc, -⟩, -⟩ := hcd
  obtain ⟨y, hy, hcr, -⟩ := hc L R n cb stk _ hcb htc
  obtain ⟨s', f', fl⟩ := y
  refine ⟨_, .ifAbort hy (corr_abrupt hcr hab), hcr, ?_⟩
  cases out with
  | ok => exact hab.elim
  | _ => trivial

/-! ## Branches -/

theorem shape_flat_args {e : Expr} {args : List Expr}
    (hshape : ∀ i args', ofInstr? i args' = some e → args' = args)
    (hs : ∀ ty body, e ≠ .block ty body) (hl : ∀ ty body, e ≠ .loop ty body)
    (hi : ∀ ty c t el, e ≠ .if_ ty c t el)
    (hty : ∀ L R n ta, tyE L R n e = some ta → tyArgs L R n args = true) :
    ∀ b L R n ta, ofBExpr? b = some e → tyE L R n e = some ta →
      ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true := by
  intro b L R n ta hb ht
  obtain ⟨i, bargs, args', rfl, hba, hin⟩ := flat_of hb hs hl hi
  obtain rfl := hshape i args' hin
  exact ⟨i, bargs, rfl, hba, hty L R n ta ht⟩

theorem shape_br {l : Nat} {args : List Expr} : ∀ b L R n ta, ofBExpr? b = some (Expr.br l args) → tyE L R n (Expr.br l args) = some ta →
      ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true :=
  shape_flat_args (e := .br l args) (args := args)
    (fun _ _ h => ((ofInstr?_br h).choose_spec.2.1).symm)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
    (fun L R n ta h => by
      unfold tyE at h; obtain ⟨hc, -⟩ := ite_some_inv h
      simp only [Bool.and_eq_true] at hc; exact hc.1.1)

theorem shape_brIf {l : Nat} {args : List Expr} : ∀ b L R n ta, ofBExpr? b = some (Expr.brIf l args) → tyE L R n (Expr.brIf l args) = some ta →
      ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true :=
  shape_flat_args (e := .brIf l args) (args := args)
    (fun _ _ h => ((ofInstr?_brIf h).choose_spec.2.1).symm)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
    (fun L R n ta h => by
      unfold tyE at h; obtain ⟨hc, -⟩ := ite_some_inv h
      simp only [Bool.and_eq_true] at hc; exact hc.1.1)

theorem shape_return {args : List Expr} : ∀ b L R n ta, ofBExpr? b = some (Expr.return_ args) → tyE L R n (Expr.return_ args) = some ta →
      ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true :=
  shape_flat_args (e := .return_ args) (args := args)
    (fun _ _ h => ((ofInstr?_return h).2).symm)
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
    (fun L R n ta h => by
      unfold tyE at h; obtain ⟨hc, -⟩ := ite_some_inv h
      simp only [Bool.and_eq_true] at hc; exact hc.1.1)

/-- At most one operand value: pushed in order, it is the optional result. -/
private theorem map_reverse_head? {vs : List WVal} (h : vs.length ≤ 1) :
    vs.reverse.map WVal.toVal = vOf vs.head? := by
  match vs, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- At most one operand value: its count is the arity of the optional result. -/
private theorem arR_head? {vs : List WVal} (h : vs.length ≤ 1) :
    (if vs.length = 1 then Ar.one else .none) = arR vs.head? := by
  match vs, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- Unfold the check of a typed `br`. -/
private theorem tyE_br_inv {L : List Ar} {R : Ar} {n l : Nat} {args : List Expr} {ta : Option Ar}
    (h : tyE L R n (.br l args) = some ta) :
    tyArgs L R n args = true ∧ L[l]? = some (if args.length = 1 then .one else .none) ∧
      args.length ≤ 1 ∧ ta = none := by
  obtain ⟨hc, hta⟩ := ite_some_inv h
  have hc' : (tyArgs L R n args = true ∧ L[l]? = some (if args.length = 1 then .one else .none)) ∧
      args.length ≤ 1 := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hc
  exact ⟨hc'.1.1, hc'.1.2, hc'.2, hta⟩

theorem fe_br {ls ls' : List WVal} {l : Nat} {args : List Expr} {vs : List WVal}
    (ha : FA s mi ls args (.ok ls' vs)) (hvs : Args ls args (.ok ls' vs)) :
    FE s mi ls (.br l args) (.brk l ls' vs.head?) := by
  intro L R n b stk ta hb hty
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨x, rfl, rfl, rfl⟩ : ∃ x, i = .br x ∧ args = args' ∧ l = x.toNat := ofInstr?_br hi
  obtain ⟨htys, hl, hlen, -⟩ := tyE_br_inv hty
  obtain ⟨y, hy, hyc⟩ := ha L R n bargs stk hba htys
  have hlv : vs.length ≤ 1 := args_length hvs ▸ hlen
  have hargs : Eval s (frameOf mi ls) stk bargs
      (s, frameOf mi ls', .normal (vOf vs.head? ++ stk)) := map_reverse_head? hlv ▸ hyc ▸ hy
  have hl' : L[x.toNat]? = some (arR vs.head?) := by
    rw [hl, ← arR_head? hlv, args_length hvs]
  exact ⟨_, eval_op (fun _ h => Instr.noConfusion h) hargs rfl, ⟨stk, rfl, hl'⟩, trivial⟩

/-- Unfold the check of a typed `return`. -/
private theorem tyE_return_inv {L : List Ar} {R : Ar} {n : Nat} {args : List Expr}
    {ta : Option Ar} (h : tyE L R n (.return_ args) = some ta) :
    tyArgs L R n args = true ∧ args.length ≤ 1 ∧
      R = (if args.length = 1 then .one else .none) ∧ ta = none := by
  obtain ⟨hc, hta⟩ := ite_some_inv h
  have hc' : (tyArgs L R n args = true ∧ args.length ≤ 1) ∧
      R = (if args.length = 1 then .one else .none) := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hc
  exact ⟨hc'.1.1, hc'.1.2, hc'.2, hta⟩

theorem fe_return {ls ls' : List WVal} {args : List Expr} {vs : List WVal}
    (ha : FA s mi ls args (.ok ls' vs)) (hvs : Args ls args (.ok ls' vs)) :
    FE s mi ls (.return_ args) (.ret vs.head?) := by
  intro L R n b stk ta hb hty
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, rfl⟩ : i = .return_ ∧ args = args' := ofInstr?_return hi
  obtain ⟨htys, hlen, hR, -⟩ := tyE_return_inv hty
  obtain ⟨y, hy, hyc⟩ := ha L R n bargs stk hba htys
  have hlv : vs.length ≤ 1 := args_length hvs ▸ hlen
  have hargs : Eval s (frameOf mi ls) stk bargs
      (s, frameOf mi ls', .normal (vOf vs.head? ++ stk)) := map_reverse_head? hlv ▸ hyc ▸ hy
  have hR' : R = arR vs.head? := by rw [hR, ← arR_head? hlv, args_length hvs]
  exact ⟨_, eval_op (fun _ h => Instr.noConfusion h) hargs rfl,
    ⟨frameOf mi ls', stk, rfl, hR'⟩, trivial⟩

/-- Unfold the check of a typed `br_if`. -/
private theorem tyE_brIf_inv {L : List Ar} {R : Ar} {n l : Nat} {args : List Expr}
    {ta : Option Ar} (h : tyE L R n (.brIf l args) = some ta) :
    tyArgs L R n args = true ∧ (args.length = 1 ∨ args.length = 2) ∧
      L[l]? = some (if args.length = 2 then .one else .none) ∧
      ta = some (if args.length = 2 then .one else .none) := by
  obtain ⟨hc, hta⟩ := ite_some_inv h
  have hc' : (tyArgs L R n args = true ∧ (args.length = 1 ∨ args.length = 2)) ∧
      L[l]? = some (if args.length = 2 then .one else .none) := by
    simpa only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hc
  have hta' : ta = some (if args.length = 2 then .one else .none) := by
    simpa only [beq_iff_eq] using hta
  exact ⟨hc'.1.1, hc'.1.2, hc'.2, hta'⟩

/-- The operands of a `br_if`: the condition on top of the optional value. -/
private theorem brIf_stack {vs : List WVal} {c : WVal} (hlen : vs.length = 1 ∨ vs.length = 2)
    (hc : vs.getLast? = some c) (stk : List Val) :
    vs.reverse.map WVal.toVal ++ stk = c.toVal :: (vOf vs.dropLast.head? ++ stk) ∧
      (if vs.length = 2 then Ar.one else .none) = arR vs.dropLast.head? := by
  match vs, hlen, hc with
  | [c'], _, hc =>
      have hcc : c' = c := by simpa using hc
      exact ⟨by rw [hcc]; rfl, rfl⟩
  | [v, c'], _, hc =>
      have hcc : c' = c := by simpa using hc
      exact ⟨by rw [hcc]; rfl, rfl⟩
  | [], hlen, _ => exact absurd hlen (by simp)
  | _ :: _ :: _ :: _, hlen, _ => exact absurd hlen (by simp)

theorem fe_brIf {ls ls' : List WVal} {l : Nat} {args : List Expr} {vs : List WVal} {c : WVal}
    {bb : Bool} (ha : FA s mi ls args (.ok ls' vs)) (hvs : Args ls args (.ok ls' vs))
    (hc : vs.getLast? = some c) (hb : c.truthy = some bb) :
    FE s mi ls (.brIf l args)
      (if bb then .brk l ls' vs.dropLast.head? else .ok ls' vs.dropLast.head?) := by
  intro L R n b stk ta hb' hty
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb' (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨x, rfl, rfl, rfl⟩ : ∃ x, i = .brIf x ∧ args = args' ∧ l = x.toNat := ofInstr?_brIf hi
  obtain ⟨htys, hlen, hl, hta⟩ := tyE_brIf_inv hty
  obtain ⟨y, hy, hyc⟩ := ha L R n bargs stk hba htys
  have hlv : vs.length = args.length := args_length hvs
  obtain ⟨hst, har⟩ := brIf_stack (hlv ▸ hlen) hc stk
  have hargs : Eval s (frameOf mi ls) stk bargs
      (s, frameOf mi ls', .normal (vs.reverse.map WVal.toVal ++ stk)) := hyc ▸ hy
  have hflat : evalFlat s (frameOf mi ls') (vs.reverse.map WVal.toVal ++ stk) (.brIf x) =
      some (s, frameOf mi ls', if bb then .brk x.toNat (vOf vs.dropLast.head? ++ stk)
        else .normal (vOf vs.dropLast.head? ++ stk)) := by
    rw [hst]; simp [evalFlat, truthy_toVal, hb]
  cases bb with
  | true =>
      have hl' : L[x.toNat]? = some (arR vs.dropLast.head?) := by rw [hl, ← hlv, har]
      exact ⟨_, eval_op (fun _ h => Instr.noConfusion h) hargs hflat, ⟨stk, rfl, hl'⟩, trivial⟩
  | false =>
      have hta' : ta = some (arR vs.dropLast.head?) := by rw [hta, ← hlv, har]
      exact ⟨_, eval_op (fun _ h => Instr.noConfusion h) hargs hflat, rfl, hta'⟩

/-! ## Operands -/

theorem fa_nil {ls : List WVal} : FA s mi ls [] (.ok ls []) := by
  intro L R n bs stk hbs _
  rw [ofBExprs?_nil hbs]
  exact ⟨_, .nil, rfl⟩

theorem fa_cons {ls ls₁ ls₂ : List WVal} {e : Expr} {es : List Expr} {v : WVal} {vs : List WVal}
    (he : FE s mi ls e (.ok ls₁ (some v))) (ha : FA s mi ls₁ es (.ok ls₂ vs)) :
    FA s mi ls (e :: es) (.ok ls₂ (v :: vs)) := by
  intro L R n bs stk hbs hty
  obtain ⟨b, bs', rfl, hb, hbs'⟩ := ofBExprs?_cons hbs
  simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at hty
  obtain ⟨x, hx, rfl, -⟩ := he L R n b stk _ hb hty.1
  obtain ⟨y, hy, rfl⟩ := ha L R n bs' _ hbs' hty.2
  refine ⟨_, eval_cons_normal hx hy, ?_⟩
  simp [Corr, vOf]

theorem fa_head {ls : List WVal} {e : Expr} {es : List Expr} {out : Out (Option WVal)}
    (he : FE s mi ls e out) (hab : out.Abrupt) : FA s mi ls (e :: es) out.cast := by
  intro L R n bs stk hbs hty
  obtain ⟨b, bs', rfl, hb, hbs'⟩ := ofBExprs?_cons hbs
  simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at hty
  obtain ⟨x, hx, hc, -⟩ := he L R n b stk _ hb hty.1
  exact ⟨x, eval_cons_stop hx (corr_abrupt hc hab), corr_cast hab hc⟩

theorem fa_tail {ls ls₁ : List WVal} {e : Expr} {es : List Expr} {v : WVal}
    {out : Out (List WVal)} (he : FE s mi ls e (.ok ls₁ (some v))) (ha : FA s mi ls₁ es out)
    (hab : out.Abrupt) : FA s mi ls (e :: es) out := by
  intro L R n bs stk hbs hty
  obtain ⟨b, bs', rfl, hb, hbs'⟩ := ofBExprs?_cons hbs
  simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at hty
  obtain ⟨x, hx, rfl, -⟩ := he L R n b stk _ hb hty.1
  obtain ⟨y, hy, hc⟩ := ha L R n bs' _ hbs' hty.2
  refine ⟨y, eval_cons_normal hx hy, ?_⟩
  cases out with
  | ok => exact hab.elim
  | _ => exact hc

/-! ## Bodies -/

theorem fs_nil {ls : List WVal} {r : Option WVal} : FS s mi ls r [] (.ok ls r) := by
  intro hr L R n bs stk ta hbs hty
  subst hr
  rw [ofBExprs?_nil hbs]
  simp only [tySeq, Option.some.injEq] at hty; subst hty
  exact ⟨_, .nil, rfl, rfl⟩

/-- A checked body's first element is checked. -/
private theorem tySeq_cons_some {L : List Ar} {R : Ar} {n : Nat} {e : Expr} {es : List Expr}
    {ta : Option Ar} (h : tySeq L R n (e :: es) = some ta) : ∃ te, tyE L R n e = some te := by
  cases hte : tyE L R n e with
  | none => exact absurd h (by simp [tySeq, hte])
  | some te => exact ⟨te, rfl⟩

/-- An empty body completes normally, keeping its carried result. -/
private theorem seq_nil_inv {ls : List WVal} {r : Option WVal} {out : Out (Option WVal)}
    (h : Silmaril.Wasm.SSA.Seq ls r [] out) : out = .ok ls r := by
  cases h
  rfl

theorem fs_cons {ls ls₁ : List WVal} {r r₁ : Option WVal} {e : Expr} {es : List Expr}
    {out : Out (Option WVal)} (he : FE s mi ls e (.ok ls₁ r₁)) (hs : FS s mi ls₁ r₁ es out)
    (hsd : Silmaril.Wasm.SSA.Seq ls₁ r₁ es out) : FS s mi ls r (e :: es) out := by
  intro _ L R n bs stk ta hbs hty
  obtain ⟨b, bs', hbe, hb, hbs'⟩ := ofBExprs?_cons hbs
  obtain ⟨te, hte⟩ := tySeq_cons_some hty
  obtain ⟨x, hx, hxc, har⟩ := he L R n b stk te hb hte
  have har' : te = some (arR r₁) := har
  have hte' : tyE L R n e = some (some (arR r₁)) := har' ▸ hte
  have hx' : Eval s (frameOf mi ls) stk [b] (s, frameOf mi ls₁, .normal (vOf r₁ ++ stk)) :=
    hxc ▸ hx
  show ∃ y, Eval s (frameOf mi ls) stk bs y ∧ Corr s mi vOf L R stk out y ∧ ArOK ta out
  rw [hbe]
  cases r₁ with
  | none =>
      have hrest : tySeq L R n es = some ta := by simpa [tySeq, hte', arR] using hty
      obtain ⟨y, hy, hc, hy'⟩ := hs rfl L R n bs' stk ta hbs' hrest
      exact ⟨y, eval_cons_normal hx' hy, hc, hy'⟩
  | some v =>
      show ∃ y, Eval s (frameOf mi ls) stk (b :: bs') y ∧ Corr s mi vOf L R stk out y ∧ ArOK ta out
      have hlast : (if es.isEmpty then some (some Ar.one) else none) = some ta := by
        rw [← hty, tySeq, hte']; rfl
      obtain ⟨hes, hta⟩ := ite_some_inv hlast
      have hnil : es = [] := List.isEmpty_iff.mp hes
      have hout : out = .ok ls₁ (some v) := seq_nil_inv (hnil ▸ hsd)
      have hbnil : bs' = [] := ofBExprs?_nil (hnil ▸ hbs')
      rw [hbnil, hout, hta]
      exact ⟨_, eval_cons_normal hx' .nil, rfl, rfl⟩

theorem fs_abrupt {ls : List WVal} {r : Option WVal} {e : Expr} {es : List Expr}
    {out : Out (Option WVal)} (he : FE s mi ls e out) (hab : out.Abrupt) :
    FS s mi ls r (e :: es) out := by
  intro _ L R n bs stk ta hbs hty
  obtain ⟨b, bs', rfl, hb, hbs'⟩ := ofBExprs?_cons hbs
  simp only [tySeq] at hty
  cases hte : tyE L R n e with
  | none => simp [hte] at hty
  | some te =>
      obtain ⟨x, hx, hc, -⟩ := he L R n b stk te hb hte
      refine ⟨x, eval_cons_stop hx (corr_abrupt hc hab), hc, ?_⟩
      cases out with
      | ok => exact hab.elim
      | _ => trivial

end Silmaril.Proofs.Wasm.SSA.Native
