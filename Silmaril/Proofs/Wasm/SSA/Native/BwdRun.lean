module

public import Silmaril.Proofs.Wasm.SSA.Native.BwdCtl

/-!
# Native adequacy, backward: the induction

`bwd`: an evaluation of silmaril's native interpreter on recognised, typed
trees is a typed list execution of the fragment with the corresponding
outcome. `native_backward`: on an arity-checked function body, every
interpreter result with an observable call outcome is a fragment run with
that outcome.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native.Bwd

open Silmaril.Wasm hiding Expr
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

theorem tyL_cons {L : List Ar} {R : Ar} {n : Nat} {e : Expr} {fs : List Expr}
    (h : TyL L R n (e :: fs)) : ∃ x, tyE L R n e = some x ∧ (∀ a, x = some a → TyL L R n fs) := by
  simp only [TyL] at h
  split at h
  · rename_i heq; exact ⟨none, heq, fun _ h => by cases h⟩
  · rename_i a heq; exact ⟨some a, heq, fun _ hh => by cases hh; exact h⟩
  · exact h.elim

theorem corrA_abrupt {H : Type} {L : List Ar} {R : Ar} {s : Store H} {mi : ModuleInst} {α : Type}
    {o : Out α} {x : Store H × Frame × Flow} (h : CorrA L R s mi o x) : o.Abrupt := by
  cases o <;> simp_all [CorrA, Out.Abrupt]

theorem toList_reverse (r : Option WVal) : (r.toList.map WVal.toVal).reverse = r.toList.map WVal.toVal := by
  cases r <;> rfl

/-- A completed head followed by the continuation's outcome. -/
theorem combine {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s : Store H} {mi : ModuleInst}
    {stk : List Val} {ls ls₁ : List WVal} {e : Expr} {fs : List Expr} {r : Option WVal}
    {x : Store H × Frame × Flow} (he : Exec ls e (.ok ls₁ r))
    (hty : tyE L R n e = some (some (arR r)))
    (hk : ∃ o, ExecT L R n ls₁ fs o ∧ Corr L R s mi (r.toList.map WVal.toVal ++ stk) o x) :
    ∃ o, ExecT L R n ls (e :: fs) o ∧ Corr L R s mi stk o x := by
  obtain ⟨o, hT, hc⟩ := hk
  cases o with
  | ok ls₂ P =>
      refine ⟨_, .cons he hty hT, ?_⟩
      simp only [Corr] at hc ⊢
      rw [hc]
      simp [List.reverse_append, toList_reverse]
  | _ => exact ⟨_, .tail he hty hT trivial, hc⟩

/-- An abrupt head. -/
theorem head_out {H : Type} {L : List Ar} {R : Ar} {n : Nat} {s : Store H} {mi : ModuleInst}
    {stk : List Val} {ls : List WVal} {e : Expr} {fs : List Expr} {o : Out (Option WVal)}
    {x : Store H × Frame × Flow} (he : Exec ls e o) (hab : o.Abrupt) (hc : CorrA L R s mi o x) :
    ∃ o, ExecT L R n ls (e :: fs) o ∧ Corr L R s mi stk o x :=
  ⟨_, .head he hab, (corr_abrupt (Out.cast_abrupt _ hab)).mpr ((corrA_cast hab).mpr hc)⟩

theorem execT_single {L : List Ar} {R : Ar} {n : Nat} {ls : List WVal} {c : Expr}
    {o : Out (List WVal)} (h : ExecT L R n ls [c] o) :
    (∃ ls₁ r P, o = .ok ls₁ (r.toList ++ P) ∧ Exec ls c (.ok ls₁ r) ∧
      tyE L R n c = some (some (arR r)) ∧ P = []) ∨
    (∃ o', Exec ls c o' ∧ o'.Abrupt ∧ o = o'.cast) := by
  cases h with
  | cons he ht hr => cases hr; exact .inl ⟨_, _, _, rfl, he, ht, rfl⟩
  | head he hab => exact .inr ⟨_, he, hab, rfl⟩
  | tail _ _ hr hab => cases hr; exact absurd hab id

section Cases

variable {H : Type} {mi : ModuleInst} {s s₁ s₂ : Store H} {fr f₁ f₂ : Frame}
  {stk stk₁ vs : List Val} {ls ls₁ : List WVal} {L : List Ar} {R : Ar} {n : Nat}
  {es body : List BExpr} {fs fs' : List Expr} {x : Store H × Frame × Flow} {fl : Flow}
  {bt : BlockType} {ty : Option IntType} {np nr : Nat}

/-- What `bwd` proves of one interpreter run `Eval s fr stk es x`. -/
private abbrev Sim (mi : ModuleInst) (s : Store H) (fr : Frame) (stk : List Val) (es : List BExpr)
    (x : Store H × Frame × Flow) : Prop :=
  ∀ {ls : List WVal} {fs : List Expr} {L : List Ar} {R : Ar} {n : Nat},
    fr = frameOf mi ls → ofBExprs? es = some fs → TyL L R n fs →
    ∃ o, ExecT L R n ls fs o ∧ Corr L R s mi stk o x

/-! ### Small facts about outcomes and recognition -/

private theorem isNormal_of_eq {s' : Store H} {f' : Frame} (h : (s', f', fl) = (s, fr, .normal vs)) :
    fl.IsNormal := by
  cases h
  trivial

private theorem corrA_normal {α : Type} {o : Out α} (h : CorrA L R s mi o (s₁, f₁, .normal vs)) :
    False := by
  cases o <;> simp [CorrA] at h

/-- A run that did not continue normally corresponds to an abrupt outcome. -/
private theorem abrupt_of_corr {o : Out (List WVal)} (hc : Corr L R s mi stk o (s₁, f₁, fl))
    (hfl : ¬ fl.IsNormal) : o.Abrupt := by
  cases o with
  | ok ls P => exact absurd (isNormal_of_eq hc) hfl
  | _ => trivial

/-- A run that continued normally corresponds to a completed outcome. -/
private theorem corr_normal {o : Out (List WVal)} (hc : Corr L R s mi stk o (s₁, f₁, .normal vs)) :
    ∃ ls' P, o = .ok ls' P ∧ s = s₁ ∧ f₁ = frameOf mi ls' ∧
      vs = (P.map WVal.toVal).reverse ++ stk := by
  rcases corr_flow hc with ⟨ls', P, rfl, hs, hf, hv⟩ | ⟨_, _, _, _, -, -, -, h, -⟩ |
      ⟨_, _, -, -, h, -⟩ | ⟨-, -, h⟩
  · exact ⟨ls', P, rfl, hs.symm, hf, Flow.normal.inj hv⟩
  all_goals cases h

private theorem arity_eq {f : Frame} (hbt : ofBlockType? bt = some ty)
    (har : Binaryen.arity f bt = some (np, nr)) : np = 0 ∧ nr = if ty.isSome then 1 else 0 := by
  have h := Prod.mk.inj (Option.some.inj ((ofBlockType?_arity hbt).symm.trans har))
  exact ⟨h.1.symm, h.2.symm⟩

/-- A recognised, typed operator at the head of a list. -/
private theorem op_inv {i : Instr} {args : List BExpr} (hfs : ofBExprs? (.op i args :: es) = some fs)
    (hty : TyL L R n fs) :
    ∃ e fs' as xe, fs = e :: fs' ∧ ofBExprs? args = some as ∧ ofInstr? i as = some e ∧
      ofBExprs? es = some fs' ∧ tyE L R n e = some xe ∧ tyArgs L R n as = true ∧
      (∀ a, xe = some a → TyL L R n fs') := by
  obtain ⟨e, fs', rfl, he, hfs'⟩ := ofBExprs?_cons hfs
  obtain ⟨as, has, hr⟩ := ofBExpr?_op he
  obtain ⟨xe, htye, hrest⟩ := tyL_cons hty
  exact ⟨e, fs', as, xe, rfl, has, hr, hfs', htye, args_typed hr htye, hrest⟩

/-- A recognised, typed block at the head of a list. -/
private theorem block_inv (hfs : ofBExprs? (.block bt body :: es) = some fs) (hty : TyL L R n fs) :
    ∃ ty body' fs' a, fs = .block ty body' :: fs' ∧ ofBlockType? bt = some ty ∧
      ofBExprs? body = some body' ∧ ofBExprs? es = some fs' ∧
      tySeq (arOf ty :: L) R n body' = some a ∧ arFits (arOf ty) (some a) = true ∧
      tyE L R n (.block ty body') = some (some (arOf ty)) ∧ TyL L R n fs' := by
  obtain ⟨e, fs', rfl, he, hfs'⟩ := ofBExprs?_cons hfs
  obtain ⟨ty, body', hbt, hb, rfl⟩ := ofBExpr?_block he
  obtain ⟨xe, htye, hrest⟩ := tyL_cons hty
  obtain ⟨a, hseqty, hfit, rfl⟩ := tyE_block htye
  exact ⟨ty, body', fs', a, rfl, hbt, hb, hfs', hseqty, hfit, htye, hrest _ rfl⟩

/-- A recognised, typed loop at the head of a list. -/
private theorem loop_inv (hfs : ofBExprs? (.loop bt body :: es) = some fs) (hty : TyL L R n fs) :
    ∃ ty body' fs' a, fs = .loop ty body' :: fs' ∧ ofBlockType? bt = some ty ∧
      ofBExprs? body = some body' ∧ ofBExprs? es = some fs' ∧
      tySeq (.none :: L) R n body' = some a ∧ arFits (arOf ty) (some a) = true ∧
      tyE L R n (.loop ty body') = some (some (arOf ty)) ∧ TyL L R n fs' := by
  obtain ⟨e, fs', rfl, he, hfs'⟩ := ofBExprs?_cons hfs
  obtain ⟨ty, body', hbt, hb, rfl⟩ := ofBExpr?_loop he
  obtain ⟨xe, htye, hrest⟩ := tyL_cons hty
  obtain ⟨a, hseqty, hfit, rfl⟩ := tyE_loop htye
  exact ⟨ty, body', fs', a, rfl, hbt, hb, hfs', hseqty, hfit, htye, hrest _ rfl⟩

/-- A recognised, typed `if` at the head of a list. -/
private theorem if_inv {c t el : List BExpr} (hfs : ofBExprs? (.if_ bt c t el :: es) = some fs)
    (hty : TyL L R n fs) :
    ∃ cb ty c' t' e' fs', c = [cb] ∧ fs = .if_ ty c' t' e' :: fs' ∧ ofBlockType? bt = some ty ∧
      ofBExprs? [cb] = some [c'] ∧ ofBExprs? t = some t' ∧ ofBExprs? el = some e' ∧
      ofBExprs? es = some fs' ∧ tyE L R n c' = some (some .one) ∧
      tyE L R n (.if_ ty c' t' e') = some (some (arOf ty)) ∧ TyL L R n fs' ∧
      (∃ a, tySeq (arOf ty :: L) R n t' = some a ∧ arFits (arOf ty) (some a) = true) ∧
      (∃ a, tySeq (arOf ty :: L) R n e' = some a ∧ arFits (arOf ty) (some a) = true) := by
  obtain ⟨e, fs', rfl, he, hfs'⟩ := ofBExprs?_cons hfs
  obtain ⟨cb, ty, c', t', e', rfl, hbt, hcb, ht, hel, rfl⟩ := ofBExpr?_if he
  obtain ⟨xe, htye, hrest⟩ := tyL_cons hty
  obtain ⟨htc, hta, hea, rfl⟩ := tyE_if htye
  have hcs : ofBExprs? [cb] = some [c'] := by simp [ofBExprs?, hcb]
  exact ⟨cb, ty, c', t', e', fs', rfl, rfl, hbt, hcs, ht, hel, hfs', htc, htye, hrest _ rfl, hta, hea⟩

/-- The arm an `if` takes on `b`, recognised and typed. -/
private theorem if_arm (b : Bool) {t el : List BExpr} {t' e' : List Expr}
    (ht : ofBExprs? t = some t') (hel : ofBExprs? el = some e')
    (hta : ∃ a, tySeq (arOf ty :: L) R n t' = some a ∧ arFits (arOf ty) (some a) = true)
    (hea : ∃ a, tySeq (arOf ty :: L) R n e' = some a ∧ arFits (arOf ty) (some a) = true) :
    ofBExprs? (if b then t else el) = some (if b then t' else e') ∧
      ∃ a, tySeq (arOf ty :: L) R n (if b then t' else e') = some a ∧
        arFits (arOf ty) (some a) = true := by
  cases b
  · exact ⟨hel, hea⟩
  · exact ⟨ht, hta⟩

/-- An `if` condition that continued normally produced exactly one value. -/
private theorem if_cond {cb : BExpr} {c' : Expr} {cv : Val}
    (ih_c : Sim mi s fr stk [cb] (s₁, f₁, .normal (cv :: stk₁))) (hfr : fr = frameOf mi ls)
    (hcs : ofBExprs? [cb] = some [c']) (htc : tyE L R n c' = some (some .one)) :
    ∃ ls₁ w, Exec ls c' (.ok ls₁ (some w)) ∧ s₁ = s ∧ f₁ = frameOf mi ls₁ ∧
      cv = WVal.toVal w ∧ stk₁ = stk := by
  obtain ⟨oc, hTc, hcc⟩ := ih_c hfr hcs (show TyL L R n [c'] by simp [TyL, htc])
  rcases execT_single hTc with ⟨ls₁, r, P, rfl, hexc, htyc, rfl⟩ | ⟨o', -, hab, rfl⟩
  · cases r with
    | none => simp [htc, arR] at htyc
    | some w =>
        have h : s₁ = s ∧ f₁ = frameOf mi ls₁ ∧ cv = WVal.toVal w ∧ stk₁ = stk := by
          simpa [Corr] using hcc
        exact ⟨ls₁, w, hexc, h⟩
  · exact (corrA_normal ((corr_abrupt (Out.cast_abrupt _ hab)).mp hcc)).elim

/-- The continuation after a block-like head that completed with `blockRes ty r`. -/
private theorem block_cont {e : Expr} {r : Option WVal}
    (he : Exec ls e (.ok ls₁ (blockRes ty r))) (hok : BlockOk ty r)
    (htye : tyE L R n e = some (some (arOf ty)))
    (htake : vs.take (if ty.isSome then 1 else 0) = (blockRes ty r).toList.map WVal.toVal)
    (ih_k : Sim mi s (frameOf mi ls₁) (vs.take (if ty.isSome then 1 else 0) ++ stk.drop 0) es x)
    (hfs' : ofBExprs? es = some fs') (hrest : TyL L R n fs') :
    ∃ o, ExecT L R n ls (e :: fs') o ∧ Corr L R s mi stk o x := by
  have hk : ∃ o, ExecT L R n ls₁ fs' o ∧
      Corr L R s mi ((blockRes ty r).toList.map WVal.toVal ++ stk) o x := by
    simpa only [htake, List.drop_zero] using ih_k rfl hfs' hrest
  exact combine he (by rw [arR_blockRes hok]; exact htye) hk

/-- Prefixing a loop iteration that branched back to the loop. -/
private theorem execT_loop_back {body' : List Expr} {o : Out (List WVal)}
    (hseq : Seq ls none body' (.brk 0 ls₁ none)) (hT : ExecT L R n ls₁ (.loop ty body' :: fs) o) :
    ExecT L R n ls (.loop ty body' :: fs) o := by
  cases hT with
  | cons hl ht hr => exact .cons (.loop_back hseq hl) ht hr
  | head hl hab => exact .head (.loop_back hseq hl) hab
  | tail hl ht hr hab => exact .tail (.loop_back hseq hl) ht hr hab

/-! ### One lemma per interpreter rule -/

private theorem sim_nil : Sim mi s fr stk [] (s, fr, .normal stk) := by
  intro ls fs L R n hfr hfs _
  rw [ofBExprs?_nil hfs, hfr]
  exact ⟨_, .nil, by simp [Corr]⟩

/-- Calls are never recognised. -/
private theorem sim_call {f : FuncIdx} {args : List BExpr} :
    Sim mi s fr stk (.op (.call f) args :: es) x := by
  intro ls fs L R n _ hfs _
  obtain ⟨e, fs', rfl, he, -⟩ := ofBExprs?_cons hfs
  obtain ⟨as, -, hr⟩ := ofBExpr?_op he
  simp [ofInstr?] at hr

private theorem sim_argsAbort {i : Instr} {args : List BExpr} (hfl : ¬ fl.IsNormal)
    (ih : Sim mi s fr stk args (s₁, f₁, fl)) : Sim mi s fr stk (.op i args :: es) (s₁, f₁, fl) := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨e, fs', as, xe, rfl, has, hr, -, -, hta, -⟩ := op_inv hfs hty
  obtain ⟨oa, hT, hc⟩ := ih hfr has (tyL_of_tyArgs hta)
  have hab : oa.Abrupt := abrupt_of_corr hc hfl
  obtain ⟨o, hex, hab', hoa⟩ := abrupt_lift hr (execT_args hta hT).1 hab
  have hca : CorrA L R s mi oa (s₁, f₁, fl) := (corr_abrupt hab).mp hc
  exact head_out hex hab' ((corrA_cast hab').mp (hoa ▸ hca))

private theorem sim_opOk {i : Instr} {args : List BExpr} {stk₂ : List Val}
    (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ih_args : Sim mi s fr stk args (s₁, f₁, .normal stk₁)) (ih_k : Sim mi s₂ f₂ stk₂ es x) :
    Sim mi s fr stk (.op i args :: es) x := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨e, fs', as, xe, rfl, has, hr, hfs', htye, hta, hrest⟩ := op_inv hfs hty
  obtain ⟨oa, hT, hc⟩ := ih_args hfr has (tyL_of_tyArgs hta)
  obtain ⟨ls₁, P, rfl, rfl, rfl, rfl⟩ := corr_normal hc
  obtain ⟨o, hex, hst⟩ := flat_step hr htye (execT_args hta hT).1 hflat
  cases o with
  | ok ls₂ r =>
      obtain ⟨hx, htyr⟩ := hst
      obtain ⟨rfl, rfl, rfl⟩ :
          s₂ = s ∧ f₂ = frameOf mi ls₂ ∧ stk₂ = r.toList.map WVal.toVal ++ stk := by
        simpa only [Prod.mk.injEq, Flow.normal.injEq] using hx
      have hxe : xe = some (arR r) := Option.some.inj (htye.symm.trans htyr)
      exact combine hex htyr (ih_k rfl hfs' (hrest _ hxe))
  | _ => simp [StepOK, CorrA] at hst

private theorem sim_opStop {i : Instr} {args : List BExpr}
    (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal)
    (ih_args : Sim mi s fr stk args (s₁, f₁, .normal stk₁)) :
    Sim mi s fr stk (.op i args :: es) (s₂, f₂, fl) := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨e, fs', as, xe, rfl, has, hr, -, htye, hta, -⟩ := op_inv hfs hty
  obtain ⟨oa, hT, hc⟩ := ih_args hfr has (tyL_of_tyArgs hta)
  obtain ⟨ls₁, P, rfl, rfl, rfl, rfl⟩ := corr_normal hc
  obtain ⟨o, hex, hst⟩ := flat_step hr htye (execT_args hta hT).1 hflat
  cases o with
  | ok ls₂ r => exact absurd (isNormal_of_eq hst.1) hfl
  | _ => exact head_out hex trivial hst

private theorem sim_blockOk (har : Binaryen.arity fr bt = some (np, nr))
    (hvs : fl.blockVals = some vs) (ih_body : Sim mi s fr (stk.take np) body (s₁, f₁, fl))
    (ih_k : Sim mi s₁ f₁ (vs.take nr ++ stk.drop np) es x) :
    Sim mi s fr stk (.block bt body :: es) x := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨ty, body', fs', a, rfl, hbt, hb, hfs', hseqty, hfit, htye, hrest⟩ := block_inv hfs hty
  obtain ⟨rfl, rfl⟩ := arity_eq hbt har
  obtain ⟨ob, hT, hc⟩ := ih_body hfr hb (tyL_of_tySeq hseqty)
  obtain ⟨ls₁, r, hseq, hbx, hok, rfl, rfl, htake⟩ := blk_vals hT hseqty hfit hc hvs
  exact block_cont (.block hseq hbx) hok htye htake ih_k hfs' hrest

/-- A block whose body branches outwards or escapes. -/
private theorem sim_blockOut {fl' : Flow} (har : Binaryen.arity fr bt = some (np, nr))
    (ih_body : Sim mi s fr (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    Sim mi s fr stk (.block bt body :: es) (s₁, f₁, fl') := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨ty, body', fs', a, rfl, hbt, hb, -, hseqty, -, -, -⟩ := block_inv hfs hty
  obtain ⟨rfl, -⟩ := arity_eq hbt har
  obtain ⟨ob, hT, hc⟩ := ih_body hfr hb (tyL_of_tySeq hseqty)
  obtain ⟨o, hseq, hbx, hco⟩ := blk_out hT hseqty hc hfl
  exact head_out (.block hseq hbx) (corrA_abrupt hco) hco

private theorem sim_loopOk (har : Binaryen.arity fr bt = some (np, nr))
    (ih_body : Sim mi s fr (stk.take np) body (s₁, f₁, .normal vs))
    (ih_k : Sim mi s₁ f₁ (vs.take nr ++ stk.drop np) es x) :
    Sim mi s fr stk (.loop bt body :: es) x := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨ty, body', fs', a, rfl, hbt, hb, hfs', hseqty, hfit, htye, hrest⟩ := loop_inv hfs hty
  obtain ⟨rfl, rfl⟩ := arity_eq hbt har
  obtain ⟨ob, hT, hc⟩ := ih_body hfr hb (tyL_of_tySeq hseqty)
  obtain ⟨ls₁, r, hseq, hlx, hok, rfl, rfl, htake⟩ := loop_vals hT hseqty hfit hc
  exact block_cont (.loop hseq hlx) hok htye htake ih_k hfs' hrest

private theorem sim_loopBack (har : Binaryen.arity fr bt = some (np, nr))
    (ih_body : Sim mi s fr (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ih_k : Sim mi s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) x) :
    Sim mi s fr stk (.loop bt body :: es) x := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨ty, body', fs', a, rfl, hbt, hb, -, hseqty, -, -, -⟩ := loop_inv hfs hty
  obtain ⟨rfl, -⟩ := arity_eq hbt har
  obtain ⟨ob, hT, hc⟩ := ih_body hfr hb (tyL_of_tySeq hseqty)
  obtain ⟨ls₁, hseq, hs, rfl⟩ := loop_back hT hseqty hc
  subst s₁
  obtain ⟨o, hT', hc'⟩ : ∃ o, ExecT L R n ls₁ (.loop ty body' :: fs') o ∧ Corr L R s mi stk o x := by
    simpa only [List.take_zero, List.drop_zero, List.nil_append] using ih_k rfl hfs hty
  exact ⟨o, execT_loop_back hseq hT', hc'⟩

/-- A loop whose body branches outwards or escapes. -/
private theorem sim_loopOut {fl' : Flow} (har : Binaryen.arity fr bt = some (np, nr))
    (ih_body : Sim mi s fr (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    Sim mi s fr stk (.loop bt body :: es) (s₁, f₁, fl') := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨ty, body', fs', a, rfl, hbt, hb, -, hseqty, -, -, -⟩ := loop_inv hfs hty
  obtain ⟨rfl, -⟩ := arity_eq hbt har
  obtain ⟨ob, hT, hc⟩ := ih_body hfr hb (tyL_of_tySeq hseqty)
  obtain ⟨o, hseq, hlx, hco⟩ := loop_out (ty := ty) hT hseqty hc hfl
  exact head_out (.loop hseq hlx) (corrA_abrupt hco) hco

private theorem sim_ifOk {cv : Val} {b : Bool} {c t el : List BExpr}
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (hvs : fl.blockVals = some vs) (ih_c : Sim mi s fr stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ih_arm : Sim mi s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (ih_k : Sim mi s₂ f₂ (vs.take nr ++ stk₁.drop np) es x) :
    Sim mi s fr stk (.if_ bt c t el :: es) x := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨cb, ty, c', t', e', fs', rfl, rfl, hbt, hcs, ht, hel, hfs', htc, htye, hrest, hta, hea⟩ :=
    if_inv hfs hty
  obtain ⟨ls₁, w, hexc, rfl, rfl, rfl, rfl⟩ := if_cond ih_c hfr hcs htc
  obtain ⟨rfl, rfl⟩ := arity_eq hbt har
  have hw : w.truthy = some b := (truthy_toVal w).symm.trans hb
  obtain ⟨harm, a, hst, hft⟩ := if_arm b ht hel hta hea
  obtain ⟨ob, hT, hco⟩ := ih_arm rfl harm (tyL_of_tySeq hst)
  obtain ⟨ls₂, r, hseq, hbx, hok, rfl, rfl, htake⟩ := blk_vals hT hst hft hco hvs
  exact block_cont (.if_ hexc hw hseq hbx) hok htye htake ih_k hfs' hrest

/-- An `if` whose chosen arm branches outwards or escapes. -/
private theorem sim_ifOut {cv : Val} {b : Bool} {c t el : List BExpr} {fl' : Flow}
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (ih_c : Sim mi s fr stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ih_arm : Sim mi s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    Sim mi s fr stk (.if_ bt c t el :: es) (s₂, f₂, fl') := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨cb, ty, c', t', e', fs', rfl, rfl, hbt, hcs, ht, hel, -, htc, -, -, hta, hea⟩ :=
    if_inv hfs hty
  obtain ⟨ls₁, w, hexc, rfl, rfl, rfl, rfl⟩ := if_cond ih_c hfr hcs htc
  obtain ⟨rfl, -⟩ := arity_eq hbt har
  have hw : w.truthy = some b := (truthy_toVal w).symm.trans hb
  obtain ⟨harm, a, hst, -⟩ := if_arm b ht hel hta hea
  obtain ⟨ob, hT, hco⟩ := ih_arm rfl harm (tyL_of_tySeq hst)
  obtain ⟨o, hseq, hbx, hcor⟩ := blk_out hT hst hco hfl
  exact head_out (.if_ hexc hw hseq hbx) (corrA_abrupt hcor) hcor

private theorem sim_ifAbort {c t el : List BExpr} (hfl : ¬ fl.IsNormal)
    (ih_c : Sim mi s fr stk c (s₁, f₁, fl)) : Sim mi s fr stk (.if_ bt c t el :: es) (s₁, f₁, fl) := by
  intro ls fs L R n hfr hfs hty
  obtain ⟨cb, ty, c', t', e', fs', rfl, rfl, -, hcs, -, -, -, htc, -⟩ := if_inv hfs hty
  obtain ⟨oc, hTc, hcc⟩ := ih_c hfr hcs (show TyL L R n [c'] by simp [TyL, htc])
  rcases execT_single hTc with ⟨ls₁, r, P, rfl, -, -, rfl⟩ | ⟨o', hexc, hab, rfl⟩
  · exact absurd (isNormal_of_eq hcc) hfl
  · have hca : CorrA L R s mi o' (s₁, f₁, fl) :=
      (corrA_cast hab).mp ((corr_abrupt (Out.cast_abrupt _ hab)).mp hcc)
    exact head_out (.if_abrupt hexc hab) hab hca

end Cases

/-- **Backward simulation** of the native interpreter by the fragment. -/
theorem bwd {H : Type} {mi : ModuleInst} {s : Store H} {fr : Frame} {stk : List Val}
    {es : List BExpr} {x : Store H × Frame × Flow} (h : Binaryen.Eval s fr stk es x) :
    ∀ {ls : List WVal} {fs : List Expr} {L : List Ar} {R : Ar} {n : Nat},
      fr = frameOf mi ls → ofBExprs? es = some fs → TyL L R n fs →
      ∃ o, ExecT L R n ls fs o ∧ Corr L R s mi stk o x := by
  induction h with
  | nil => exact sim_nil
  | argsAbort _ hfl ih => exact sim_argsAbort hfl ih
  | callOk => exact sim_call
  | callTrap => exact sim_call
  | callThrow => exact sim_call
  | opOk _ _ hflat _ ih_args ih_k => exact sim_opOk hflat ih_args ih_k
  | opStop _ _ hflat hfl ih_args => exact sim_opStop hflat hfl ih_args
  | blockOk har _ hvs _ ih_body ih_k => exact sim_blockOk har hvs ih_body ih_k
  | blockBrk har _ ih_body => exact sim_blockOut har ih_body (.inl ⟨_, _, rfl, rfl⟩)
  | blockEsc har _ hfl ih_body => exact sim_blockOut har ih_body (.inr ⟨hfl, rfl⟩)
  | loopOk har _ _ ih_body ih_k => exact sim_loopOk har ih_body ih_k
  | loopBack har _ _ ih_body ih_k => exact sim_loopBack har ih_body ih_k
  | loopBrk har _ ih_body => exact sim_loopOut har ih_body (.inl ⟨_, _, rfl, rfl⟩)
  | loopEsc har _ hfl ih_body => exact sim_loopOut har ih_body (.inr ⟨hfl, rfl⟩)
  | ifOk _ hb har _ hvs _ ih_c ih_arm ih_k => exact sim_ifOk hb har hvs ih_c ih_arm ih_k
  | ifBrk _ hb har _ ih_c ih_arm =>
      exact sim_ifOut hb har ih_c ih_arm (.inl ⟨_, _, rfl, rfl⟩)
  | ifEsc _ hb har _ hfl ih_c ih_arm => exact sim_ifOut hb har ih_c ih_arm (.inr ⟨hfl, rfl⟩)
  | ifAbort _ hfl ih_c => exact sim_ifAbort hfl ih_c

/-- An interpreter exit carrying the value `r` (above some junk) is the
fragment's return of `r`, when `r` has the function's result arity. -/
private theorem flowOut_ret {res : Option IntType} {r : Option WVal} {junk : List Val} {o : FOut}
    (har : arR r = arOf res) (ho : flowOut res (.ret (r.toList.map WVal.toVal ++ junk)) = some o) :
    o = .ret (blockRes res r) := by
  cases res with
  | none =>
      have h : FOut.ret none = o := by simpa only [flowOut, Option.some.injEq] using ho
      exact h.symm
  | some t =>
      cases r with
      | none => simp [arOf, arR] at har
      | some w =>
          have h : FOut.ret (some w) = o := by
            simpa only [flowOut, Option.toList_some, List.map_cons, List.map_nil, List.cons_append,
              List.nil_append, List.head?_cons, Option.bind_some, ofVal_toVal, Option.map_some,
              Option.some.injEq] using ho
          exact h.symm

/-- A completed body pushes the values of an optional result. -/
private theorem pushed_toList {P : List WVal} {b : Ar}
    (h : P = [] ∧ b = .none ∨ ∃ w, P = [w] ∧ b = .one) : ∃ r, P = r.toList ∧ b = arR r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩
  · exact ⟨none, rfl, rfl⟩
  · exact ⟨some w, rfl, rfl⟩

private theorem getLast?_toList (r : Option WVal) : r.toList.getLast? = r := by
  cases r <;> rfl

/-- A completed body: its pushed value is the function's return value. -/
private theorem exit_ok {res : Option IntType} {a : Option Ar} {ls' P : List WVal} {o : FOut}
    (hfit : arFits (arOf res) (some a) = true)
    (hP : ∃ b, a = some b ∧ (P = [] ∧ b = .none ∨ ∃ w, P = [w] ∧ b = .one))
    (ho : flowOut res (.normal ((P.map WVal.toVal).reverse ++ [])) = some o) :
    funcExit res (toOpt (.ok ls' P)) = some o := by
  obtain ⟨b, rfl, hb'⟩ := hP
  obtain ⟨r, rfl, rfl⟩ := pushed_toList hb'
  have har : arR r = arOf res := (arFits_eq hfit).symm
  have ho' : flowOut res (.normal (r.toList.map WVal.toVal ++ [])) = some o := by
    simpa only [toList_reverse] using ho
  show funcExit res (.ok ls' r.toList.getLast?) = some o
  rw [flowOut_ret har ho', getLast?_toList]
  rfl

/-- A branch out of the body: only the function's own label is observable. -/
private theorem exit_brk {res : Option IntType} {l : Nat} {ls' : List WVal} {r : Option WVal}
    {junk : List Val} {o : FOut} (hl : [arOf res][l]? = some (arR r))
    (ho : flowOut res (.brk l (r.toList.map WVal.toVal ++ junk)) = some o) :
    funcExit res (toOpt (.brk l ls' r)) = some o := by
  cases l with
  | succ l => simp [flowOut] at ho
  | zero =>
      have har : arR r = arOf res := by simpa using hl.symm
      rw [flowOut_ret har ho]
      rfl

/-- **Native adequacy, backward**: on an arity-checked function body, every
result of silmaril's native interpreter with an observable call outcome is a
run of the fragment function with that outcome. -/
theorem native_backward {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H} {mi : ModuleInst}
    {f : FragFunc} {bs : List BExpr} (hb : ofBExprs? bs = some f.body) (hn : f.native = true)
    {args : List WVal} (hty : args.map WVal.type = f.params) {s' : Store H} {fr : Frame} {fl : Flow}
    (h : Silmaril.Wasm.Binaryen.Eval s (frameOf mi (f.initLocals args)) [] bs (s', fr, fl))
    {o : FOut} (ho : flowOut f.result fl = some o) : f.Run args o := by
  obtain ⟨a, hseqty⟩ : ∃ a, tySeq [arOf f.result] (arOf f.result)
      (f.params.length + f.locals.length) f.body = some a := arFits_some hn
  have hfit : arFits (arOf f.result) (some a) = true := by
    rw [← hseqty]
    exact hn
  obtain ⟨ob, hT, hc⟩ := bwd h rfl hb (tyL_of_tySeq hseqty)
  obtain ⟨hseq, hP⟩ := execT_seq hseqty hT
  refine ⟨hty, toOpt ob, hseq, ?_⟩
  rcases corr_flow hc with ⟨ls', P, hob, -, -, hfl⟩ | ⟨l, ls', r, junk, hob, -, -, hfl, hl⟩ |
      ⟨r, junk, hob, -, hfl, hR⟩ | ⟨hob, -, hfl⟩
  · rw [hob]
    exact exit_ok hfit (hP _ _ hob) (hfl ▸ ho)
  · rw [hob]
    exact exit_brk hl (hfl ▸ ho)
  · have ho' : flowOut f.result (.ret (r.toList.map WVal.toVal ++ junk)) = some o := hfl ▸ ho
    rw [hob, flowOut_ret hR.symm ho']
    rfl
  · have ho' : flowOut f.result .trap = some o := hfl ▸ ho
    rw [hob]
    exact ho'

end Silmaril.Proofs.Wasm.SSA.Native.Bwd
