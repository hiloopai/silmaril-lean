module

public import Silmaril.Wasm.SSA.Native.Defs
public import Silmaril.Wasm.SSA.Fragment.Thms

/-!
# Native adequacy, backward: basic notions

A typed list execution `ExecT` runs fragment expressions left to right,
pushing the value of each one that produces a value, and records that each
completed element has the arity the check gives it. `Corr` relates a list
outcome to a final interpreter result (stack top-first, frame `frameOf`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native.Bwd

open Silmaril.Wasm hiding Expr
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

/-! ## Values -/

/-- The arity of a carried value. -/
def arR (r : Option WVal) : Ar := if r.isSome then .one else .none

@[simp] theorem arR_none : arR none = .none := rfl
@[simp] theorem arR_some (w : WVal) : arR (some w) = .one := rfl

theorem asInt_toVal (t : IntType) (w : WVal) :
    Binaryen.asInt t (WVal.toVal w) = w.asInt t := by
  cases t <;> cases w <;> rfl

theorem ofInt_toVal (t : IntType) (x : BitVec t.width) :
    Binaryen.ofInt t x = WVal.toVal (WVal.ofInt t x) := by
  cases t <;> rfl

theorem truthy_toVal (w : WVal) : Binaryen.truthy (WVal.toVal w) = w.truthy := by
  cases w <;> rfl

theorem ofVal_toVal (w : WVal) : WVal.ofVal? (WVal.toVal w) = some w := by
  cases w <;> rfl

theorem toVal_inj {a b : WVal} (h : WVal.toVal a = WVal.toVal b) : a = b := by
  have := congrArg WVal.ofVal? h
  rwa [ofVal_toVal, ofVal_toVal, Option.some.injEq] at this

theorem map_toVal_inj {as bs : List WVal} (h : as.map WVal.toVal = bs.map WVal.toVal) : as = bs :=
  List.map_injective_iff.mpr (fun _ _ => toVal_inj) h

/-! ## Frames -/

theorem frameOf_local {mi : ModuleInst} {ls : List WVal} {i : Nat} :
    ((frameOf mi ls).locals[i]?).join = (ls[i]?).map WVal.toVal := by
  simp only [frameOf, List.getElem?_map]
  cases ls[i]? <;> rfl

theorem frameOf_setLocal {mi : ModuleInst} {ls : List WVal} {x : LocalIdx} {w : WVal} :
    (frameOf mi ls).setLocal x (WVal.toVal w) = frameOf mi (ls.set x.toNat w) := by
  simp [frameOf, Frame.setLocal, List.map_set]

/-! ## Outcomes -/

/-- Abrupt outcomes and interpreter results. -/
def CorrA {H : Type} (L : List Ar) (R : Ar) (s : Store H) (mi : ModuleInst) {α : Type} :
    Out α → Store H × Frame × Flow → Prop
  | .ok .., _ => False
  | .brk l ls r, x => ∃ junk, x = (s, frameOf mi ls, .brk l (r.toList.map WVal.toVal ++ junk)) ∧
      L[l]? = some (arR r)
  | .ret r, x => ∃ fr junk, x = (s, fr, .ret (r.toList.map WVal.toVal ++ junk)) ∧ R = arR r
  | .trap, x => ∃ fr, x = (s, fr, .trap)

/-- A list outcome and an interpreter result, from stack `stk`. -/
def Corr {H : Type} (L : List Ar) (R : Ar) (s : Store H) (mi : ModuleInst) (stk : List Val) :
    Out (List WVal) → Store H × Frame × Flow → Prop
  | .ok ls P, x => x = (s, frameOf mi ls, .normal ((P.map WVal.toVal).reverse ++ stk))
  | o, x => CorrA L R s mi o x

theorem corrA_cast {H : Type} {L : List Ar} {R : Ar} {s : Store H} {mi : ModuleInst} {α β : Type}
    {o : Out α} (hab : o.Abrupt) {x : Store H × Frame × Flow} :
    CorrA L R s mi (o.cast : Out β) x ↔ CorrA L R s mi o x := by
  cases o <;> simp_all [Out.cast, Out.Abrupt, CorrA]

theorem corr_abrupt {H : Type} {L : List Ar} {R : Ar} {s : Store H} {mi : ModuleInst}
    {stk : List Val} {o : Out (List WVal)} (hab : o.Abrupt) {x : Store H × Frame × Flow} :
    Corr L R s mi stk o x ↔ CorrA L R s mi o x := by
  cases o <;> simp_all [Out.Abrupt, Corr]

/-! ## Typed list executions -/

/-- Left-to-right execution of a list, pushing produced values (in order). -/
inductive ExecT (L : List Ar) (R : Ar) (n : Nat) : List WVal → List Expr → Out (List WVal) → Prop where
  | nil {ls} : ExecT L R n ls [] (.ok ls [])
  | cons {ls ls₁ ls₂ e es r P} : Exec ls e (.ok ls₁ r) → tyE L R n e = some (some (arR r)) →
      ExecT L R n ls₁ es (.ok ls₂ P) → ExecT L R n ls (e :: es) (.ok ls₂ (r.toList ++ P))
  | head {ls e es} {o : Out (Option WVal)} : Exec ls e o → o.Abrupt →
      ExecT L R n ls (e :: es) o.cast
  | tail {ls ls₁ e es r o} : Exec ls e (.ok ls₁ r) → tyE L R n e = some (some (arR r)) →
      ExecT L R n ls₁ es o → o.Abrupt → ExecT L R n ls (e :: es) o

/-- The typing of a list, prefix-closed: after a non-completing element the rest is free. -/
def TyL (L : List Ar) (R : Ar) (n : Nat) : List Expr → Prop
  | [] => True
  | e :: es =>
      match tyE L R n e with
      | some none => True
      | some (some _) => TyL L R n es
      | none => False

theorem tyL_of_tyArgs {L : List Ar} {R : Ar} {n : Nat} :
    ∀ {es : List Expr}, tyArgs L R n es = true → TyL L R n es
  | [], _ => trivial
  | e :: es, h => by
      simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at h
      simp only [TyL, h.1]
      exact tyL_of_tyArgs h.2

theorem tyL_of_tySeq {L : List Ar} {R : Ar} {n : Nat} :
    ∀ {es : List Expr} {a : Option Ar}, tySeq L R n es = some a → TyL L R n es
  | [], _, _ => trivial
  | e :: es, a, h => by
      simp only [tySeq] at h
      simp only [TyL]
      split at h
      · rename_i heq; rw [heq]; trivial
      · rename_i heq; rw [heq]; exact tyL_of_tySeq h
      · rename_i heq; rw [heq]
        split at h
        · rename_i he; simp at he; subst he; trivial
        · cases h
      · cases h

/-- Typed operands produce one value each. -/
theorem execT_args {L : List Ar} {R : Ar} {n : Nat} :
    ∀ {ls : List WVal} {es : List Expr} {o : Out (List WVal)}, tyArgs L R n es = true →
      ExecT L R n ls es o → Args ls es o ∧ (∀ ls' P, o = .ok ls' P → P.length = es.length)
  | _, _, _, _, .nil => ⟨.nil, fun _ _ h => by cases h; rfl⟩
  | _, e :: es, _, h, .cons (r := r) he ht hr => by
      simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at h
      have : arR r = .one := by rw [h.1] at ht; simpa using ht.symm
      cases r with
      | none => simp at this
      | some w =>
          obtain ⟨ha, hl⟩ := execT_args h.2 hr
          exact ⟨.cons he ha, fun _ _ hh => by cases hh; simp [hl _ _ rfl]⟩
  | _, _, _, _, .head he hab => ⟨.head_abrupt he hab, fun _ _ hh => by
      cases ‹Out (Option WVal)› <;> simp_all [Out.cast, Out.Abrupt]⟩
  | _, e :: es, _, h, .tail (r := r) he ht hr hab => by
      simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at h
      have : arR r = .one := by rw [h.1] at ht; simpa using ht.symm
      cases r with
      | none => simp at this
      | some w =>
          obtain ⟨ha, _⟩ := execT_args h.2 hr
          exact ⟨.tail_abrupt he ha hab, fun _ _ hh => by subst hh; exact absurd hab id⟩

/-- A list outcome as a body outcome: the last pushed value is the result. -/
def toOpt : Out (List WVal) → Out (Option WVal)
  | .ok ls P => .ok ls P.getLast?
  | .brk l ls r => .brk l ls r
  | .ret r => .ret r
  | .trap => .trap

theorem toOpt_cast {o : Out (Option WVal)} (hab : o.Abrupt) : toOpt o.cast = o := by
  cases o <;> simp_all [Out.cast, Out.Abrupt, toOpt]

theorem toOpt_abrupt {o : Out (List WVal)} (hab : o.Abrupt) : (toOpt o).Abrupt := by
  cases o <;> simp_all [Out.Abrupt, toOpt]

/-- A typed body: its list execution is a `Seq` run; a completed body pushes
exactly its arity's values. -/
theorem execT_seq {L : List Ar} {R : Ar} {n : Nat} :
    ∀ {ls : List WVal} {es : List Expr} {o : Out (List WVal)} {a : Option Ar},
      tySeq L R n es = some a → ExecT L R n ls es o →
      Seq ls none es (toOpt o) ∧ (∀ ls' P, o = .ok ls' P →
        ∃ b, a = some b ∧ (P = [] ∧ b = .none ∨ ∃ w, P = [w] ∧ b = .one))
  | _, _, _, _, ht, .nil => by
      simp [tySeq] at ht; subst ht
      exact ⟨.nil, fun _ _ hh => by cases hh; exact ⟨.none, rfl, .inl ⟨rfl, rfl⟩⟩⟩
  | _, e :: es, _, a, ht, .cons (r := r) he hte hr => by
      simp only [tySeq, hte] at ht
      cases r with
      | none =>
          obtain ⟨hs, hP⟩ := execT_seq ht hr
          refine ⟨.cons he (by simpa [toOpt] using hs), fun ls' P hh => ?_⟩
          cases hh
          obtain ⟨b, hb, h⟩ := hP _ _ rfl
          exact ⟨b, hb, by simpa using h⟩
      | some w =>
          simp only [arR_some] at ht
          split at ht
          · rename_i hes
            simp at hes; subst hes
            cases hr
            refine ⟨.cons he .nil, fun ls' P hh => ?_⟩
            cases hh
            exact ⟨.one, (Option.some.inj ht).symm, .inr ⟨w, rfl, rfl⟩⟩
          · cases ht
  | _, e :: es, _, a, ht, .head he hab => by
      rw [toOpt_cast hab]
      exact ⟨.abrupt he hab, fun _ _ hh => by
        cases ‹Out (Option WVal)› <;> simp_all [Out.cast, Out.Abrupt]⟩
  | _, e :: es, _, a, ht, .tail (r := r) he hte hr hab => by
      simp only [tySeq, hte] at ht
      cases r with
      | none =>
          obtain ⟨hs, _⟩ := execT_seq ht hr
          exact ⟨.cons he hs, fun _ _ hh => by subst hh; exact absurd hab id⟩
      | some w =>
          simp only [arR_some] at ht
          split at ht
          · rename_i hes
            simp at hes; subst hes
            cases hr; exact absurd hab id
          · cases ht

/-! ## Recognition -/

theorem ofBExprs?_nil {fs : List Expr} (h : ofBExprs? [] = some fs) : fs = [] := by
  simp [ofBExprs?] at h; exact h

theorem ofBExprs?_cons {b : BExpr} {bs : List BExpr} {fs : List Expr}
    (h : ofBExprs? (b :: bs) = some fs) :
    ∃ e fs', fs = e :: fs' ∧ ofBExpr? b = some e ∧ ofBExprs? bs = some fs' := by
  simp only [ofBExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨e, he, fs', hfs, rfl⟩ := h
  exact ⟨e, fs', rfl, he, hfs⟩

theorem ofBExpr?_op {i : Instr} {args : List BExpr} {e : Expr} (h : ofBExpr? (.op i args) = some e) :
    ∃ as, ofBExprs? args = some as ∧ ofInstr? i as = some e := by
  simp only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  exact h

theorem ofBExpr?_block {bt : BlockType} {body : List BExpr} {e : Expr}
    (h : ofBExpr? (.block bt body) = some e) :
    ∃ ty body', ofBlockType? bt = some ty ∧ ofBExprs? body = some body' ∧ e = .block ty body' := by
  simp only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ty, hty, body', hb, rfl⟩ := h
  exact ⟨ty, body', hty, hb, rfl⟩

theorem ofBExpr?_loop {bt : BlockType} {body : List BExpr} {e : Expr}
    (h : ofBExpr? (.loop bt body) = some e) :
    ∃ ty body', ofBlockType? bt = some ty ∧ ofBExprs? body = some body' ∧ e = .loop ty body' := by
  simp only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ty, hty, body', hb, rfl⟩ := h
  exact ⟨ty, body', hty, hb, rfl⟩

theorem ofBExpr?_if {bt : BlockType} {c t el : List BExpr} {e : Expr}
    (h : ofBExpr? (.if_ bt c t el) = some e) :
    ∃ cb ty c' t' e', c = [cb] ∧ ofBlockType? bt = some ty ∧ ofBExpr? cb = some c' ∧
      ofBExprs? t = some t' ∧ ofBExprs? el = some e' ∧ e = .if_ ty c' t' e' := by
  match c, h with
  | [cb], h =>
      simp only [ofBExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ty, hty, c', hc, t', ht, e', he, rfl⟩ := h
      exact ⟨cb, ty, c', t', e', rfl, hty, hc, ht, he, rfl⟩
  | [], h => simp [ofBExpr?] at h
  | _ :: _ :: _, h => simp [ofBExpr?] at h

theorem ofBExpr?_try {bt : BlockType} {cs : List Catch} {body : List BExpr} {e : Expr} :
    ofBExpr? (.tryTable bt cs body) = some e → False := by
  simp [ofBExpr?]

theorem ofBlockType?_arity {f : Frame} {bt : BlockType} {ty : Option IntType}
    (h : ofBlockType? bt = some ty) :
    Binaryen.arity f bt = some (0, if ty.isSome then 1 else 0) := by
  cases bt with
  | empty => simp [ofBlockType?] at h; subst h; rfl
  | value t => simp [ofBlockType?, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | typeIdx => simp [ofBlockType?] at h

end Silmaril.Proofs.Wasm.SSA.Native.Bwd
