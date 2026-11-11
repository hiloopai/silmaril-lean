module

public import Silmaril.Proofs.Wasm.SSA.Native.FwdOp

/-!
# Native adequacy, forward direction: the simulation

`Corr` relates a fragment outcome to an interpreter result: normal outcomes
push their values on the stack and keep the frame of the new locals; branches
and returns carry their value on top of an arbitrary stack (with the target's
arity recorded); traps keep nothing. `FE`/`FA`/`FS` are the simulation
statements for expressions, operands and bodies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType)
open Silmaril.Wasm.Binaryen (BExpr evalFlat Flow Eval arity Next)
open Silmaril.Wasm.Execution.Core (Val Store Frame ModuleInst)
open Silmaril.Wasm.SSA

/-- Values of an optional result. -/
def vOf (r : Option WVal) : List Val := r.toList.map WVal.toVal

/-- The arity of an optional result. -/
def arR (r : Option WVal) : Ar := if r.isSome then .one else .none

section
variable {H : Type} (s : Store H) (mi : ModuleInst)

/-- Outcome correspondence. -/
def Corr {α : Type} (push : α → List Val) (L : List Ar) (R : Ar) (stk : List Val) :
    Out α → Store H × Frame × Flow → Prop
  | .ok ls a, x => x = (s, frameOf mi ls, .normal (push a ++ stk))
  | .brk l ls r, x => ∃ junk, x = (s, frameOf mi ls, .brk l (vOf r ++ junk)) ∧ L[l]? = some (arR r)
  | .ret r, x => ∃ fr junk, x = (s, fr, .ret (vOf r ++ junk)) ∧ R = arR r
  | .trap, x => ∃ fr, x = (s, fr, .trap)

/-- A normal outcome has the arity the check found. -/
def ArOK (ta : Option Ar) : Out (Option WVal) → Prop
  | .ok _ r => ta = some (arR r)
  | _ => True

/-- Simulation of an expression. -/
def FE (ls : List WVal) (e : Expr) (o : Out (Option WVal)) : Prop :=
  ∀ L R n b stk ta, ofBExpr? b = some e → tyE L R n e = some ta →
    ∃ x, Eval s (frameOf mi ls) stk [b] x ∧ Corr s mi vOf L R stk o x ∧ ArOK ta o

/-- Simulation of operands. -/
def FA (ls : List WVal) (es : List Expr) (o : Out (List WVal)) : Prop :=
  ∀ L R n bs stk, ofBExprs? bs = some es → tyArgs L R n es = true →
    ∃ x, Eval s (frameOf mi ls) stk bs x ∧ Corr s mi (fun vs => vs.reverse.map WVal.toVal) L R stk o x

/-- Simulation of a body (from no carried result). -/
def FS (ls : List WVal) (r : Option WVal) (es : List Expr) (o : Out (Option WVal)) : Prop :=
  r = none → ∀ L R n bs stk ta, ofBExprs? bs = some es → tySeq L R n es = some ta →
    ∃ x, Eval s (frameOf mi ls) stk bs x ∧ Corr s mi vOf L R stk o x ∧ ArOK ta o

end

/-! ## Generic facts -/

section
variable {H : Type} {s : Store H} {mi : ModuleInst}

theorem corr_abrupt {α : Type} {push : α → List Val} {L : List Ar} {R : Ar} {stk : List Val}
    {o : Out α} {x : Store H × Frame × Flow} (h : Corr s mi push L R stk o x) (hab : o.Abrupt) :
    ¬ x.2.2.IsNormal := by
  cases o with
  | ok => exact hab.elim
  | brk => obtain ⟨_, rfl, _⟩ := h; exact fun h => h
  | ret => obtain ⟨_, _, rfl, _⟩ := h; exact fun h => h
  | trap => obtain ⟨_, rfl⟩ := h; exact fun h => h

theorem corr_cast {α β : Type} {push : α → List Val} {push' : β → List Val} {L : List Ar} {R : Ar}
    {stk : List Val} {o : Out α} {x : Store H × Frame × Flow} (hab : o.Abrupt)
    (h : Corr s mi push L R stk o x) : Corr s mi push' L R stk o.cast x := by
  cases o with
  | ok => exact hab.elim
  | _ => exact h

theorem corr_push {α : Type} {push push' : α → List Val} {L : List Ar} {R : Ar}
    {stk : List Val} {o : Out α} {x : Store H × Frame × Flow} (hab : o.Abrupt)
    (h : Corr s mi push L R stk o x) : Corr s mi push' L R stk o x := by
  cases o with
  | ok => exact hab.elim
  | _ => exact h

theorem eval_cons_normal {f : Frame} {stk : List Val} {b : BExpr} {bs : List BExpr}
    {s' : Store H} {f' : Frame} {stk' : List Val} {r : Store H × Frame × Flow}
    (h₁ : Eval s f stk [b] (s', f', .normal stk')) (h₂ : Eval s' f' stk' bs r) :
    Eval s f stk (b :: bs) r :=
  Silmaril.Wasm.Binaryen.eval_cons_iff.mpr ⟨_, h₁, h₂⟩

theorem eval_cons_stop {f : Frame} {stk : List Val} {b : BExpr} {bs : List BExpr}
    {x : Store H × Frame × Flow} (h₁ : Eval s f stk [b] x) (hx : ¬ x.2.2.IsNormal) :
    Eval s f stk (b :: bs) x := by
  obtain ⟨s', f', fl⟩ := x
  exact Silmaril.Wasm.Binaryen.eval_cons_iff.mpr ⟨_, h₁,
    (Silmaril.Wasm.Binaryen.next_of_not_normal hx).mpr rfl⟩

/-- A flat instruction after its operands. -/
theorem eval_op {f : Frame} {stk : List Val} {i : Instr} {bargs : List BExpr}
    (hi : ∀ x, i ≠ .call x) {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    (hargs : Eval s f stk bargs (s₁, f₁, .normal stk₁)) {r : Store H × Frame × Flow}
    (hflat : evalFlat s₁ f₁ stk₁ i = some r) : Eval s f stk [.op i bargs] r := by
  obtain ⟨s₂, f₂, fl⟩ := r
  cases fl with
  | normal stk₂ => exact .opOk hi hargs hflat .nil
  | _ => exact .opStop hi hargs hflat (fun h => h)

theorem eval_op_abrupt {f : Frame} {stk : List Val} {i : Instr} {bargs : List BExpr}
    {x : Store H × Frame × Flow} (hargs : Eval s f stk bargs x) (hx : ¬ x.2.2.IsNormal) :
    Eval s f stk [.op i bargs] x := by
  obtain ⟨s', f', fl⟩ := x
  exact .argsAbort hargs hx

end

theorem arity_of {f : Frame} {bt : BlockType} {ty : Option IntType}
    (h : ofBlockType? bt = some ty) : arity f bt = some (0, if ty.isSome then 1 else 0) := by
  cases bt with
  | empty => simp [ofBlockType?] at h; subst h; rfl
  | value v =>
      simp only [ofBlockType?, Option.map_eq_some_iff] at h
      obtain ⟨t, -, rfl⟩ := h
      rfl
  | typeIdx => simp [ofBlockType?] at h

theorem take_vOf {ty : Option IntType} {r : Option WVal} (hok : BlockOk ty r) (junk : List Val) :
    (vOf r ++ junk).take (if ty.isSome then 1 else 0) = vOf (blockRes ty r) := by
  cases ty with
  | none => simp [blockRes, vOf]
  | some t =>
      obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hok rfl)
      simp [blockRes, vOf]

theorem arOf_blockRes {ty : Option IntType} {r : Option WVal} (hok : BlockOk ty r) :
    arOf ty = arR (blockRes ty r) := by
  cases ty with
  | none => rfl
  | some t =>
      obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hok rfl)
      rfl

theorem arFits_inv {a : Ar} {r : Option (Option Ar)} (h : arFits a r = true) :
    ∃ t, r = some t ∧ (t = some a ∨ t = none) := by
  match r, h with
  | some (some b), h => simp [arFits] at h; exact ⟨_, rfl, .inl (by rw [h])⟩
  | some none, _ => exact ⟨_, rfl, .inr rfl⟩

theorem cast_ne_ok {α β : Type} (o : Out α) (ls : List WVal) (a : β) : (o.cast : Out β) ≠ .ok ls a := by
  cases o <;> simp [Out.cast]

theorem args_length {ls ls' : List WVal} : ∀ {es : List Expr} {vs : List WVal},
    Args ls es (.ok ls' vs) → vs.length = es.length := by
  intro es
  induction es generalizing ls with
  | nil =>
      intro vs h
      generalize ho : (Out.ok ls' vs : Out (List WVal)) = o at h
      cases h; cases ho; rfl
  | cons e es ih =>
      intro vs h
      generalize ho : (Out.ok ls' vs : Out (List WVal)) = o at h
      cases h with
      | cons _ ha => cases ho; simp [ih ha]
      | head_abrupt _ _ => exact absurd ho.symm (cast_ne_ok _ _ _)
      | tail_abrupt _ _ hab => subst ho; exact hab.elim

theorem ofBExprs?_single {bs : List BExpr} {e : Expr} (h : ofBExprs? bs = some [e]) :
    ∃ b, bs = [b] ∧ ofBExpr? b = some e := by
  obtain ⟨b, bs', rfl, hb, hbs⟩ := ofBExprs?_cons h
  rw [ofBExprs?_nil hbs]; exact ⟨b, rfl, hb⟩

end Silmaril.Proofs.Wasm.SSA.Native
