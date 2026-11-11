module

public import Silmaril.Proofs.Wasm.SSA.Native.FwdSim

/-! # Native adequacy, forward direction: constructs -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType)
open Silmaril.Wasm.Binaryen (BExpr evalFlat Flow Eval arity Next)
open Silmaril.Wasm.Execution.Core (Val Store Frame ModuleInst)
open Silmaril.Wasm.SSA

variable {H : Type} {s : Store H} {mi : ModuleInst}

/-- Unfold an arity check whose answer is `some ta`. -/
theorem ite_some_inv {c : Prop} [Decidable c] {a ta : Option Ar} (h : (if c then some a else none) = some ta) :
    c ∧ ta = a := by
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · cases h

theorem flat_of {b : BExpr} {e : Expr} (hb : ofBExpr? b = some e)
    (hs : ∀ ty body, e ≠ .block ty body) (hl : ∀ ty body, e ≠ .loop ty body)
    (hi : ∀ ty c t el, e ≠ .if_ ty c t el) :
    ∃ i bargs args, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ ofInstr? i args = some e :=
  ofBExpr?_flat hb hs hl hi

/-! ## Operators -/

theorem fe_op {ls ls' : List WVal} {o : Op} {args : List Expr} {vs : List WVal} {w : WVal}
    (ha : FA s mi ls args (.ok ls' vs)) (hev : o.eval vs = some (.val w)) :
    FE s mi ls (.op o args) (.ok ls' (some w)) := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨hc, rfl⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hn, -⟩, htys⟩ := hc
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, hnc, hflat⟩ := flat_op s hi hn
  obtain ⟨x, hx, rfl⟩ := ha L R n bargs stk hba htys
  exact ⟨_, eval_op hnc hx (hflat vs _ _ stk hev), by simp [Corr, resFlow, vOf], rfl⟩

theorem fe_op_trap {ls ls' : List WVal} {o : Op} {args : List Expr} {vs : List WVal}
    (ha : FA s mi ls args (.ok ls' vs)) (hev : o.eval vs = some .trap) :
    FE s mi ls (.op o args) .trap := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨hc, rfl⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hn, -⟩, htys⟩ := hc
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, hnc, hflat⟩ := flat_op s hi hn
  obtain ⟨x, hx, rfl⟩ := ha L R n bargs stk hba htys
  exact ⟨_, eval_op hnc hx (hflat vs _ _ stk hev), ⟨_, rfl⟩, trivial⟩

/-- Operand lists that stop abruptly stop the whole flat instruction. -/
theorem fe_args_abrupt {ls : List WVal} {e : Expr} {args : List Expr} {out : Out (List WVal)}
    (ha : FA s mi ls args out) (hab : out.Abrupt)
    (hshape : ∀ b L R n ta, ofBExpr? b = some e → tyE L R n e = some ta →
      ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true) :
    FE s mi ls e out.cast := by
  intro L R n b stk ta hb hty
  obtain ⟨i, bargs, rfl, hba, htys⟩ := hshape b L R n ta hb hty
  obtain ⟨x, hx, hc⟩ := ha L R n bargs stk hba htys
  refine ⟨x, eval_op_abrupt hx (corr_abrupt hc hab), corr_cast hab hc, ?_⟩
  cases out with
  | ok => exact hab.elim
  | _ => trivial

theorem shape_op {o : Op} {args : List Expr} : ∀ b L R n ta, ofBExpr? b = some (.op o args) →
    tyE L R n (.op o args) = some ta →
    ∃ i bargs, b = .op i bargs ∧ ofBExprs? bargs = some args ∧ tyArgs L R n args = true := by
  intro b L R n ta hb hty
  unfold tyE at hty
  obtain ⟨hc, -⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hn, -⟩, htys⟩ := hc
  obtain ⟨i, bargs, args', rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, -, -⟩ := flat_op (H := Unit) {} hi hn
  exact ⟨i, bargs, rfl, hba, htys⟩

/-! ## Locals, `drop`, `nop`, `unreachable` -/

theorem fe_localGet {ls : List WVal} {i : Nat} {v : WVal} (h : ls[i]? = some v) :
    FE s mi ls (.localGet i) (.ok ls (some v)) := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨-, rfl⟩ := ite_some_inv hty
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨x, rfl, rfl, rfl⟩ := ofInstr?_localGet hi
  rw [ofBExprs?_nil hba]
  refine ⟨_, eval_op (fun _ h => Instr.noConfusion h) .nil ?_, rfl, rfl⟩
  simp [evalFlat, frameOf, h, vOf]

theorem fe_localSet {ls ls' : List WVal} {i : Nat} {e : Expr} {v : WVal}
    (he : FE s mi ls e (.ok ls' (some v))) :
    FE s mi ls (.localSet i e) (.ok (ls'.set i v) none) := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨hc, rfl⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨-, hte⟩ := hc
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨x, rfl, rfl, rfl⟩ := ofInstr?_localSet hi
  obtain ⟨be, rfl, hbe⟩ := ofBExprs?_single hba
  obtain ⟨y, hy, rfl, -⟩ := he L R n be stk _ hbe hte
  refine ⟨_, eval_op (fun _ h => Instr.noConfusion h) hy ?_, rfl, rfl⟩
  simp [evalFlat, vOf, Silmaril.Wasm.Execution.Core.Frame.setLocal, frameOf, List.map_set]

theorem fe_localTee {ls ls' : List WVal} {i : Nat} {e : Expr} {v : WVal}
    (he : FE s mi ls e (.ok ls' (some v))) :
    FE s mi ls (.localTee i e) (.ok (ls'.set i v) (some v)) := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨hc, rfl⟩ := ite_some_inv hty
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨-, hte⟩ := hc
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨x, rfl, rfl, rfl⟩ := ofInstr?_localTee hi
  obtain ⟨be, rfl, hbe⟩ := ofBExprs?_single hba
  obtain ⟨y, hy, rfl, -⟩ := he L R n be stk _ hbe hte
  refine ⟨_, eval_op (fun _ h => Instr.noConfusion h) hy ?_, rfl, rfl⟩
  simp [evalFlat, vOf, Silmaril.Wasm.Execution.Core.Frame.setLocal, frameOf, List.map_set]

theorem fe_drop {ls ls' : List WVal} {e : Expr} {r : Option WVal}
    (he : FE s mi ls e (.ok ls' r)) : FE s mi ls (.drop e) (.ok ls' none) := by
  intro L R n b stk ta hb hty
  unfold tyE at hty
  obtain ⟨hte, rfl⟩ := ite_some_inv hty
  simp only [beq_iff_eq] at hte
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, rfl⟩ := ofInstr?_drop hi
  obtain ⟨be, rfl, hbe⟩ := ofBExprs?_single hba
  obtain ⟨y, hy, rfl, har⟩ := he L R n be stk _ hbe hte
  have : r.isSome := by
    simp only [ArOK, arR, Option.some.injEq] at har; split at har <;> simp_all
  obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp this
  refine ⟨_, eval_op (fun _ h => Instr.noConfusion h) hy ?_, rfl, rfl⟩
  simp [evalFlat, vOf]

theorem fe_nop {ls : List WVal} : FE s mi ls .nop (.ok ls none) := by
  intro L R n b stk ta hb hty
  simp only [tyE, Option.some.injEq] at hty; subst hty
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, rfl⟩ := ofInstr?_nop hi
  rw [ofBExprs?_nil hba]
  exact ⟨_, eval_op (r := (s, frameOf mi ls, .normal stk)) (fun _ h => Instr.noConfusion h) .nil rfl,
    rfl, rfl⟩

theorem fe_unreachable {ls : List WVal} : FE s mi ls .unreachable .trap := by
  intro L R n b stk ta hb hty
  obtain ⟨ins, bargs, args, rfl, hba, hi⟩ :=
    flat_of hb (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨rfl, rfl⟩ := ofInstr?_unreachable hi
  rw [ofBExprs?_nil hba]
  exact ⟨_, eval_op (r := (s, frameOf mi ls, .trap)) (fun _ h => Instr.noConfusion h) .nil rfl,
    ⟨_, rfl⟩, trivial⟩

/-- A sub-expression that stops abruptly stops a flat instruction with that one operand. -/
theorem fe_one_abrupt {ls : List WVal} {e e' : Expr} {out : Out (Option WVal)}
    (he : FE s mi ls e out) (hab : out.Abrupt)
    (hshape : ∀ b L R n ta, ofBExpr? b = some e' → tyE L R n e' = some ta →
      ∃ i be, b = .op i [be] ∧ ofBExpr? be = some e ∧ ∃ te, tyE L R n e = some te) :
    FE s mi ls e' out := by
  intro L R n b stk ta hb hty
  obtain ⟨i, be, rfl, hbe, te, hte⟩ := hshape b L R n ta hb hty
  obtain ⟨x, hx, hc, -⟩ := he L R n be stk te hbe hte
  refine ⟨x, eval_op_abrupt hx (corr_abrupt hc hab), hc, ?_⟩
  cases out with
  | ok => exact hab.elim
  | _ => trivial

/-- The operand of a typed `localSet`/`localTee` produces one value. -/
private theorem local_arg_ty {L : List Ar} {R : Ar} {n i : Nat} {e : Expr} {a ta : Option Ar}
    (h : (if (decide (i < n) && tyE L R n e == some (some .one)) then some a else none) = some ta) :
    tyE L R n e = some (some .one) := by
  have hc : (decide (i < n) && tyE L R n e == some (some .one)) = true := (ite_some_inv h).1
  have hc' : i < n ∧ tyE L R n e = some (some .one) := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hc
  exact hc'.2

/-- The operand of `localSet`/`localTee`/`drop` (selected by `k`, as in `shape_one`):
the instruction has that one operand, and the operand produces one value. -/
private theorem shape_one_arg {i₀ : Nat} {e e' : Expr} {ins : Instr} {args : List Expr}
    {L : List Ar} {R : Ar} {n : Nat} {ta : Option Ar} (k : Nat)
    (he' : e' = (match k with | 0 => .localSet i₀ e | 1 => .localTee i₀ e | _ => .drop e))
    (hi : ofInstr? ins args = some e') (hty : tyE L R n e' = some ta) :
    args = [e] ∧ tyE L R n e = some (some .one) := by
  match k, he' with
  | 0, he' =>
      have he₀ : e' = .localSet i₀ e := he'
      have hty' : tyE L R n (.localSet i₀ e) = some ta := he₀ ▸ hty
      obtain ⟨_, -, hargs, -⟩ := ofInstr?_localSet (he₀ ▸ hi)
      exact ⟨hargs, local_arg_ty hty'⟩
  | 1, he' =>
      have he₀ : e' = .localTee i₀ e := he'
      have hty' : tyE L R n (.localTee i₀ e) = some ta := he₀ ▸ hty
      obtain ⟨_, -, hargs, -⟩ := ofInstr?_localTee (he₀ ▸ hi)
      exact ⟨hargs, local_arg_ty hty'⟩
  | _ + 2, he' =>
      have he₀ : e' = .drop e := he'
      have hty' : tyE L R n (.drop e) = some ta := he₀ ▸ hty
      have hc : (tyE L R n e == some (some .one)) = true := (ite_some_inv hty').1
      have hte : tyE L R n e = some (some .one) := by simpa only [beq_iff_eq] using hc
      exact ⟨(ofInstr?_drop (he₀ ▸ hi)).2, hte⟩

theorem shape_one {i₀ : Nat} {e : Expr} (k : Nat) (e' : Expr)
    (he' : e' = (match k with | 0 => .localSet i₀ e | 1 => .localTee i₀ e | _ => .drop e)) :
    ∀ b L R n ta, ofBExpr? b = some e' → tyE L R n e' = some ta →
      ∃ i be, b = .op i [be] ∧ ofBExpr? be = some e ∧ ∃ te, tyE L R n e = some te := by
  intro b L R n ta hb hty
  have hs : ∀ ty body, e' ≠ .block ty body := by
    rw [he']; split <;> exact fun _ _ h => nomatch h
  have hl : ∀ ty body, e' ≠ .loop ty body := by
    rw [he']; split <;> exact fun _ _ h => nomatch h
  have hif : ∀ ty c t el, e' ≠ .if_ ty c t el := by
    rw [he']; split <;> exact fun _ _ _ _ h => nomatch h
  obtain ⟨ins, bargs, args, hbeq, hba, hi⟩ : ∃ ins bargs args, b = .op ins bargs ∧
      ofBExprs? bargs = some args ∧ ofInstr? ins args = some e' := flat_of hb hs hl hif
  obtain ⟨hargs, hte⟩ : args = [e] ∧ tyE L R n e = some (some .one) :=
    shape_one_arg k he' hi hty
  obtain ⟨be, hbargs, hbe⟩ : ∃ be, bargs = [be] ∧ ofBExpr? be = some e :=
    ofBExprs?_single (hargs ▸ hba)
  exact ⟨ins, be, by rw [hbeq, hbargs], hbe, _, hte⟩

end Silmaril.Proofs.Wasm.SSA.Native
