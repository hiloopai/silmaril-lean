module

public import Silmaril.Wasm.Logic.V1.Judgement.Defs

/-!
# Soundness of the control-flow proof rules

Figure 9 of Watt et al. The `[block]` and `[loop]` rules are where the logic's
treatment of WebAssembly's structured control flow meets the semantics: a break
to a `block` leaves it, so the labels field is extended with the block's
postcondition, whereas a break to a `loop` starts the next iteration, so it is
extended with the loop's precondition, which is therefore the loop invariant.

`valid_loop` is the one rule whose soundness is a recursion on the execution:
its hypothesis `loop` is the conclusion at every strictly smaller derivation
height, supplied by the induction in `Silmaril.Proofs.Wasm.Logic.V1.Soundness`.

The stack-length premises `pre` and `post` replace the paper's `Pₙ`/`Qₘ`
notation; in WebAssembly 1.0 a block takes no operands, so `n` is always 0.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert} {P Q : Assert}

/-- An `i32` runtime value determines its bit pattern. -/
private theorem i32_inj {x y : BitVec 32} (eq : Value.int .i32 x = Value.int .i32 y) : x = y := by
  injection eq

/-- Two suffixes of one and the same list that have the same length are equal.
This is what pins down the values transferred by a branch: the arity recorded by
`BigStepN.labelBrZero` and the `Assert.StackLen` premise give the two lengths,
and `Satisfies` only says that the transferred values are *some* suffix. -/
private theorem suffix_eq {α : Type*} {xs ys zs ws : List α} (eq : xs ++ zs = ys ++ ws)
    (len : zs.length = ws.length) : zs = ws := (List.append_inj' eq len).2

/-- Inversion for a `br` instruction: the only rule is `BigStepN.br`. -/
private theorem br_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value} {l : LabelIdx}
    {o : Outcome H} (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.br l]) o) :
    o = ⟨s, f, .br l us⟩ := by
  cases run with
  | br => rfl
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for a `return` instruction. -/
private theorem return_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {o : Outcome H} (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.return_]) o) :
    o = ⟨s, f, .ret us⟩ := by
  cases run with
  | return_ => rfl
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for a `block` instruction: the only rule is `BigStepN.block`. -/
private theorem block_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr} {o : Outcome H}
    (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.block bt body]) o) :
    ∃ k, k + 1 ≤ m ∧
      BigStepN host k s f us [.label bt.toList.length [] (expression body)] o := by
  cases run with
  | block => rename_i rest; exact ⟨_, Nat.le_refl _, rest⟩
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for a `loop` instruction. -/
private theorem loop_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr} {o : Outcome H}
    (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.loop bt body]) o) :
    ∃ k, k + 1 ≤ m ∧
      BigStepN host k s f us [.label 0 [.loop bt body] (expression body)] o := by
  cases run with
  | loop => rename_i rest; exact ⟨_, Nat.le_refl _, rest⟩
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for an `if` instruction: the condition is the topmost operand. -/
private theorem if_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {bt : Silmaril.Wasm.V1.BlockType} {left right : Silmaril.Wasm.V1.Expr} {o : Outcome H}
    (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.if_ bt left right]) o) :
    ∃ (k : Nat) (us' : List Value) (cc : BitVec 32), k + 1 ≤ m ∧
      us = us' ++ [Value.int .i32 cc] ∧
      ((cc = 0 ∧ BigStepN host k s f us' (expression [Silmaril.Wasm.V1.Instr.block bt right]) o) ∨
        (cc ≠ 0 ∧ BigStepN host k s f us' (expression [Silmaril.Wasm.V1.Instr.block bt left]) o)) := by
  cases run with
  | ifZero => rename_i rest; exact ⟨_, _, 0, Nat.le_refl _, rfl, Or.inl ⟨rfl, rest⟩⟩
  | ifNonzero =>
    rename_i nonzero rest
    exact ⟨_, _, _, Nat.le_refl _, rfl, Or.inr ⟨nonzero, rest⟩⟩
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for a `br_if` instruction. -/
private theorem brIf_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {l : LabelIdx} {o : Outcome H}
    (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.brIf l]) o) :
    ∃ (k : Nat) (us' : List Value) (cc : BitVec 32), k + 1 ≤ m ∧
      us = us' ++ [Value.int .i32 cc] ∧
      ((cc = 0 ∧ BigStepN host k s f us' [] o) ∨
        (cc ≠ 0 ∧ BigStepN host k s f us' (expression [Silmaril.Wasm.V1.Instr.br l]) o)) := by
  cases run with
  | brIfZero => rename_i rest; exact ⟨_, _, 0, Nat.le_refl _, rfl, Or.inl ⟨rfl, rest⟩⟩
  | brIfNonzero =>
    rename_i nonzero rest
    exact ⟨_, _, _, Nat.le_refl _, rfl, Or.inr ⟨nonzero, rest⟩⟩
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Inversion for a `br_table` instruction. -/
private theorem brTable_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value}
    {ls : List LabelIdx} {dflt : LabelIdx} {o : Outcome H}
    (run : BigStepN host m s f us (expression [Silmaril.Wasm.V1.Instr.brTable ls dflt]) o) :
    ∃ (k : Nat) (us' : List Value) (cc : BitVec 32), k + 1 ≤ m ∧
      us = us' ++ [Value.int .i32 cc] ∧
      BigStepN host k s f us' (expression [Silmaril.Wasm.V1.Instr.br (ls[cc.toNat]?.getD dflt)]) o := by
  cases run with
  | brTable => rename_i rest; exact ⟨_, _, _, Nat.le_refl _, rfl, rest⟩
  | plain => rename_i step _; cases step
  | plainTrap => rename_i step; cases step

/-- Case analysis on the execution of a single `label` administrative
instruction: it exits normally, a branch targets it, a branch passes it, a
return passes it, or it traps. -/
private theorem label_inv {m : Nat} {s : Store H} {f : Frame} {us : List Value} {ar : Nat}
    {cont : Silmaril.Wasm.V1.Expr} {body : List Admin} {o : Outcome H}
    (run : BigStepN host m s f us [.label ar cont body] o) :
    ∃ (k : Nat) (s' : Store H) (f' : Frame), k + 1 ≤ m ∧
      ((∃ ws, BigStepN host k s f [] body ⟨s', f', .normal ws⟩ ∧
          BigStepN host k s' f' (us ++ ws) [] o) ∨
        (∃ (l : LabelIdx) (extra ws : List Value),
            BigStepN host k s f [] body ⟨s', f', .br l (extra ++ ws)⟩ ∧ l.toNat = 0 ∧
              ws.length = ar ∧ BigStepN host k s' f' (us ++ ws) (expression cont) o) ∨
        (∃ (l : LabelIdx) (ws : List Value),
            BigStepN host k s f [] body ⟨s', f', .br l ws⟩ ∧ l.toNat ≠ 0 ∧
              o = ⟨s', f', .br (lowerLabel l) (us ++ ws)⟩) ∨
        (∃ ws, BigStepN host k s f [] body ⟨s', f', .ret ws⟩ ∧
            o = ⟨s', f', .ret (us ++ ws)⟩) ∨
        (BigStepN host k s f [] body ⟨s', f', .trap⟩ ∧ o = ⟨s', f', .trap⟩)) := by
  cases run with
  | labelNormal =>
    rename_i innerRun restRun
    exact ⟨_, _, _, Nat.le_refl _, Or.inl ⟨_, innerRun, restRun⟩⟩
  | labelBrZero =>
    rename_i htarget harity innerRun restRun
    exact ⟨_, _, _, Nat.le_refl _,
      Or.inr (Or.inl ⟨_, _, _, innerRun, htarget, harity, by simpa using restRun⟩)⟩
  | labelBrSucc =>
    rename_i houter innerRun
    exact ⟨_, _, _, Nat.le_refl _, Or.inr (Or.inr (Or.inl ⟨_, _, innerRun, houter, rfl⟩))⟩
  | labelRet =>
    rename_i innerRun
    exact ⟨_, _, _, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl ⟨_, innerRun, rfl⟩)))⟩
  | labelTrap =>
    rename_i innerRun
    exact ⟨_, _, _, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inr ⟨innerRun, rfl⟩)))⟩

/-- The `[br]` rule: the precondition is the targeted label's assertion, and the
postcondition is free because the code after a branch is unreachable. -/
theorem valid_br (l : LabelIdx) (target : L[l.toNat]? = some P) :
    Valid host n F L R P [.br l] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain rfl := br_inv run
  exact ⟨h, ρ, disj, reify, fun _ _ => rfl, P, vf, vs, target, rfl, hpre⟩

/-- The `[return]` rule. -/
theorem valid_return (target : R = some P) : Valid host n F L R P [.return_] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain rfl := return_inv run
  exact ⟨h, ρ, disj, reify, fun _ _ => rfl, P, vf, vs, target, rfl, hpre⟩

/-- A branch past the innermost label, seen from outside it: the label index drops
by one and the enclosing operands come along. -/
private theorem satisfies_lower {X Q Q' : Assert} {ρ : Sto} {vf ws : List Value} {h : AHeap}
    {l : LabelIdx} (houter : l.toNat ≠ 0) (sat : Satisfies (X :: L) R Q' ρ [] h (.br l ws)) :
    Satisfies L R Q ρ vf h (.br (lowerLabel l) (vf ++ ws)) := by
  obtain ⟨P', extra, ws', hidx, hws, hP⟩ := sat
  obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
  have hidx' : L[(lowerLabel l).toNat]? = some P' := by
    rw [show (lowerLabel l).toNat = j from by show l.toNat - 1 = j; omega]
    simpa only [hj, List.getElem?_cons_succ] using hidx
  exact ⟨P', vf ++ extra, ws', hidx', by rw [hws, List.append_assoc], hP⟩

/-- A return through a label, seen from outside it. -/
private theorem satisfies_ret {X Q Q' : Assert} {ρ : Sto} {vf ws : List Value} {h : AHeap}
    (sat : Satisfies (X :: L) R Q' ρ [] h (.ret ws)) :
    Satisfies L R Q ρ vf h (.ret (vf ++ ws)) := by
  obtain ⟨R', extra, ws', hR, hws, hr⟩ := sat
  exact ⟨R', vf ++ extra, ws', hR, by rw [hws, List.append_assoc], hr⟩

/-- A label body that fell through, seen from outside the label. -/
private theorem satisfies_normal {L' : List Assert} {R' : Option Assert} {Q : Assert} {ρ : Sto} {vf ws : List Value} {h : AHeap}
    (sat : Satisfies L' R' Q ρ [] h (.normal ws)) : Satisfies L R Q ρ vf h (.normal (vf ++ ws)) := by
  obtain ⟨ws', hws, hQ⟩ := sat
  have hws' : ws' = ws := by simpa using hws.symm
  exact ⟨ws, rfl, hws' ▸ hQ⟩

/-- The `[block]` rule: a break to the block exits it, so the labels field is
extended with the block's postcondition. -/
theorem valid_block (bt : Silmaril.Wasm.V1.BlockType) (body : Silmaril.Wasm.V1.Expr) (pre : Assert.StackLen P 0)
    (post : Assert.StackLen Q bt.toList.length)
    (inner : Valid host n F (Q :: L) R P body Q) :
    Valid host n F L R P [.block bt body] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain rfl : vs = [] := List.length_eq_zero_iff.mp (pre ρ vs h hpre)
  have run' : BigStepN host n s f vf (expression [.block bt body]) o := by
    simpa only [List.append_nil] using run
  obtain ⟨k₀, hk₀, run₁⟩ := block_inv run'
  obtain ⟨k, s', f', hk, hcase⟩ := label_inv run₁
  have hkn : k ≤ n := by omega
  rcases hcase with ⟨ws, innerRun, restRun⟩ |
    ⟨l, extra, ws, innerRun, htarget, harity, restRun⟩ |
    ⟨l, ws, innerRun, houter, rfl⟩ | ⟨ws, innerRun, rfl⟩ | ⟨innerRun, rfl⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner s f ρ [] [] h hf _ hpre disj reify (innerRun.mono hkn)
    obtain rfl : o = ⟨s', f', .normal (vf ++ ws)⟩ := restRun.nil_inv
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_normal sat₁⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, P', _pre, ws', hidx, hws, hP⟩ :=
      inner s f ρ [] [] h hf _ hpre disj reify (innerRun.mono hkn)
    obtain rfl : Q = P' := by
      simpa only [htarget, List.getElem?_cons_zero, Option.some.injEq] using hidx
    obtain rfl : ws = ws' := suffix_eq hws (by rw [harity, post ρ₁ ws' h₁ hP])
    obtain rfl : o = ⟨s', f', .normal (vf ++ ws)⟩ := restRun.nil_inv
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, ws, rfl, hP⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner s f ρ [] [] h hf _ hpre disj reify (innerRun.mono hkn)
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_lower houter sat₁⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner s f ρ [] [] h hf _ hpre disj reify (innerRun.mono hkn)
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_ret sat₁⟩
  · obtain ⟨_, _, _, _, _, sat₁⟩ :=
      inner s f ρ [] [] h hf _ hpre disj reify (innerRun.mono hkn)
    exact (sat₁ : False).elim

/-- The agreement conjunct across one more loop iteration. -/
private theorem agree_loop {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr} {ρ ρ₁ ρ₂ : Sto}
    (agree₁ : ∀ x, x ∉ Expr.modified body → ρ₁ x = ρ x)
    (agree₂ : ∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.loop bt body] → ρ₂ x = ρ₁ x) :
    ∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.loop bt body] → ρ₂ x = ρ x := by
  intro x hx
  have hx' : x ∉ Expr.modified body := by
    simpa only [Expr.modified_single, Instr.modified_loop] using hx
  exact (agree₂ x hx).trans (agree₁ x hx')

/-- The `[loop]` rule: a break to the loop starts the next iteration, so the
labels field is extended with the loop's precondition, which thereby acts as the
invariant. Sound by recursion on the derivation height. `post` is carried for
symmetry with `[block]` and for the paper's `Qₘ` notation; a loop label has
arity `0`, so a branch to it transfers no value and the length of `Q` is never
needed. -/
theorem valid_loop (bt : Silmaril.Wasm.V1.BlockType) (body : Silmaril.Wasm.V1.Expr) (pre : Assert.StackLen P 0)
    (_post : Assert.StackLen Q bt.toList.length)
    (inner : ∀ k ≤ n, Valid host k F (P :: L) R P body Q)
    (loop : ∀ k < n, Valid host k F L R P [.loop bt body] Q) :
    Valid host n F L R P [.loop bt body] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain rfl : vs = [] := List.length_eq_zero_iff.mp (pre ρ vs h hpre)
  have run' : BigStepN host n s f vf (expression [.loop bt body]) o := by
    simpa only [List.append_nil] using run
  obtain ⟨k₀, hk₀, run₁⟩ := loop_inv run'
  obtain ⟨k, s', f', hk, hcase⟩ := label_inv run₁
  have hkn : k ≤ n := by omega
  rcases hcase with ⟨ws, innerRun, restRun⟩ |
    ⟨l, extra, ws, innerRun, htarget, harity, restRun⟩ |
    ⟨l, ws, innerRun, houter, rfl⟩ | ⟨ws, innerRun, rfl⟩ | ⟨innerRun, rfl⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner k hkn s f ρ [] [] h hf _ hpre disj reify innerRun
    obtain rfl : o = ⟨s', f', .normal (vf ++ ws)⟩ := restRun.nil_inv
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_normal sat₁⟩
  · show ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F o.store o.frame ρ' (h' ∪ hf) ∧
        (∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.loop bt body] → ρ' x = ρ x) ∧
        Satisfies L R Q ρ' vf h' o.result
    obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, P', _pre, ws', hidx, -, hP⟩ :=
      inner k hkn s f ρ [] [] h hf _ hpre disj reify innerRun
    obtain rfl : P = P' := by
      simpa only [htarget, List.getElem?_cons_zero, Option.some.injEq] using hidx
    obtain rfl : ws = [] := List.length_eq_zero_iff.mp harity
    obtain rfl : ws' = [] := List.length_eq_zero_iff.mp (pre ρ₁ ws' h₁ hP)
    obtain ⟨h₂, ρ₂, disj₂, reify₂, agree₂, sat₂⟩ :=
      loop k (by omega) s' f' ρ₁ [] vf h₁ hf o hP disj₁ reify₁ restRun
    exact ⟨h₂, ρ₂, disj₂, reify₂, agree_loop agree₁ agree₂, sat₂⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner k hkn s f ρ [] [] h hf _ hpre disj reify innerRun
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_lower houter sat₁⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      inner k hkn s f ρ [] [] h hf _ hpre disj reify innerRun
    exact ⟨h₁, ρ₁, disj₁, reify₁, by simpa using agree₁, satisfies_ret sat₁⟩
  · obtain ⟨_, _, _, _, _, sat₁⟩ :=
      inner k hkn s f ρ [] [] h hf _ hpre disj reify innerRun
    exact (sat₁ : False).elim

/-- The `[if]` rule. -/
theorem valid_if (bt : Silmaril.Wasm.V1.BlockType) (left right : Silmaril.Wasm.V1.Expr) (S : List (Term Value)) (Hp : HAssert)
    (c : Term (BitVec 32))
    (hthen : Valid host n F L R (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ ≠ 0)))
      [.block bt left] Q)
    (helse : Valid host n F L R (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ = 0)))
      [.block bt right] Q) :
    Valid host n F L R (Assert.mk (S ++ [Term.i32 c]) Hp) [.if_ bt left right] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain ⟨rfl, hH⟩ := hpre
  replace run : BigStepN host n s f ((vf ++ S.map fun τ => τ ρ) ++ [Term.i32 c ρ])
      (expression [Silmaril.Wasm.V1.Instr.if_ bt left right]) o := by
    simpa [List.map_append, List.append_assoc] using run
  obtain ⟨k, us, cc, hk, hus, hcase⟩ := if_inv run
  obtain ⟨rfl, hcc⟩ := List.append_inj' hus rfl
  obtain rfl : cc = c ρ := (i32_inj (by simpa [Term.i32, Term.int] using hcc)).symm
  rcases hcase with ⟨hzero, runRight⟩ | ⟨hnonzero, runLeft⟩
  · obtain ⟨h', ρ', disj', reify', agree, sat⟩ :=
      helse s f ρ _ vf h hf o ⟨rfl, hH, hzero⟩ disj reify (runRight.mono (by omega))
    exact ⟨h', ρ', disj', reify', fun x hx => agree x (by simp_all), sat⟩
  · obtain ⟨h', ρ', disj', reify', agree, sat⟩ :=
      hthen s f ρ _ vf h hf o ⟨rfl, hH, hnonzero⟩ disj reify (runLeft.mono (by omega))
    exact ⟨h', ρ', disj', reify', fun x hx => agree x (by simp_all), sat⟩

/-- The `[br_if]` rule: the postcondition describes the case where the break is
not taken. -/
theorem valid_brIf (l : LabelIdx) (S : List (Term Value)) (Hp : HAssert)
    (c : Term (BitVec 32))
    (taken : Valid host n F L R (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ ≠ 0)))
      [.br l] Q) :
    Valid host n F L R (Assert.mk (S ++ [Term.i32 c]) Hp) [.brIf l]
      (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ = 0))) := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain ⟨rfl, hH⟩ := hpre
  replace run : BigStepN host n s f ((vf ++ S.map fun τ => τ ρ) ++ [Term.i32 c ρ])
      (expression [Silmaril.Wasm.V1.Instr.brIf l]) o := by
    simpa [List.map_append, List.append_assoc] using run
  obtain ⟨k, us, cc, hk, hus, hcase⟩ := brIf_inv run
  obtain ⟨rfl, hcc⟩ := List.append_inj' hus rfl
  obtain rfl : cc = c ρ := (i32_inj (by simpa [Term.i32, Term.int] using hcc)).symm
  rcases hcase with ⟨hzero, restRun⟩ | ⟨hnonzero, runBr⟩
  · obtain rfl := restRun.nil_inv
    exact ⟨h, ρ, disj, reify, fun _ _ => rfl, _, rfl, rfl, hH, hzero⟩
  · -- The branch is taken, so the result is a `br`, whose interpretation does
    -- not mention the postcondition at all.
    obtain rfl := br_inv runBr
    exact taken s f ρ _ vf h hf _ ⟨rfl, hH, hnonzero⟩ disj reify (runBr.mono (by omega))

/-- The `[br_table]` rule. -/
theorem valid_brTable (ls : List LabelIdx) (dflt : LabelIdx) (S : List (Term Value))
    (Hp : HAssert) (c : Term (BitVec 32))
    (cases : ∀ (k : Nat) (l : LabelIdx), ls[k]? = some l →
      Valid host n F L R (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => (c ρ).toNat = k)))
        [.br l] Q)
    (dfltCase : Valid host n F L R
      (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => ls.length ≤ (c ρ).toNat)))
      [.br dflt] Q) :
    Valid host n F L R (Assert.mk (S ++ [Term.i32 c]) Hp) [.brTable ls dflt] Q := by
  intro s f ρ vs vf h hf o hpre disj reify run
  obtain ⟨rfl, hH⟩ := hpre
  replace run : BigStepN host n s f ((vf ++ S.map fun τ => τ ρ) ++ [Term.i32 c ρ])
      (expression [Silmaril.Wasm.V1.Instr.brTable ls dflt]) o := by
    simpa [List.map_append, List.append_assoc] using run
  obtain ⟨k, us, cc, hk, hus, runBr⟩ := brTable_inv run
  obtain ⟨rfl, hcc⟩ := List.append_inj' hus rfl
  obtain rfl : cc = c ρ := (i32_inj (by simpa [Term.i32, Term.int] using hcc)).symm
  rcases hls : ls[(c ρ).toNat]? with - | l
  · rw [hls] at runBr
    exact dfltCase s f ρ _ vf h hf o
      ⟨rfl, hH, List.getElem?_eq_none_iff.mp hls⟩ disj reify (runBr.mono (by omega))
  · rw [hls] at runBr
    exact cases (c ρ).toNat l hls s f ρ _ vf h hf o ⟨rfl, hH, rfl⟩ disj reify
      (runBr.mono (by omega))

end Silmaril.Wasm.Logic.V1
