module

public import Silmaril.Wasm.FnInst.Opt.Rules.Defs
public import Silmaril.Wasm.FnInst.Opt.Inst.Thms

@[expose] public section

/-! # The peephole family: one rule lemma each, at the minimal hole

Each rule is proved once, as a `RunEq` at its minimal hole (a few lines of computation),
and holds over every model (`valid_*`): the code calls nothing. The module-level and
in-context forms are then corollaries of `peephole_module` and `sat_plug_equiv`
(`Silmaril.Wasm.FnInst.Opt.Rules.Thms`).

The information example `callDrop`: distinguished in some completion of the least
informative model, not distinguished in every completion, and equivalent over `pureZero`.
-/

namespace Silmaril.Proofs.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt

/-! ## Computation helpers -/

theorem St.with_stack {st : St} {l : List Val} (e : st.stack = l) :
    ({ st with stack := l } : St) = st := by
  cases st
  cases e
  rfl

theorem run_cons_ok {ft : FTypes} {E : Env} {i : Instr} {c : Code} {st st' : St}
    (hs : step ft E i st = {Out.ok st'}) : run ft E (i :: c) st = run ft E c st' := by
  rw [run_cons, hs, Out.bind_ok]

theorem exists_cons {st : St} (h : 1 ≤ st.stack.length) : ∃ a r, st.stack = a :: r := by
  cases e : st.stack with
  | nil => rw [e] at h; exact absurd h (by simp)
  | cons a r => exact ⟨a, r, rfl⟩

theorem binop_cons (f : Val → Val → Val) {st : St} {b a : Val} {r : List Val}
    (e : st.stack = b :: a :: r) : binop f st = .ok { st with stack := f a b :: r } := by
  unfold binop
  rw [e]

/-- A neutral right operand: the binary step on `k` above `a` gives back `a`. -/
theorem neutral_step {i : Instr} {k : Val} (h : Neutral i k) (ft : FTypes) (E : Env) {st : St}
    {a : Val} {r : List Val} (e : st.stack = k :: a :: r) :
    step ft E i st = {Out.ok { st with stack := a :: r }} := by
  cases h with
  | and =>
    show {binop _ st} = _
    rw [binop_cons _ e, BitVec.and_allOnes]
  | _ =>
    show {binop _ st} = _
    rw [binop_cons _ e]
    simp

/-! ## The rule lemmas -/

theorem neutral_runEq {i : Instr} {k : Val} (h : Neutral i k) (E : Env) :
    RunEq [] 1 E (neutralL h).1 (skip 1).1 := by
  intro st hst
  obtain ⟨a, r, e⟩ := exists_cons hst
  have e₁ : ({ st with stack := k :: st.stack } : St).stack = k :: a :: r := by rw [e]
  show run [] E [.const k, i] st = run [] E [] st
  rw [run_cons_ok rfl, run_cons_ok (neutral_step h [] E e₁), St.with_stack e]

theorem eqzV_eqzV_eqzV (a : Val) : eqzV (eqzV (eqzV a)) = eqzV a := by
  unfold eqzV
  by_cases ha : a = 0 <;> simp [ha]

theorem unop_cons (f : Val → Val) {st : St} {a : Val} {r : List Val} (e : st.stack = a :: r) :
    unop f st = .ok { st with stack := f a :: r } := by
  unfold unop
  rw [e]

theorem eqz_step (ft : FTypes) (E : Env) {st : St} {a : Val} {r : List Val}
    (e : st.stack = a :: r) : step ft E .eqz st = {Out.ok { st with stack := eqzV a :: r }} := by
  show {unop eqzV st} = _
  rw [unop_cons eqzV e]

theorem eqz3_runEq (E : Env) : RunEq [] 1 E eqz3L.1 eqz1.1 := by
  intro st hst
  obtain ⟨a, r, e⟩ := exists_cons hst
  show run [] E [.eqz, .eqz, .eqz] st = run [] E [.eqz] st
  rw [run_cons_ok (eqz_step [] E e), run_cons_ok (eqz_step [] E rfl),
    run_cons_ok (eqz_step [] E rfl), run_cons_ok (eqz_step [] E e), eqzV_eqzV_eqzV]

theorem dropGet_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (dropGetL x).1 (skip 0).1 := by
  intro st _
  show run [] E [.localGet x, .drop] st = run [] E [] st
  rw [run_cons_ok rfl, run_cons_ok rfl]

theorem dropGlobal_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (dropGlobalL x).1 (skip 0).1 := by
  intro st _
  show run [] E [.globalGet x, .drop] st = run [] E [] st
  rw [run_cons_ok rfl, run_cons_ok rfl]

theorem teeForm_runEq (x : ℕ) (E : Env) : RunEq [] 1 E (teeFormL x).1 (teeFormR x).1 := by
  intro st hst
  obtain ⟨a, r, e⟩ := exists_cons hst
  have hset : step [] E (.localSet x) st =
      {Out.ok ⟨Function.update st.locals x a, st.globals, r⟩} := by
    show {exec1 (.localSet x) st} = _
    simp only [exec1, pop1, e]
  have htee : step [] E (.localTee x) st =
      {Out.ok ⟨Function.update st.locals x a, st.globals, a :: r⟩} := by
    show {exec1 (.localTee x) st} = _
    simp only [exec1, pop1, e]
  show run [] E [.localSet x, .localGet x] st = run [] E [.localTee x] st
  rw [run_cons_ok hset, run_cons_ok rfl, run_cons_ok htee]
  simp only [Function.update_self]

theorem rseSet_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (rseSetL x).1 (skip 0).1 := by
  intro st _
  have hset : step [] E (.localSet x) { st with stack := st.locals x :: st.stack } =
      {Out.ok ⟨Function.update st.locals x (st.locals x), st.globals, st.stack⟩} := by
    show {exec1 (.localSet x) _} = _
    simp only [exec1, pop1]
  show run [] E [.localGet x, .localSet x] st = run [] E [] st
  rw [run_cons_ok rfl, run_cons_ok hset, Function.update_eq_self]

theorem rseTee_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (rseTeeL x).1 (rseTeeR x).1 := by
  intro st _
  have htee : step [] E (.localTee x) { st with stack := st.locals x :: st.stack } =
      {Out.ok ⟨Function.update st.locals x (st.locals x), st.globals,
        st.locals x :: st.stack⟩} := by
    show {exec1 (.localTee x) _} = _
    simp only [exec1, pop1]
  show run [] E [.localGet x, .localTee x] st = run [] E [.localGet x] st
  rw [run_cons_ok rfl, run_cons_ok htee, Function.update_eq_self, run_cons_ok rfl]

/-! ## Valid over every model -/

theorem valid_neutral {i : Instr} {k : Val} (h : Neutral i k) (M : Env) :
    holds (hole 1 1) M (.equiv (neutralL h) (skip 1)) := fun E _ => neutral_runEq h E

theorem valid_eqz3 (M : Env) : holds (hole 1 1) M (.equiv eqz3L eqz1) :=
  fun E _ => eqz3_runEq E

theorem valid_dropGet (x : ℕ) (M : Env) : holds (hole 0 0) M (.equiv (dropGetL x) (skip 0)) :=
  fun E _ => dropGet_runEq x E

theorem valid_dropGlobal (x : ℕ) (M : Env) :
    holds (hole 0 0) M (.equiv (dropGlobalL x) (skip 0)) := fun E _ => dropGlobal_runEq x E

theorem valid_teeForm (x : ℕ) (M : Env) :
    holds (hole 1 1) M (.equiv (teeFormL x) (teeFormR x)) := fun E _ => teeForm_runEq x E

theorem valid_rseSet (x : ℕ) (M : Env) : holds (hole 0 0) M (.equiv (rseSetL x) (skip 0)) :=
  fun E _ => rseSet_runEq x E

theorem valid_rseTee (x : ℕ) (M : Env) :
    holds (hole 0 1) M (.equiv (rseTeeL x) (rseTeeR x)) := fun E _ => rseTee_runEq x E

/-! ## Refuted at a smaller hole -/

/-- `i32.const 0; i32.add` is *not* the empty code from an empty stack: it traps there. The
rule needs its operand, which the minimal hole `1 → 1` provides (and `chk` rejects the pair at
`0 → 0`). -/
theorem addZero_distinct_at_empty (E : Env) {st : St} (e : st.stack = []) :
    run [] E [.const 0, .add] st ≠ run [] E [] st := by
  intro h
  have hadd : step [] E .add { st with stack := 0 :: st.stack } = {Out.trap} := by
    show {binop _ _} = _
    unfold binop
    rw [e]
  have ht : Out.trap ∈ run [] E [.const 0, .add] st := by
    rw [run_cons_ok rfl, run_cons, hadd]
    exact Or.inr ⟨rfl, rfl⟩
  rw [h] at ht
  cases ht

end Silmaril.Proofs.Wasm.FnInst.Opt.Rules
