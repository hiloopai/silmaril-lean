module

public import Silmaril.Wasm.FnInst.Opt.Rules.Defs
public import Silmaril.Wasm.FnInst.Opt.Inst.Thms
import Silmaril.Proofs.Wasm.FnInst.Opt.Rules.Basic
import Silmaril.Proofs.Wasm.FnInst.Opt.Rules.Info

@[expose] public section

/-! # The peephole family through the segment institution

Each rule of `Silmaril.Wasm.FnInst.Opt.Rules.Defs` is proved once, at its minimal hole, in
`Silmaril.Proofs.Wasm.FnInst.Opt.Rules.Basic` (`valid_*`, 2 to 12 lines each). Everything below
is generic transfer, one line per rule:

* **every function of every module** (`*_module`): `peephole_module` gives, for every
  well-typed module whose bodies are rewritten at typed positions (`Mdl.Rewrites`), the same
  semantics of every function at every call depth;
* **every context** (`*_inContext`): `sat_plug_equiv` gives, for every typed context `τ`
  placing the minimal hole into a hole `Y` and every model of `Y`, the equivalence of the
  plugged code.

The information example is in `Silmaril.Proofs.Wasm.FnInst.Opt.Rules.Info`
(`callDrop_distSome_top`, `callDrop_not_equiv_top`, `callDrop_not_distEvery_top`,
`callDrop_equiv_pureZero`, `callDrop_not_distSome_pureZero`). The refutation
`addZero_distinct_at_empty` shows why the hole's operand count matters.
-/

namespace Silmaril.Wasm.FnInst.Opt.Rules

section

open Silmaril.Wasm.FnInst.Opt

theorem St.with_stack {st : St} {l : List Val} (e : st.stack = l) :
    ({ st with stack := l } : St) = st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.St.with_stack e

theorem run_cons_ok {ft : FTypes} {E : Env} {i : Instr} {c : Code} {st st' : St}
    (hs : step ft E i st = {Out.ok st'}) : run ft E (i :: c) st = run ft E c st' :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.run_cons_ok hs

theorem exists_cons {st : St} (h : 1 ≤ st.stack.length) : ∃ a r, st.stack = a :: r :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.exists_cons h

theorem binop_cons (f : Val → Val → Val) {st : St} {b a : Val} {r : List Val}
    (e : st.stack = b :: a :: r) : binop f st = .ok { st with stack := f a b :: r } :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.binop_cons f e

/-- A neutral right operand: the binary step on `k` above `a` gives back `a`. -/
theorem neutral_step {i : Instr} {k : Val} (h : Neutral i k) (ft : FTypes) (E : Env) {st : St}
    {a : Val} {r : List Val} (e : st.stack = k :: a :: r) :
    step ft E i st = {Out.ok { st with stack := a :: r }} :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.neutral_step h ft E e

theorem neutral_runEq {i : Instr} {k : Val} (h : Neutral i k) (E : Env) :
    RunEq [] 1 E (neutralL h).1 (skip 1).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.neutral_runEq h E

theorem eqzV_eqzV_eqzV (a : Val) : eqzV (eqzV (eqzV a)) = eqzV a :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.eqzV_eqzV_eqzV a

theorem unop_cons (f : Val → Val) {st : St} {a : Val} {r : List Val} (e : st.stack = a :: r) :
    unop f st = .ok { st with stack := f a :: r } :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.unop_cons f e

theorem eqz_step (ft : FTypes) (E : Env) {st : St} {a : Val} {r : List Val}
    (e : st.stack = a :: r) : step ft E .eqz st = {Out.ok { st with stack := eqzV a :: r }} :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.eqz_step ft E e

theorem eqz3_runEq (E : Env) : RunEq [] 1 E eqz3L.1 eqz1.1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.eqz3_runEq E

theorem dropGet_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (dropGetL x).1 (skip 0).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.dropGet_runEq x E

theorem dropGlobal_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (dropGlobalL x).1 (skip 0).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.dropGlobal_runEq x E

theorem teeForm_runEq (x : ℕ) (E : Env) : RunEq [] 1 E (teeFormL x).1 (teeFormR x).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.teeForm_runEq x E

theorem rseSet_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (rseSetL x).1 (skip 0).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.rseSet_runEq x E

theorem rseTee_runEq (x : ℕ) (E : Env) : RunEq [] 0 E (rseTeeL x).1 (rseTeeR x).1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.rseTee_runEq x E

theorem valid_neutral {i : Instr} {k : Val} (h : Neutral i k) (M : Env) :
    holds (hole 1 1) M (.equiv (neutralL h) (skip 1)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_neutral h M

theorem valid_eqz3 (M : Env) : holds (hole 1 1) M (.equiv eqz3L eqz1) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_eqz3 M

theorem valid_dropGet (x : ℕ) (M : Env) : holds (hole 0 0) M (.equiv (dropGetL x) (skip 0)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_dropGet x M

theorem valid_dropGlobal (x : ℕ) (M : Env) :
    holds (hole 0 0) M (.equiv (dropGlobalL x) (skip 0)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_dropGlobal x M

theorem valid_teeForm (x : ℕ) (M : Env) :
    holds (hole 1 1) M (.equiv (teeFormL x) (teeFormR x)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_teeForm x M

theorem valid_rseSet (x : ℕ) (M : Env) : holds (hole 0 0) M (.equiv (rseSetL x) (skip 0)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_rseSet x M

theorem valid_rseTee (x : ℕ) (M : Env) :
    holds (hole 0 1) M (.equiv (rseTeeL x) (rseTeeR x)) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.valid_rseTee x M

/-- `i32.const 0; i32.add` is *not* the empty code from an empty stack: it traps there. The
rule needs its operand, which the minimal hole `1 → 1` provides (and `chk` rejects the pair at
`0 → 0`). -/
theorem addZero_distinct_at_empty (E : Env) {st : St} (e : st.stack = []) :
    run [] E [.const 0, .add] st ≠ run [] E [] st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.addZero_distinct_at_empty E e

end

section

open Silmaril.Wasm.FnInst.Opt

theorem callHole_ft {f n m : ℕ} (hf : callHole.ft[f]? = some (n, m)) : f = 0 ∧ n = 0 ∧ m = 1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callHole_ft hf

theorem pureZero_completion : pureZero.Completion callHole.ft Env.top :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.pureZero_completion

/-- The only completion of `pureZero` is itself. -/
theorem completion_pureZero {ft : FTypes} {E : Env} (hE : E.Completion ft pureZero) :
    E = pureZero :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.completion_pureZero hE

theorem step_call0 (E : Env) (st : St) :
    step callHole.ft E (.call 0) st = callOut E 0 0 st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.step_call0 E st

theorem callOut_pureZero (st : St) :
    callOut pureZero 0 0 st = {Out.ok ⟨st.locals, st.globals, 0 :: st.stack⟩} :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callOut_pureZero st

theorem callDrop_runEq_pureZero : RunEq callHole.ft 0 pureZero callDropL.1 callDropR.1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_runEq_pureZero

theorem trap_mem_callDrop (st : St) :
    Out.trap ∈ run callHole.ft Env.trapAll callDropL.1 st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.trap_mem_callDrop st

theorem callDrop_distSome_top : holds callHole Env.top (.distSome callDropL callDropR) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_distSome_top

theorem callDrop_not_equiv_top : ¬ holds callHole Env.top (.equiv callDropL callDropR) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_not_equiv_top

theorem callDrop_not_distEvery_top : ¬ holds callHole Env.top (.distEvery callDropL callDropR) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_not_distEvery_top

theorem callDrop_equiv_pureZero : holds callHole pureZero (.equiv callDropL callDropR) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_equiv_pureZero

theorem callDrop_not_distSome_pureZero :
    ¬ holds callHole pureZero (.distSome callDropL callDropR) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Rules.callDrop_not_distSome_pureZero

end

end Silmaril.Wasm.FnInst.Opt.Rules

namespace Silmaril.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt CategoryTheory

variable {M M' : Mdl} {imp : Env}

/-! ## Every function of every module -/

theorem neutral_module {i : Instr} {k : Val} (h : Neutral i k) (hM : M.Typed)
    (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.const k, i] [] 1 1 M M') : ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_neutral h _) (List.nil_prefix) hM himp himp' hR

theorem eqz3_module (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.eqz, .eqz, .eqz] [.eqz] 1 1 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_eqz3 _) (List.nil_prefix) hM himp himp' hR

theorem dropGet_module (x : ℕ) (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.localGet x, .drop] [] 0 0 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_dropGet x _) (List.nil_prefix) hM himp himp' hR

theorem dropGlobal_module (x : ℕ) (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.globalGet x, .drop] [] 0 0 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_dropGlobal x _) (List.nil_prefix) hM himp himp' hR

theorem teeForm_module (x : ℕ) (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.localSet x, .localGet x] [.localTee x] 1 1 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_teeForm x _) (List.nil_prefix) hM himp himp' hR

theorem rseSet_module (x : ℕ) (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.localGet x, .localSet x] [] 0 0 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_rseSet x _) (List.nil_prefix) hM himp himp' hR

theorem rseTee_module (x : ℕ) (hM : M.Typed) (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites [.localGet x, .localTee x] [.localGet x] 0 1 M M') :
    ∀ n, fsem M imp n = fsem M' imp n :=
  peephole_module (valid_rseTee x _) (List.nil_prefix) hM himp himp' hR

/-! ## Every context -/

theorem neutral_inContext {i : Instr} {k : Val} (h : Neutral i k) {Y : HSig}
    (τ : hole 1 1 ⟶ Y) (N : Model Y) :
    Sat N (Sen.equiv (plug τ (neutralL h)) (plug τ (skip 1))) :=
  sat_plug_equiv τ N (valid_neutral h _)

theorem eqz3_inContext {Y : HSig} (τ : hole 1 1 ⟶ Y) (N : Model Y) :
    Sat N (Sen.equiv (plug τ eqz3L) (plug τ eqz1)) :=
  sat_plug_equiv τ N (valid_eqz3 _)

theorem dropGet_inContext (x : ℕ) {Y : HSig} (τ : hole 0 0 ⟶ Y) (N : Model Y) :
    Sat N (Sen.equiv (plug τ (dropGetL x)) (plug τ (skip 0))) :=
  sat_plug_equiv τ N (valid_dropGet x _)

theorem teeForm_inContext (x : ℕ) {Y : HSig} (τ : hole 1 1 ⟶ Y) (N : Model Y) :
    Sat N (Sen.equiv (plug τ (teeFormL x)) (plug τ (teeFormR x))) :=
  sat_plug_equiv τ N (valid_teeForm x _)

theorem rseSet_inContext (x : ℕ) {Y : HSig} (τ : hole 0 0 ⟶ Y) (N : Model Y) :
    Sat N (Sen.equiv (plug τ (rseSetL x)) (plug τ (skip 0))) :=
  sat_plug_equiv τ N (valid_rseSet x _)

end Silmaril.Wasm.FnInst.Opt.Rules
