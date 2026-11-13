module

public import Silmaril.Proofs.Wasm.Jco.Resource.Sim
public import Silmaril.Wasm.Jco.Adaptor.Thms

/-!
# Resources in the jco toolchain: the core instance inside a component instance

The core instance `M` inside a component instance with handle tables (`withTab M T`) behaves
as `M` and leaves the table alone:

* `load_withTab`, `store_withTab`: memory accesses;
* `lowerParam_withTab`, `lowerParams_withTab`, `liftResult_withTab`: the canonical ABI of the
  first fragment;
* `step_withTab`, `exec_withTab`, `run_withTab`: adaptor code of `Silmaril.Wasm.Jco.Adaptor`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (T : Type)

theorem get_bind_apply {σ β : Type} (k : σ → RM σ β) (s : σ) (o : Out σ β) :
    (RM.get >>= k) s o ↔ k s s o := by
  rw [bind_apply]
  constructor
  · rintro (⟨a, s', h1, h2⟩ | ⟨h, -⟩)
    · cases h1
      exact h2
    · cases h
  · intro h
    exact .inl ⟨s, s, rfl, h⟩

theorem ofOption_bind_apply {σ α β : Type} (x : Option α) (k : α → RM σ β) (s : σ)
    (o : Out σ β) : (ofOption x >>= k) s o ↔ match x with
      | some a => k a s o
      | none => o = .trap := by
  cases x <;> simp [ofOption_some, ofOption_none, pure_bind, fail_bind, fail]

theorem load_withTab (a n : Nat) : (withTab M T).load a n = (M.load a n).onFst := by
  funext st o
  rcases st with ⟨s, t⟩
  have hl : (withTab M T).load a n (s, t) o ↔ ofOption ((M.mem s).read a n) (s, t) o :=
    get_bind_apply _ (s, t) o
  have hr : (M.load a n).onFst (s, t) o ↔ (ofOption ((M.mem s).read a n)).onFst (s, t) o := by
    cases o with
    | ok _ st' => exact and_congr_left' (get_bind_apply _ s _)
    | trap => exact get_bind_apply _ s _
  rw [eq_iff_iff, hl, hr, onFst_ofOption]

theorem setMem_onFst (x : M.St) (s : M.St) (t : T) (o : Out (M.St × T) Unit) :
    (RM.set x : RM M.St Unit).onFst (s, t) o ↔ RM.set (x, t) (s, t) o := by
  cases o with
  | ok u st' =>
    rcases st' with ⟨s', t'⟩
    simp only [onFst_ok, RM.set, Out.ok.injEq, Prod.mk.injEq]
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  | trap => simp [onFst_trap, RM.set]

theorem store_withTab (a : Nat) (bs : List UInt8) :
    (withTab M T).store a bs = (M.store a bs).onFst := by
  funext st o
  rcases st with ⟨s, t⟩
  have hl : (withTab M T).store a bs (s, t) o ↔ (ofOption ((M.mem s).write a bs) >>= fun m =>
      RM.set (M.setMem s m, t)) (s, t) o :=
    get_bind_apply _ (s, t) o
  have hr : (M.store a bs).onFst (s, t) o ↔ (ofOption ((M.mem s).write a bs) >>= fun m =>
      (RM.set (M.setMem s m)).onFst) (s, t) o := by
    rw [← onFst_ofOption (τ := T), ← onFst_bind]
    cases o with
    | ok _ st' => exact and_congr_left' (get_bind_apply _ s _)
    | trap => exact get_bind_apply _ s _
  have hm : (ofOption ((M.mem s).write a bs) >>= fun m =>
        (RM.set (M.setMem s m, t) : RM (M.St × T) Unit)) (s, t) o ↔
      (ofOption ((M.mem s).write a bs) >>= fun m =>
        (RM.set (M.setMem s m)).onFst) (s, t) o := by
    refine (ofOption_bind_apply _ _ _ _).trans (Iff.trans ?_ (ofOption_bind_apply _ _ _ _).symm)
    cases (M.mem s).write a bs with
    | none => exact Iff.rfl
    | some m => exact (setMem_onFst M T _ s t o).symm
  exact propext (hl.trans (hm.trans hr.symm))

theorem call_withTab (n : String) (xs : List Flat) :
    (withTab M T).call n xs = (M.call n xs).onFst := rfl

variable (r : List Flat → RM M.St (List Flat))

theorem lowerBytes_withTab (limit : Nat) (bs : List UInt8) :
    lowerBytes (withTab M T) (fun xs => (r xs).onFst) limit bs =
      (lowerBytes M r limit bs).onFst := by
  simp only [lowerBytes, onFst_bind, onFst_check, onFst_ofOption, onFst_pure, store_withTab]

theorem lowerParam_withTab (t : PTy) (v : PVal) :
    lowerParam (withTab M T) (fun xs => (r xs).onFst) t v = (lowerParam M r t v).onFst := by
  cases t <;> cases v <;>
    simp only [lowerParam, onFst_bind, onFst_check, onFst_pure, onFst_fail,
      lowerBytes_withTab]

theorem readPair_withTab (rp : BitVec 32) :
    readPair (withTab M T) rp = (readPair M rp).onFst := by
  simp only [readPair, onFst_bind, onFst_check, onFst_ofOption, load_withTab]

theorem liftResult_withTab (res : Option PTy) (xs : List Flat) :
    liftResult (withTab M T) res xs = (liftResult M res xs).onFst := by
  rcases res with _ | (t | _ | _)
  · cases xs <;> simp only [liftResult, onFst_pure, onFst_fail]
  · cases h : t.lift xs with
    | none => simp only [liftResult, h, onFst_fail]
    | some p =>
      rcases p with ⟨v, _ | _⟩ <;> simp only [liftResult, h, onFst_pure, onFst_fail]
  · rcases xs with _ | ⟨x, _ | _⟩ <;>
      simp only [liftResult, onFst_bind, onFst_ofOption, onFst_pure, onFst_fail, readPair_withTab]
  · rcases xs with _ | ⟨x, _ | _⟩ <;>
      simp only [liftResult, onFst_bind, onFst_ofOption, onFst_pure, onFst_fail, readPair_withTab]

theorem step_withTab (i : AInstr) (f : Frame) :
    i.step (withTab M T) f = (i.step M f).onFst := by
  cases i with
  | localGet j => cases h : f.locals[j]? <;> simp only [AInstr.step, h, onFst_pure, onFst_fail]
  | localSet j =>
    rcases f with ⟨ls, _ | ⟨v, st⟩⟩
    · exact onFst_fail.symm
    · by_cases h : j < ls.length <;> simp only [AInstr.step, h, ite_true, ite_false,
        onFst_pure, onFst_fail]
  | i32Const c => exact (onFst_pure _).symm
  | call g n =>
    by_cases h : n ≤ f.stack.length <;>
      simp only [AInstr.step, h, ite_true, ite_false, onFst_bind, onFst_pure, onFst_fail]

theorem exec_withTab (is : List AInstr) (f : Frame) :
    exec (withTab M T) is f = (exec M is f).onFst := by
  induction is generalizing f with
  | nil => exact (onFst_pure _).symm
  | cons i is ih => simp only [exec_cons, step_withTab, ih, onFst_bind]

theorem run_withTab (fn : AFn) (xs : List Flat) :
    fn.run (withTab M T) xs = (fn.run M xs).onFst := by
  simp only [AFn.run, onFst_bind, onFst_check, onFst_pure, exec_withTab]

end Silmaril.Proofs.Wasm.Jco.Res
