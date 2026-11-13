module

public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.StepA

/-!
# Merging a resource manager: plain code and the result

* `step_link`, `exec_link`, `run_link`: code that calls no manager export runs on `M`'s part of
  the merged instance;
* `onSnd_fail`, `call_new`: the manager's `new`;
* **`post_eq`**: the glue's conversion of the result (`rm.new` of an `own` result) followed by
  lifting is lifting followed by the caller's `lower_own`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst) (H : HTab)

/-- The instruction calls no manager export. -/
def Plain : AInstr → Prop
  | .call g _ => mgrName g = false
  | _ => True

theorem step_link (i : AInstr) (hi : Plain i) (f : Frame) :
    i.step (link M (mgr H)) f = (i.step M f).onFst := by
  cases i with
  | call g n =>
    have hg : mgrName g = false := hi
    by_cases h : n ≤ f.stack.length
    · simp only [AInstr.step, h, ↓reduceIte, onFst_bind, onFst_pure, hg, Bool.false_eq_true]
    · simp only [AInstr.step, h, ↓reduceIte, onFst_fail]
  | localGet j => cases h : f.locals[j]? <;> simp only [AInstr.step, h, onFst_pure, onFst_fail]
  | localSet j =>
    rcases f with ⟨ls, _ | ⟨v, st⟩⟩
    · exact onFst_fail.symm
    · by_cases h : j < ls.length <;> simp only [AInstr.step, h, ite_true, ite_false,
        onFst_pure, onFst_fail]
  | i32Const c => exact (onFst_pure _).symm

theorem exec_link (is : List AInstr) (hi : ∀ i ∈ is, Plain i) (f : Frame) :
    exec (link M (mgr H)) is f = (exec M is f).onFst := by
  induction is generalizing f with
  | nil => exact (onFst_pure _).symm
  | cons i is ih =>
    rw [exec_cons, exec_cons, step_link M H i (hi i (List.mem_cons_self ..)), onFst_bind]
    exact RM.bind_congr fun f' => ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) f'

theorem run_link (fn : AFn) (hi : ∀ i ∈ fn.body, Plain i) (xs : List Flat) :
    fn.run (link M (mgr H)) xs = (fn.run M xs).onFst := by
  simp only [AFn.run, onFst_bind, onFst_check, onFst_pure, exec_link M H _ hi]

theorem onSnd_fail {σ τ α : Type} : ((fail : RM τ α).onSnd : RM (σ × τ) α) = fail := by
  funext st o
  cases o <;> simp [RM.onSnd, fail]

theorem call_new {r : RtId} (hr : r < 2 ^ 32) (x : BitVec 32) :
    (link M (mgr H)).call "rm.new" [Flat.i32 x, Flat.i32 (BitVec.ofNat 32 r)] =
      (RM.ofTab (newF H r x) >>= fun h => pure [Flat.i32 h]) := by
  rw [← ofTab_map]
  have hm : mgrName "rm.new" = true := by decide
  show (if mgrName "rm.new" = true then
      (mgrCall H "rm.new" [Flat.i32 x, Flat.i32 (BitVec.ofNat 32 r)]).onSnd
    else (M.call "rm.new" [Flat.i32 x, Flat.i32 (BitVec.ofNat 32 r)]).onFst) = _
  simp only [hm, ↓reduceIte]
  dsimp only [mgrCall]
  simp only [ite_true]
  have hfun : (fun t => (newF H (BitVec.ofNat 32 r).toNat x t).map fun p => ([Flat.i32 p.1], p.2)) =
      (fun t => (newF H r x t).map fun p => ([Flat.i32 p.1], p.2)) := by rw [toNat_ofNat_lt hr]
  exact (congrArg (fun f => (RM.ofFn f).onSnd) hfun).trans (onSnd_ofFn _)

theorem call_new_none {y : Flat} (hy : asI32? y = none) (rt : Flat) :
    (link M (mgr H)).call "rm.new" [y, rt] = fail := by
  have hm : mgrName "rm.new" = true := by decide
  show (if mgrName "rm.new" = true then (mgrCall H "rm.new" [y, rt]).onSnd
    else (M.call "rm.new" [y, rt]).onFst) = _
  simp only [hm, ↓reduceIte]
  rcases y with ⟨(_ | _) | (_ | _), b⟩ <;> simp [asI32?] at hy <;> exact onSnd_fail

/-! ## The result -/

/-- The last step of the convention: unerase, or trap on a `borrow` result. -/
abbrev finR {σ : Type} (res : Option RTy) (r : Option PVal) : RM σ (Option RVal) :=
  if resultOk res then pure (unerase res r) else fail

theorem onFst_finR {σ τ : Type} (res : Option RTy) (r : Option PVal) :
    ((finR res r : RM σ (Option RVal)).onFst : RM (σ × τ) (Option RVal)) = finR res r := by
  unfold finR
  cases resultOk res
  · exact onFst_fail
  · exact onFst_pure _

theorem hostLower_plain {res : Option RTy} (h : ∀ r, res ≠ some (.own r)) (v : Option RVal) :
    hostLower H M res v = pure v := by
  rcases res with _ | (_ | r | _)
  · rfl
  · rfl
  · exact absurd rfl (h r)
  · rfl

theorem single32_snoc (ys : List Flat) (y : Flat) :
    single32? (ys ++ [y]) = if ys = [] then asI32? y else none := by
  rcases ys with _ | ⟨a, ys⟩
  · rcases y with ⟨(_ | _) | (_ | _), b⟩ <;> rfl
  · simp only [List.cons_append, reduceCtorEq, ↓reduceIte]
    have hne : ys ++ [y] ≠ [] := by simp
    rcases hys : ys ++ [y] with _ | ⟨c, cs⟩
    · exact absurd hys hne
    · rcases a with ⟨(_ | _) | (_ | _), b⟩ <;> rfl

/-- A result that is not a handle. -/
theorem post_plain {res : Option RTy} (h : ∀ r, res ≠ some (.own r)) (he : postM res = [])
    (g : Frame) :
    ((exec (link M (mgr H)) (postM res) g >>= fun f => pure f.stack.reverse) >>= fun rs =>
        liftResult (link M (mgr H)) (res.map RTy.erase) rs >>= finR res) =
      ((liftResult M (res.map RTy.erase) g.stack.reverse >>= finR res).onFst >>=
        hostLower H M res) := by
  rw [he, exec_nil, RM.pure_bind, RM.pure_bind, onFst_bind, RM.bind_assoc]
  rw [show liftResult (link M (mgr H)) (res.map RTy.erase) g.stack.reverse =
    (liftResult M (res.map RTy.erase) g.stack.reverse).onFst from liftResult_withTab M H.T _ _]
  refine RM.bind_congr fun r => ?_
  rw [onFst_finR, show hostLower H M res = pure from funext (hostLower_plain M H h), RM.bind_pure]

theorem exec_postOwn (r : RtId) (ls : List Flat) (y : Flat) (st : List Flat) :
    exec (link M (mgr H)) (postM (some (.own r))) ⟨ls, y :: st⟩ =
      ((link M (mgr H)).call "rm.new" [y, Flat.i32 (BitVec.ofNat 32 r)] >>= fun ys =>
        pure ⟨ls, ys.reverse ++ st⟩) := by
  rw [postM, exec_cons, step_i32Const, RM.pure_bind, exec_cons,
    step_call _ "rm.new" ⟨ls, Flat.i32 (BitVec.ofNat 32 r) :: y :: st⟩ (by simp)]
  simp only [exec_nil, RM.bind_pure]
  rfl

theorem exec_postOwn_nil (r : RtId) (ls : List Flat) :
    exec (link M (mgr H)) (postM (some (.own r))) ⟨ls, []⟩ = fail := by
  rw [postM, exec_cons, step_i32Const, RM.pure_bind, exec_cons]
  simp only [AInstr.step, List.length_cons, List.length_nil, Nat.reduceLeDiff, ↓reduceIte,
    RM.fail_bind]

theorem spec_u32_none {rs : List Flat} (h : single32? rs = none) (r : RtId) :
    ((liftResult M (some (.val .u32)) rs >>= finR (some (.own r))).onFst >>=
      hostLower H M (some (.own r))) = fail := by
  rw [liftResult_u32, h, RM.fail_bind, onFst_fail, RM.fail_bind]

/-- An `own` result whose rep is an `i32`. -/
theorem post_own_i32 {r : RtId} (hr : r < 2 ^ 32) (ls st : List Flat) (x : BitVec 32) :
    ((exec (link M (mgr H)) (postM (some (.own r))) ⟨ls, Flat.i32 x :: st⟩ >>= fun f =>
        pure f.stack.reverse) >>= fun rs =>
        liftResult (link M (mgr H)) (some (.val .u32)) rs >>= finR (some (.own r))) =
      ((liftResult M (some (.val .u32)) (Flat.i32 x :: st).reverse >>=
        finR (some (.own r))).onFst >>= hostLower H M (some (.own r))) := by
  rw [exec_postOwn, call_new M H hr, RM.bind_assoc, RM.bind_assoc, RM.bind_assoc]
  simp only [RM.pure_bind, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_append, List.reverse_cons]
  cases st with
  | nil =>
    simp only [List.reverse_nil, List.nil_append, liftResult_u32, single32?, finR, resultOk,
      unerase, ↓reduceIte, RM.pure_bind, onFst_pure]
    rfl
  | cons z st =>
    have hn : ∀ h : BitVec 32, single32? ((z :: st).reverse ++ [Flat.i32 h]) = none := by
      intro h
      rw [single32_snoc]
      simp
    have hn' : single32? ((z :: st).reverse ++ [Flat.i32 x]) = none := hn x
    rw [spec_u32_none M H hn']
    simp only [liftResult_u32, hn, RM.fail_bind]
    exact ofTab_bind_fail _

/-- **The result conversion of the glue**: `rm.new` and lifting is lifting and `lower_own`. -/
theorem post_own {r : RtId} (hr : r < 2 ^ 32) (g : Frame) :
    ((exec (link M (mgr H)) (postM (some (.own r))) g >>= fun f => pure f.stack.reverse) >>=
        fun rs => liftResult (link M (mgr H)) (some (.val .u32)) rs >>= finR (some (.own r))) =
      ((liftResult M (some (.val .u32)) g.stack.reverse >>= finR (some (.own r))).onFst >>=
        hostLower H M (some (.own r))) := by
  rcases g with ⟨ls, _ | ⟨y, st⟩⟩
  · rw [exec_postOwn_nil, RM.fail_bind, RM.fail_bind, spec_u32_none M H rfl]
  · cases hy : asI32? y with
    | none =>
      have hs : single32? (y :: st).reverse = none := by
        rw [List.reverse_cons, single32_snoc]
        by_cases h : st.reverse = [] <;> simp [h, hy]
      rw [exec_postOwn, call_new_none M H hy, RM.fail_bind, RM.fail_bind, spec_u32_none M H hs,
        RM.fail_bind]
    | some x =>
      rw [asI32_eq hy]
      exact post_own_i32 M H hr ls st x

end Silmaril.Proofs.Wasm.Jco.Res
