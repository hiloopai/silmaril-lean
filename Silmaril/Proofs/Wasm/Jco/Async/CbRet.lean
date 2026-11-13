module

public import Silmaril.Wasm.Jco.Async.CbRet.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms

/-!
# `task.return` called from a callback: proofs

Proofs of `Silmaril.Wasm.Jco.Async.CbRet.Thms`.

* `earlyDrive_retCb`: from a state where the task has no results and `task.return` of the values
  steps to `st'`, the loop up to `task.return` with the callback of `retCb ex` has exactly one
  outcome: the values and the code `ex`, at `st'`.
* `asyncCallC_eq`: the caller's view is the synchronous lift, then the tail.
* `liftFst_bind_congr`: two tails that agree on every state of `M` next to the store `st` give the
  same lifted computation from `(x, st)`.
* `asyncCallC_retCb`: with `canonCall … = RM.liftFst m₀`, the caller's view of `retCb ex` is the
  stackful async shim's call.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.CbRet

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event startSync step Waits)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait
open Silmaril.Proofs.Wasm.Jco.Async.Early

variable (M : CoreInst)

/-- The callback of `retCb ex` on a task without results: `task.return`, then the code `ex`. -/
theorem retCb_cb_apply (ex : List Flat) (t : Nat) (ws : List Val) (a : List Flat) (x : M.St)
    {st st' : Store} {r : Res} (hs : step st (.taskReturn t ws) = some (st', r)) :
    (retCb M ex).cb t ws a (x, st) = (pure ex : RM M.withStore.St (List Flat)) (x, st') :=
  builtin_then M hs _ x

/-- Once the task holds results, the loop stops at once. -/
theorem earlyDrive_of_result (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (rs : List Flat) (s : M.withStore.St) {ys : List Val} (hr : (s.2.tasks t).result = some ys)
    (o : Out M.withStore.St (List Val × List Flat)) :
    EarlyDrive M cb t rs s o ↔ o = .ok (ys, rs) s := by
  constructor
  · intro h
    cases h with
    | ret hr' =>
      rw [hr] at hr'
      cases hr'
      rfl
    | exitTrap hr' => rw [hr] at hr'; cases hr'
    | yieldOk hr' => rw [hr] at hr'; cases hr'
    | yieldTrap hr' => rw [hr] at hr'; cases hr'
    | waitOk hr' => rw [hr] at hr'; cases hr'
    | waitTrap hr' => rw [hr] at hr'; cases hr'
    | bad hr' => rw [hr] at hr'; cases hr'
  · rintro rfl
    exact .ret hr

/-- Every outcome of the loop with the callback of `retCb ex` is the values with the code `ex`. -/
theorem earlyDrive_retCb_out (ex : List Flat) (t : Nat) (ws : List Val) (x : M.St)
    {st st' : Store} (hr : (st.tasks t).result = none)
    (hs : step st (.taskReturn t ws) = some (st', .unit))
    {o : Out M.withStore.St (List Val × List Flat)}
    (h : EarlyDrive M ((retCb M ex).cb t ws) t [i32n cbYield] (x, st) o) :
    o = .ok (ws, ex) (x, st') := by
  have hr' : (st'.tasks t).result = some ws := step_taskReturn_result hs
  have hcb := retCb_cb_apply M ex t ws [i32n 0, i32n 0, i32n 0] x hs
  cases h with
  | ret hr₀ => exact absurd (hr.symm.trans hr₀) (by simp)
  | exitTrap _ hc => exact absurd hc (by decide)
  | yieldOk _ _ h hd =>
    have he : Out.ok _ _ = Out.ok ex (x, st') := (congrFun hcb _).mp h
    obtain ⟨hrs, hs₁⟩ := Out.ok.inj he
    have hr₁ : (st'.tasks t).result = some ws := hr'
    rw [hrs, hs₁] at hd
    exact (earlyDrive_of_result M _ t ex (x, st') hr₁ o).1 hd
  | yieldTrap _ _ h =>
    have he : (Out.trap : Out M.withStore.St (List Flat)) = Out.ok ex (x, st') :=
      (congrFun hcb _).mp h
    cases he
  | waitOk _ hc => exact absurd hc (by decide)
  | waitTrap _ hc => exact absurd hc (by decide)
  | bad _ hb => exact absurd ⟨_, rfl, by decide⟩ hb

/-- **The loop up to `task.return` with the callback of `retCb ex`** has exactly one outcome:
the values, with the code `ex`, at the store after `task.return`. -/
theorem earlyDrive_retCb (ex : List Flat) (t : Nat) (ws : List Val) (x : M.St) {st st' : Store}
    (hr : (st.tasks t).result = none) (hs : step st (.taskReturn t ws) = some (st', .unit)) :
    EarlyDrive M ((retCb M ex).cb t ws) t [i32n cbYield] (x, st) =
      (pure (ws, ex) : RM M.withStore.St (List Val × List Flat)) (x, st') := by
  have hr' : (st'.tasks t).result = some ws := step_taskReturn_result hs
  have hcb := retCb_cb_apply M ex t ws [i32n 0, i32n 0, i32n 0] x hs
  have hy : (BitVec.ofNat 32 cbYield).toNat % 16 = 1 := by decide
  funext o
  apply propext
  refine ⟨earlyDrive_retCb_out M ex t ws x hr hs, fun h => ?_⟩
  have ho : o = .ok (ws, ex) (x, st') := h
  rw [ho]
  exact EarlyDrive.yieldOk (c := BitVec.ofNat 32 cbYield) hr hy ((congrFun hcb _).mpr rfl)
    (.ret hr')

/-- **`EXIT` before `task.return` traps**, and has no other outcome. -/
theorem earlyDrive_exit_noRet (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (s : M.withStore.St) (hr : (s.2.tasks t).result = none)
    (o : Out M.withStore.St (List Val × List Flat)) :
    EarlyDrive M cb t [i32n cbExit] s o ↔ o = .trap := by
  have he : (BitVec.ofNat 32 cbExit).toNat % 16 = 0 := by decide
  refine ⟨fun h => ?_, fun h => h ▸ EarlyDrive.exitTrap (c := BitVec.ofNat 32 cbExit) hr he⟩
  cases h with
  | ret hr₀ => rw [hr] at hr₀; cases hr₀
  | exitTrap => rfl
  | yieldOk _ hc => exact absurd hc (by decide)
  | yieldTrap _ hc => exact absurd hc (by decide)
  | waitOk _ hc => exact absurd hc (by decide)
  | waitTrap _ hc => exact absurd hc (by decide)
  | bad _ hb => exact absurd ⟨_, rfl, by decide⟩ hb

/-- The caller's view decomposed: the C convention, then the tail. -/
theorem asyncCallC_eq {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : CbSplit M L) (sig : Sig) (vs : List PVal) :
    asyncCallC M R core b sig vs =
      (startTask M >>= fun t => canonCall M.withStore R core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= fun ws => b.pre t ws >>= fun p =>
          EarlyDrive M (b.cb t p.2) t p.1 >>= fun q => RM.ofOption (valsRes sig.result q.1)) := by
  simp only [asyncCallC, canonCall, RM.bind_assoc]

/-- Two tails that agree on every state of `M` next to the store `st` give the same lifted
computation from `(x, st)`. -/
theorem liftFst_bind_congr {α β : Type} (m : RM M.St α) (K K' : α → RM M.withStore.St β)
    (x : M.St) (st : Store) (h : ∀ a x', K a (x', st) = K' a (x', st)) :
    ((RM.liftFst m : RM M.withStore.St α) >>= K) (x, st) =
      ((RM.liftFst m : RM M.withStore.St α) >>= K') (x, st) := by
  funext o
  apply propext
  rw [liftFst_bind_apply_ws M m K (x, st) o, liftFst_bind_apply_ws M m K' (x, st) o]
  simp only [h]

/-- The tail of `retCb ex` after `M` returned: the values at the store after `task.return`. -/
theorem retCb_tail (ex : List Flat) (st : Store) (res : Option PTy) (ws : List Val) (x : M.St) :
    ∃ st', step (startSync st).1 (.taskReturn st.next ws) = some (st', .unit) ∧
      ((retCb M ex).pre st.next ws >>= fun p => EarlyDrive M ((retCb M ex).cb st.next p.2)
          st.next p.1 >>= fun q => RM.ofOption (valsRes res q.1)) (x, (startSync st).1) =
        (RM.ofOption (valsRes res ws) : RM M.withStore.St (Option PVal)) (x, st') := by
  obtain ⟨st', hs, -, -⟩ := step_fresh st ws
  have hr : (((startSync st).1).tasks st.next).result = none := by
    simp [startSync, Silmaril.Wasm.Component.Async.upd]
  refine ⟨st', hs, ?_⟩
  show (pure ([i32n cbYield], ws) >>= _ : RM M.withStore.St (Option PVal)) _ = _
  rw [RM.pure_bind]
  refine (bind_at M (earlyDrive_retCb M ex st.next ws x hr hs) _).trans ?_
  rw [RM.pure_bind]

/-- The tail of the stackful async shim after `M` returned: the same values at the same store. -/
theorem shim_tail (cb : List Flat → RM M.withStore.St (List Flat)) (st st' : Store)
    (res : Option PTy) (ws : List Val) (x : M.St)
    (hs : step (startSync st).1 (.taskReturn st.next ws) = some (st', .unit)) :
    (epiTail M (retE M .stackful) cb .stackful st.next ws >>= fun ws' =>
        RM.ofOption (valsRes res ws')) (x, (startSync st).1) =
      (RM.ofOption (valsRes res ws) : RM M.withStore.St (Option PVal)) (x, st') := by
  simp only [epiTail, retE, RM.bind_assoc, RM.pure_bind, Style.exitResult, List.isEmpty_nil,
    RM.check_true, taskReturn_then]
  exact builtin_then M hs _ x

/-- **The caller's view of `retCb ex` is the stackful async shim's call** (the adaptor's
`task.return` at once), when the synchronous lift is `RM.liftFst m₀`. -/
theorem asyncCallC_retCb (ex : List Flat) (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) :
    asyncCallC M R core (retCb M ex) sig vs =
      asyncCall M R (shimRun M core sig.result .stackful) (AComp.noCallback M) .stackful sig vs := by
  rw [asyncCallC_eq, shimRun_eq, asyncCall_bodyWith, hc, startTask_bind, startTask_bind]
  funext s
  refine liftFst_bind_congr M m₀ _ _ s.1 _ fun v x => ?_
  cases resVals v with
  | none => simp only [RM.ofOption_none, RM.fail_bind]
  | some ws =>
    simp only [RM.ofOption_some, RM.pure_bind]
    obtain ⟨st', hs, he⟩ := retCb_tail M ex s.2 sig.result ws x
    rw [he, shim_tail M _ s.2 st' sig.result ws x hs]

end Silmaril.Proofs.Wasm.Jco.Async.CbRet
