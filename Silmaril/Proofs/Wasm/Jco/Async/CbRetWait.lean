module

public import Silmaril.Proofs.Wasm.Jco.Async.CbRet

/-!
# `task.return` called from a callback after a wait: proofs

Part of `Silmaril.Wasm.Jco.Async.CbRet.Thms`.

* `earlyDrive_result`: when the loop up to `task.return` stops, the task holds the values.
* `asyncCallC_eq_asyncCall`: the caller's view of a `CbSplit` is `asyncCall` (stackful) of the
  body as an epilogue (`CbSplit.asEpi`), for every body. So `fstIs_of_epiOk` applies.
* `earlyDrive_waitRet`: from `WAIT si` with a callback that calls `task.return` (and ignores the
  event), the loop takes an event of a member of `si` and stops with the values.
* `pipeCb_epiOk`: the body `pipeCb ex` is faithful (`EpiOk`) on `Fresh` stores.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.CbRet

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event startSync step Waits upd packCopy)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait
open Silmaril.Proofs.Wasm.Jco.Async.Early

variable (M : CoreInst)

/-- **When the loop up to `task.return` stops, the task holds the values.** -/
theorem earlyDrive_result (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (rs : List Flat) (s s' : M.withStore.St) (q : List Val × List Flat)
    (h : EarlyDrive M cb t rs s (.ok q s')) : (s'.2.tasks t).result = some q.1 := by
  generalize ho : (Out.ok q s' : Out M.withStore.St (List Val × List Flat)) = o at h
  induction h with
  | ret hr =>
    cases ho
    exact hr
  | exitTrap => cases ho
  | yieldOk _ _ _ _ ih => exact ih ho
  | yieldTrap => cases ho
  | waitOk _ _ _ _ _ ih => exact ih ho
  | waitTrap => cases ho
  | bad => cases ho

/-- Binds whose continuations agree after every value of the first computation. -/
theorem bind_congr_ok' {σ α β : Type} {m : RM σ α} {k k' : α → RM σ β}
    (h : ∀ s a s', m s (.ok a s') → k a s' = k' a s') : (m >>= k) = (m >>= k') := by
  funext s o
  apply propext
  rw [RM.bind_apply, RM.bind_apply]
  constructor
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, (h s a s' h1) ▸ h2⟩
    · exact .inr h1
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, (h s a s' h1).symm ▸ h2⟩
    · exact .inr h1

/-- **The caller's view of a body whose callback may call `task.return` is `asyncCall` of the
body as a stackful epilogue.** -/
theorem asyncCallC_eq_asyncCall {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : CbSplit M L) (sig : Sig) (vs : List PVal) :
    asyncCallC M R core b sig vs =
      asyncCall M R (bodyWith M core sig.result b.asEpi) (AComp.noCallback M) .stackful sig vs := by
  simp only [asyncCallC, asyncCall, bodyWith, CbSplit.asEpi, RM.bind_assoc]
  refine RM.bind_congr fun t => RM.bind_congr fun _ => RM.bind_congr fun _ =>
    RM.bind_congr fun _ => RM.bind_congr fun _ => RM.bind_congr fun p => ?_
  refine Eq.trans ?_ (RM.bind_assoc (EarlyDrive M (b.cb t p.2) t p.1) (fun _ => pure []) _).symm
  refine bind_congr_ok' fun s q s' hq => ?_
  have hr := earlyDrive_result M _ t _ s s' q hq
  simp only [RM.pure_bind, List.isEmpty_nil, RM.check_true]
  rw [taskResult_bind]
  simp only [hr]

/-- A wait keeps the tasks. -/
theorem waits_result {st st' : Store} {si h t : Nat} {e : Event} (hw : Waits st si h e st')
    (hr : (st.tasks t).result = none) : (st'.tasks t).result = none := by
  obtain ⟨-, -, -, rfl⟩ := hw
  exact hr

/-- **`WAIT si` with a callback that calls `task.return`**: every outcome of the loop up to
`task.return` takes an event of a member of `si` and stops with the values. -/
theorem earlyDrive_waitRet_out (ex : List Flat) (t : Nat) (ys : List Val) (si : Nat)
    (hsi : 16 * si + 2 < 2 ^ 32) (x : M.St) (st : Store) (hr : (st.tasks t).result = none)
    {o : Out M.withStore.St (List Val × List Flat)}
    (h : EarlyDrive M ((retCb M ex).cb t ys) t (waitCode si) (x, st) o) :
    ∃ h e st' st'', Waits st si h e st' ∧ step st' (.taskReturn t ys) = some (st'', .unit) ∧
      o = .ok (ys, ex) (x, st'') := by
  have ⟨hm, hd⟩ := code_toNat si hsi
  cases h with
  | ret hr₀ => exact absurd (hr.symm.trans hr₀) (by simp)
  | exitTrap _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap _ hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk _ _ hw hcb hdr =>
    show ∃ h e st' st'', Waits st si h e st' ∧ step st' (.taskReturn t ys) = some (st'', .unit) ∧
      o = .ok (ys, ex) (x, st'')
    have hw' : Waits st si _ _ _ := hd ▸ hw
    have hr' := waits_result hw' hr
    obtain ⟨st'', hs, -⟩ := step_taskReturn _ t ys hr'
    have he : Out.ok _ _ = Out.ok ex (x, st'') :=
      (congrFun (retCb_cb_apply M ex t ys _ x hs) _).mp hcb
    obtain ⟨hrs, hs₁⟩ := Out.ok.inj he
    rw [hrs, hs₁] at hdr
    exact ⟨_, _, _, st'', hw', hs, (earlyDrive_of_result M _ t ex (x, st'')
      (step_taskReturn_result hs) o).1 hdr⟩
  | waitTrap _ _ hw hcb =>
    have hw' : Waits st si _ _ _ := hd ▸ hw
    obtain ⟨st'', hs, -⟩ := step_taskReturn _ t ys (waits_result hw' hr)
    have he : (Out.trap : Out M.withStore.St (List Flat)) = Out.ok ex (x, st'') :=
      (congrFun (retCb_cb_apply M ex t ys _ x hs) _).mp hcb
    cases he
  | bad _ hb => exact absurd ⟨_, rfl, by rw [hm]⟩ hb

/-- The loop with a member's event: it stops with the values. -/
theorem earlyDrive_waitRet_ok (ex : List Flat) (t : Nat) (ys : List Val) (si : Nat)
    (hsi : 16 * si + 2 < 2 ^ 32) (x : M.St) (st : Store) (hr : (st.tasks t).result = none)
    {h : Nat} {e : Event} {st' st'' : Store} (hw : Waits st si h e st')
    (hs : step st' (.taskReturn t ys) = some (st'', .unit)) :
    EarlyDrive M ((retCb M ex).cb t ys) t (waitCode si) (x, st) (.ok (ys, ex) (x, st'')) := by
  have ⟨hm, hd⟩ := code_toNat si hsi
  have hcb := (congrFun (retCb_cb_apply M ex t ys
    [i32n e.code.toNat, i32n e.index, i32n e.payload] x hs) (.ok ex (x, st''))).mpr rfl
  exact EarlyDrive.waitOk (c := BitVec.ofNat 32 (2 + 16 * si)) hr hm (hd.symm ▸ hw) hcb
    (.ret (step_taskReturn_result hs))

/-! ## The body `pipeCb` -/

section Stores

variable (st : Store) (ws : List Val)

/-- After the pipe and `joinWait`: the writable end has joined the set `st.next + 3`. -/
@[expose] def pJ : Store := joinStore (st₄ st ws) (st.next + 2)

/-- After the wait took the writable end's event. -/
@[expose] def pJ' : Store := { pJ st ws with ev := upd (pJ st ws).ev (st.next + 2) none }

end Stores

/-- The body up to its callback code: the pipe, then `WAIT` on the set of the writable end. -/
theorem pipeCb_pre (ex : List Flat) (st : Store) (ws : List Val) (hf : st.chans (st.next + 1) = {})
    (x : M.St) :
    (pipeCb M ex).pre st.next ws (x, (startSync st).1) =
      (pure (waitCode (st.next + 3), ws) : RM M.withStore.St (List Flat × List Val))
        (x, pJ st ws) := by
  have hj := joinWait_run M (st₄ st ws) (st.next + 2) x (by rw [st₄_next]; omega)
    ⟨_, st₄_tbl st ws⟩
  show (builtin M .streamNew >>= _) _ = _
  refine (builtin_then M (step_new st) _ x).trans ?_
  refine (builtin_then M (step_write st ws hf) _ x).trans ?_
  refine (builtin_then M (step_read st ws) _ x).trans ?_
  refine (bind_at M hj _).trans ?_
  rw [RM.pure_bind, st₄_next]
  rfl

/-- The only wait from `pJ` takes the writable end's event. -/
theorem pJ_waits (st : Store) (hU : Unused st) (ws : List Val) {h : Nat} {e : Event}
    {st' : Store} (hw : Waits (pJ st ws) (st.next + 3) h e st') : st' = pJ' st ws ∧ h = st.next + 2 := by
  obtain ⟨-, hj, -, rfl⟩ := hw
  have hj' : upd (st₄ st ws).joined (st.next + 2) (some (st₄ st ws).next) h = some (st.next + 3) := hj
  by_cases hh : h = st.next + 2
  · exact ⟨by rw [hh]; rfl, hh⟩
  · have h4 : (st₄ st ws).joined h = some (st.next + 3) := by
      simpa only [upd, hh, ite_false] using hj'
    have hst : st.joined h = some (st.next + 3) := h4
    exact absurd hst ((hU (st.next + 3) (by omega)).2.2.2.2 h)

theorem pJ_task (st : Store) (ws : List Val) : ((pJ st ws).tasks st.next).result = none :=
  st₄_task st ws

/-- The writable end's event at `pJ`. -/
theorem pJ_waits_ok (st : Store) (ws : List Val) :
    Waits (pJ st ws) (st.next + 3) (st.next + 2)
      ⟨.streamWrite, st.next + 2, packCopy .completed ws.length, []⟩ (pJ' st ws) := by
  have hn := st₄_next st ws
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp [pJ, joinStore, upd, hn]
  · simp [pJ, joinStore, upd, hn]
  · simpa [pJ, joinStore] using st₄_ev st ws

/-- **The loop from `pJ` with the callback that calls `task.return`** has one outcome. -/
theorem pipeCb_drive (ex : List Flat) (st : Store) (hU : Unused st)
    (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val) (x : M.St) {K : Store}
    (hK : step (pJ' st ws) (.taskReturn st.next ws) = some (K, .unit)) :
    EarlyDrive M ((retCb M ex).cb st.next ws) st.next (waitCode (st.next + 3)) (x, pJ st ws) =
      (pure (ws, ex) : RM M.withStore.St (List Val × List Flat)) (x, K) := by
  funext o
  apply propext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, _, st', st'', hw, hs, ho⟩ :=
      earlyDrive_waitRet_out M ex st.next ws _ hb x _ (pJ_task st ws) h
    have hst' : st' = pJ' st ws := (pJ_waits st hU ws hw).1
    have hKK : K = st'' := by
      rw [hst', hK] at hs
      exact (Prod.mk.inj (Option.some.inj hs)).1
    rw [ho, hKK]
    rfl
  · have ho : o = .ok (ws, ex) (x, K) := h
    rw [ho]
    exact (earlyDrive_waitRet_ok M ex st.next ws _ hb x _ (pJ_task st ws) (pJ_waits_ok st ws) hK)

/-- **The body `pipeCb ex` returns the values faithfully** on a store whose handles from
`st.next` on are unused. -/
theorem pipeCb_epiOk (ex : List Flat) (cb : List Flat → RM M.withStore.St (List Flat))
    (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) :
    EpiOk M (pipeCb M ex).asEpi cb .stackful st := by
  intro ws x
  obtain ⟨K, hK, hKr, -⟩ := step_taskReturn (pJ' st ws) st.next ws (pJ_task st ws)
  have hf : st.chans (st.next + 1) = {} := (hU (st.next + 1) (by omega)).2.1
  have he : epiTail M (pipeCb M ex).asEpi cb .stackful st.next ws (x, (startSync st).1) =
      (pure ws : RM M.withStore.St (List Val)) (x, K) := by
    unfold epiTail CbSplit.asEpi
    rw [RM.bind_assoc]
    refine (bind_at M (pipeCb_pre M ex st ws hf x) _).trans ?_
    rw [RM.pure_bind]
    refine (bind_at M (bind_at M (pipeCb_drive M ex st hU hb ws x hK) _) _).trans ?_
    simp only [RM.pure_bind, List.isEmpty_nil, RM.check_true]
    exact taskResult_apply M _ (x, K) _ hKr
  rw [he]
  exact ⟨fun o h => ⟨K, h⟩, K, rfl⟩

end Silmaril.Proofs.Wasm.Jco.Async.CbRet
