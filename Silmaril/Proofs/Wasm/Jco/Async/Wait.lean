module

public import Silmaril.Wasm.Jco.Async.Wait.Defs
public import Silmaril.Wasm.Jco.Async.Native.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Frame
public import Silmaril.Proofs.Wasm.Jco.Async.Basic
public import Silmaril.Proofs.Wasm.Jco.Async.Native

/-!
# Natively async bodies that wait or use streams: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Wait.Thms`.

* `asyncCall_bodyWith`: `canon lift async` of a body with an epilogue is the synchronous lift,
  then the epilogue's tail (`epiTail`), then the read-back at the result type.
* `fstIs_of_epiOk`: when the synchronous lift over `M.withStore` is `RM.liftFst m₀` and the
  epilogue returns the values faithfully (`EpiOk`), the call agrees with `visible m₀` over
  `M`'s state.
* `retE_tail`: the adaptor's epilogue has the deterministic tail of `Frame` (`asyncStore`).
* `drive_wait_iff`: with a callback answering `EXIT`, the callback loop on `WAIT si` ends once
  with an event of a member of `si` taken, and has no other outcome.
* `pipeE_epiOk`, `pipeWaitE_epiOk`: the stream epilogues return the values faithfully from every
  `Fresh` store.
* `waitE_none`: `WAIT` on the fresh empty set has no outcome when no waitable has joined it.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Wait

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event startSync step Waits)
open Silmaril.Proofs.Wasm.Jco.Async.Frame

variable (M : CoreInst)

/-! ## The general form -/

theorem asyncCall_bodyWith (R core cb : List Flat → RM M.withStore.St (List Flat))
    (E : Nat → List Val → RM M.withStore.St (List Flat)) (sty : Style) (sig : Sig)
    (vs : List PVal) :
    asyncCall M R (bodyWith M core sig.result E) cb sty sig vs =
      (startTask M >>= fun t => canonCall M.withStore R core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= fun ws => epiTail M E cb sty t ws >>= fun ws' =>
          RM.ofOption (valsRes sig.result ws')) := by
  cases sty
  · simp only [asyncCall, bodyWith, epiTail, canonCall, RM.bind_assoc]
  · simp only [asyncCall, bodyWith, epiTail, canonCall, RM.bind_assoc]
    have hd : ∀ (t : Nat) (a : List Flat) (k : List Val → RM M.withStore.St (Option PVal)),
        ((Drive M cb a : RM M.withStore.St Unit) >>= fun _ => taskResult M t) >>= k =
          (Drive M cb a : RM M.withStore.St Unit) >>= fun _ => taskResult M t >>= k :=
      fun _ _ _ => RM.bind_assoc _ _ _
    simp only [hd]

/-- The tail of an async call after `M` returned `v`. -/
@[expose] def tailK (E : Nat → List Val → RM M.withStore.St (List Flat))
    (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (t : Nat) (res : Option PTy)
    (v : Option PVal) : RM M.withStore.St (Option PVal) :=
  RM.ofOption (resVals v) >>= fun ws => epiTail M E cb sty t ws >>= fun ws' =>
    RM.ofOption (valsRes res ws')

/-- What the caller sees after `M` returned `v`. -/
@[expose] def tailV (res : Option PTy) (v : Option PVal) : RM M.St (Option PVal) :=
  RM.ofOption (resVals v) >>= fun ws => RM.ofOption (valsRes res ws)

theorem ofOption_apply {σ α : Type} (x : Option α) (s : σ) (o : Out σ α) :
    (RM.ofOption x : RM σ α) s o ↔ (∃ a, x = some a ∧ o = .ok a s) ∨ (x = none ∧ o = .trap) := by
  cases x with
  | none => cases o <;> simp [RM.ofOption, RM.fail]
  | some a => cases o <;> simp [RM.ofOption, RM.pure]

/-- A tail that returns `ws` faithfully, followed by the read-back. -/
theorem epi_bind_ok {E cb sty st ws x} (hE : EpiOk M E cb sty st) (res : Option PTy)
    (r : Option PVal) (y : M.St) :
    (∃ z, (epiTail M E cb sty st.next ws >>= fun ws' => RM.ofOption (valsRes res ws'))
        (x, (startSync st).1) (.ok r (y, z))) ↔ valsRes res ws = some r ∧ y = x := by
  obtain ⟨hall, st₀, h₀⟩ := hE ws x
  constructor
  · rintro ⟨z, ⟨a, s', h1, h2⟩ | ⟨h1, -⟩⟩
    · obtain ⟨st', he⟩ := hall _ h1
      cases he
      rcases (ofOption_apply _ _ _).1 h2 with ⟨b, hb, he⟩ | ⟨-, he⟩
      · cases he
        exact ⟨hb, rfl⟩
      · cases he
    · obtain ⟨_, he⟩ := hall _ h1
      cases he
  · rintro ⟨hv, rfl⟩
    exact ⟨st₀, .inl ⟨ws, (y, st₀), h₀, (ofOption_apply _ _ _).2 (.inl ⟨r, hv, rfl⟩)⟩⟩

theorem epi_bind_trap {E cb sty st ws x} (hE : EpiOk M E cb sty st) (res : Option PTy) :
    (epiTail M E cb sty st.next ws >>= fun ws' => RM.ofOption (valsRes res ws'))
        (x, (startSync st).1) .trap ↔ valsRes res ws = none := by
  obtain ⟨hall, st₀, h₀⟩ := hE ws x
  constructor
  · rintro (⟨a, s', h1, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨st', he⟩ := hall _ h1
      cases he
      rcases (ofOption_apply _ _ _).1 h2 with ⟨b, -, he⟩ | ⟨hb, -⟩
      · cases he
      · exact hb
    · obtain ⟨_, he⟩ := hall _ h1
      cases he
  · intro hv
    exact .inl ⟨ws, (x, st₀), h₀, (ofOption_apply _ _ _).2 (.inr ⟨hv, rfl⟩)⟩

theorem ofOption_ok_iff {σ α : Type} (x : Option α) (s : σ) (a : α) (s' : σ) :
    (RM.ofOption x : RM σ α) s (.ok a s') ↔ x = some a ∧ s' = s := by
  cases x <;> simp [RM.ofOption, RM.fail, RM.pure, and_comm, eq_comm]

theorem ofOption_trap_iff {σ α : Type} (x : Option α) (s : σ) :
    (RM.ofOption x : RM σ α) s .trap ↔ x = none := by
  cases x <;> simp [RM.ofOption, RM.fail, RM.pure]

/-- The tail after `M` returned `v` agrees with what the caller sees, over `M`'s state. -/
theorem tailK_fst {E cb sty st} (hE : EpiOk M E cb sty st) (res : Option PTy) (v : Option PVal)
    (x : M.St) :
    (∀ r y, (∃ z, tailK M E cb sty st.next res v (x, (startSync st).1) (.ok r (y, z))) ↔
        tailV M res v x (.ok r y)) ∧
      (tailK M E cb sty st.next res v (x, (startSync st).1) .trap ↔ tailV M res v x .trap) := by
  unfold tailK tailV
  cases hv : resVals v with
  | none =>
    simp only [RM.ofOption_none, RM.fail_bind]
    exact ⟨fun r y => by simp [RM.fail], by simp [RM.fail]⟩
  | some ws =>
    simp only [RM.ofOption_some, RM.pure_bind]
    exact ⟨fun r y => (epi_bind_ok M hE res r y).trans (ofOption_ok_iff _ _ _ _).symm,
      (epi_bind_trap M hE res).trans (ofOption_trap_iff _ _).symm⟩

/-- Values of a lifted computation followed by a tail that agrees with `V` over `M`'s state. -/
theorem bind_fst_ok {α : Type} (m₀ : RM M.St α) (K : α → RM M.withStore.St (Option PVal))
    (V : α → RM M.St (Option PVal)) (st : Store) (x₀ : M.St)
    (hK : ∀ v x r y, (∃ z, K v (x, st) (.ok r (y, z))) ↔ V v x (.ok r y)) (r : Option PVal)
    (y : M.St) :
    (∃ z, ((RM.liftFst m₀ : RM M.withStore.St α) >>= K) (x₀, st) (.ok r (y, z))) ↔
      (m₀ >>= V) x₀ (.ok r y) := by
  have hL := fun z => liftFst_bind_apply_ws M m₀ K (x₀, st) (.ok r (y, z))
  rw [RM.bind_apply]
  constructor
  · rintro ⟨z, hz⟩
    rcases (hL z).1 hz with ⟨v, x', hm, hk⟩ | ⟨-, he⟩
    · exact .inl ⟨v, x', hm, (hK v x' r y).1 ⟨z, hk⟩⟩
    · cases he
  · rintro (⟨v, x', hm, hk⟩ | ⟨-, he⟩)
    · obtain ⟨z, hz⟩ := (hK v x' r y).2 hk
      exact ⟨z, (hL z).2 (.inl ⟨v, x', hm, hz⟩)⟩
    · cases he

/-- Traps of a lifted computation followed by a tail that agrees with `V` over `M`'s state. -/
theorem bind_fst_trap {α : Type} (m₀ : RM M.St α) (K : α → RM M.withStore.St (Option PVal))
    (V : α → RM M.St (Option PVal)) (st : Store) (x₀ : M.St)
    (hK : ∀ v x, K v (x, st) .trap ↔ V v x .trap) :
    ((RM.liftFst m₀ : RM M.withStore.St α) >>= K) (x₀, st) .trap ↔ (m₀ >>= V) x₀ .trap := by
  refine (liftFst_bind_apply_ws M m₀ K (x₀, st) .trap).trans ?_
  rw [RM.bind_apply]
  constructor
  · rintro (⟨v, x', hm, hk⟩ | ⟨h, -⟩)
    · exact .inl ⟨v, x', hm, (hK v x').1 hk⟩
    · exact .inr ⟨h, rfl⟩
  · rintro (⟨v, x', hm, hk⟩ | ⟨h, -⟩)
    · exact .inl ⟨v, x', hm, (hK v x').2 hk⟩
    · exact .inr ⟨h, rfl⟩

/-- **An async call whose epilogue returns the values faithfully is `visible m₀` over `M`'s
state.** -/
theorem fstIs_of_epiOk (R core cb : List Flat → RM M.withStore.St (List Flat))
    (E : Nat → List Val → RM M.withStore.St (List Flat)) (sty : Style) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hE : EpiOk M E cb sty s.2) :
    FstIs M (asyncCall M R (bodyWith M core sig.result E) cb sty sig vs)
      (visible M m₀ sig.result) s := by
  have hA : asyncCall M R (bodyWith M core sig.result E) cb sty sig vs s =
      ((RM.liftFst m₀ : RM M.withStore.St _) >>= tailK M E cb sty s.2.next sig.result)
        (s.1, (startSync s.2).1) := by
    rw [asyncCall_bodyWith, hc, startTask_bind]
    rfl
  have hV : visible M m₀ sig.result = (m₀ >>= tailV M sig.result) := rfl
  have hK := fun v x => tailK_fst M hE sig.result v x
  unfold FstIs
  rw [hA, hV]
  exact ⟨bind_fst_ok M m₀ _ _ _ s.1 (fun v x => (hK v x).1),
    bind_fst_trap M m₀ _ _ _ s.1 (fun v x => (hK v x).2)⟩

/-! ## The adaptor's epilogue -/

theorem shimRun_eq (core : List Flat → RM M.withStore.St (List Flat)) (res : Option PTy)
    (sty : Style) : shimRun M core res sty = bodyWith M core res (retE M sty) := rfl

theorem taskResult_apply (t : Nat) (s : M.withStore.St) (ws : List Val)
    (h : (s.2.tasks t).result = some ws) :
    taskResult M t s = (pure ws : RM M.withStore.St (List Val)) s := by
  have e := taskResult_bind M t (fun a => pure a)
  rw [RM.bind_pure] at e
  rw [e]
  simp only [h]

/-- The adaptor's epilogue returns the values faithfully from every store. -/
theorem retE_epiOk (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (st : Store) :
    EpiOk M (retE M sty) cb sty st := by
  intro ws x
  obtain ⟨st', hstep, hres, -⟩ := step_fresh st ws
  have he : epiTail M (retE M sty) cb sty st.next ws (x, (startSync st).1) =
      (pure ws : RM M.withStore.St (List Val)) (x, st') := by
    cases sty
    · simp only [epiTail, retE, RM.bind_assoc, RM.pure_bind, Style.exitResult, List.isEmpty_nil,
        RM.check_true]
      rw [builtin_bind]
      simp only [hstep]
      exact taskResult_apply M _ (x, st') _ hres
    · simp only [epiTail, retE, RM.bind_assoc, RM.pure_bind, Style.exitResult,
        Silmaril.Proofs.Wasm.Jco.Async.drive_exit]
      rw [builtin_bind]
      simp only [hstep]
      exact taskResult_apply M _ (x, st') _ hres
  rw [he]
  exact ⟨fun o h => ⟨st', h⟩, st', rfl⟩

end Silmaril.Proofs.Wasm.Jco.Async.Wait

namespace Silmaril.Proofs.Wasm.Jco.Async.Wait

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event Chan startSync step Waits upd packCopy
  CopyResult EventCode blocked)
open Silmaril.Proofs.Wasm.Jco.Async.Frame

/-! ## The store along the stream epilogues -/

section Steps

variable (st : Store) (ws : List Val)

/-- The store after the task and `stream.new`. -/
@[expose] def st₂ : Store := ((startSync st).1.alloc2 .streamR .streamW).1

/-- After the pending `stream.write`. -/
@[expose] def st₃ : Store := (st₂ st).setChan (st.next + 1) { pend := .write (st.next + 2) ws }

/-- After the rendezvous `stream.read`. -/
@[expose] def st₄ : Store :=
  ((st₃ st ws).setChan (st.next + 1) { pend := .idle, sent := ws }).post (st.next + 2)
    ⟨.streamWrite, st.next + 2, packCopy .completed ws.length, []⟩

theorem step_new : step (startSync st).1 .streamNew = some (st₂ st, .ends (st.next + 1) (st.next + 2)) :=
  rfl

theorem step_write (hf : st.chans (st.next + 1) = {}) :
    step (st₂ st) (.streamWrite (st.next + 2) ws) = some (st₃ st ws, .nat blocked) := by
  simp [step, Silmaril.Wasm.Component.Async.streamWrite, st₂, st₃, Store.alloc2, upd, startSync, hf]

theorem step_read :
    step (st₃ st ws) (.streamRead (st.next + 1) ws.length) =
      some (st₄ st ws, .read (packCopy .completed ws.length) ws) := by
  simp [step, Silmaril.Wasm.Component.Async.streamRead, st₂, st₃, st₄, Store.alloc2, upd, startSync,
    Store.setChan]

theorem st₄_next : (st₄ st ws).next = st.next + 3 := by
  simp [st₄, st₃, st₂, Store.alloc2, startSync, Store.setChan, Store.post]

theorem st₄_tbl : (st₄ st ws).tbl (st.next + 2) = some (.streamW (st.next + 1)) := by
  simp [st₄, st₃, st₂, Store.alloc2, startSync, Store.setChan, Store.post, upd]

theorem st₄_ev : (st₄ st ws).ev (st.next + 2) =
    some ⟨.streamWrite, st.next + 2, packCopy .completed ws.length, []⟩ := by
  simp [st₄, Store.post, upd]

theorem st₄_task : ((st₄ st ws).tasks st.next).result = none := by
  simp [st₄, st₃, st₂, Store.alloc2, startSync, Store.setChan, Store.post, upd]

end Steps

/-- `task.return` of a task without results: it stores them and changes no handle. -/
theorem step_taskReturn (st : Store) (t : Nat) (ws : List Val) (hr : (st.tasks t).result = none) :
    ∃ st', step st (.taskReturn t ws) = some (st', .unit) ∧ (st'.tasks t).result = some ws ∧
      st'.next = st.next ∧ st'.tbl = st.tbl ∧ (∀ h, h ≠ t → st'.ev h = st.ev h) ∧
      st'.joined = st.joined := by
  let st' : Store := { st with tasks := upd st.tasks t { result := some ws } }
  by_cases ht : st.tbl t = some (.subtask t)
  · refine ⟨st'.post t ⟨.subtask, t, Silmaril.Wasm.Component.Async.subReturned, []⟩,
      by simp [step, hr, ht, st'], by simp [Store.post, upd, st'], rfl, rfl, ?_, ?_⟩
    · intro h hh
      simp [Store.post, upd, hh, st']
    · rfl
  · exact ⟨st', by simp [step, hr, ht, st'], by simp [upd, st'], rfl, rfl, fun _ _ => rfl, rfl⟩

variable (M : CoreInst)

/-- A bind only depends on the outcomes of its first computation at the state. -/
theorem bind_at {α β : Type} {m m' : RM M.withStore.St α} {s s' : M.withStore.St}
    (h : m s = m' s') (k : α → RM M.withStore.St β) : (m >>= k) s = (m' >>= k) s' := by
  funext o
  simp only [RM.bind_apply, h]

/-- A built-in that steps to `(st', res)` hands `res` and `st'` to the continuation. -/
theorem builtin_then {β : Type} {op : Op} {st st' : Store} {res : Res}
    (h : step st op = some (st', res)) (k : Res → RM M.withStore.St β) (x : M.St) :
    (builtin M op >>= k) (x, st) = k res (x, st') := by
  rw [builtin_bind]
  dsimp only
  rw [h]

/-- **The stream pipe**: on a fresh channel, `stream.new`, the pending write, the rendezvous read
and `task.return` of the items read run deterministically, and the task holds `ws`. -/
theorem pipe_run (k : Nat → RM M.withStore.St (List Flat)) (st : Store) (ws : List Val)
    (hf : st.chans (st.next + 1) = {}) (x : M.St) :
    ∃ st₅ : Store, pipeWith M k st.next ws (x, (startSync st).1) = k (st.next + 2) (x, st₅) ∧
      (st₅.tasks st.next).result = some ws ∧ st₅.next = st.next + 3 ∧
      st₅.tbl (st.next + 2) = some (.streamW (st.next + 1)) ∧
      st₅.ev (st.next + 2) = some ⟨.streamWrite, st.next + 2, packCopy .completed ws.length, []⟩ := by
  obtain ⟨st₅, h5, hr5, hn5, ht5, he5, -⟩ :=
    step_taskReturn (st₄ st ws) st.next ws (st₄_task st ws)
  refine ⟨st₅, ?_, hr5, hn5.trans (st₄_next st ws), ht5 ▸ st₄_tbl st ws,
    (he5 _ (by omega)).trans (st₄_ev st ws)⟩
  unfold pipeWith
  refine (builtin_then M (step_new st) _ x).trans ?_
  refine (builtin_then M (step_write st ws hf) _ x).trans ?_
  refine (builtin_then M (step_read st ws) _ x).trans ?_
  exact builtin_then M h5 _ x

theorem code_toNat (si : Nat) (hsi : 16 * si + 2 < 2 ^ 32) :
    (BitVec.ofNat 32 (2 + 16 * si)).toNat % 16 = 2 ∧ (BitVec.ofNat 32 (2 + 16 * si)).toNat / 16 = si := by
  have hv : (BitVec.ofNat 32 (2 + 16 * si)).toNat = 2 + 16 * si := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hv]
  omega

/-- The outcomes of `WAIT si` with a callback answering `EXIT`. -/
theorem drive_wait_out (si : Nat) (hsi : 16 * si + 2 < 2 ^ 32) (s : M.withStore.St)
    (o : Out M.withStore.St Unit) (h : Drive M (exitCb M) (waitCode si) s o) :
    ∃ h e st', Waits s.2 si h e st' ∧ o = .ok () (s.1, st') := by
  have ⟨hm, hd⟩ := code_toNat si hsi
  have hex : @Eq (RM M.withStore.St Unit) (Drive M (exitCb M) [i32n cbExit]) (pure ()) :=
    Silmaril.Proofs.Wasm.Jco.Async.drive_exit M _
  cases h with
  | exit _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk hc hw hcb hdr =>
    have e : (Out.ok _ _ : Out M.withStore.St (List Flat)) = .ok [i32n cbExit] (s.1, _) := hcb
    cases e
    exact ⟨_, _, _, hd ▸ hw, (RM.pure_apply _ _ _).1 (hex ▸ hdr)⟩
  | waitTrap _ _ hcb => cases hcb
  | bad hb => exact absurd ⟨_, rfl, by rw [hm]⟩ hb

/-- **`WAIT` with a callback answering `EXIT`**: the loop takes the event of a member of the set
and ends; it has no other outcome. -/
theorem drive_wait_iff (si : Nat) (hsi : 16 * si + 2 < 2 ^ 32) (s : M.withStore.St)
    (o : Out M.withStore.St Unit) :
    Drive M (exitCb M) (waitCode si) s o ↔
      ∃ h e st', Waits s.2 si h e st' ∧ o = .ok () (s.1, st') := by
  refine ⟨drive_wait_out M si hsi s o, ?_⟩
  rintro ⟨h, e, st', hw, rfl⟩
  have ⟨hm, hd⟩ := code_toNat si hsi
  have hcb : exitCb M [i32n e.code.toNat, i32n e.index, i32n e.payload] (s.1, st')
      (.ok [i32n cbExit] (s.1, st')) := rfl
  exact Drive.waitOk hm (hd.symm ▸ hw) hcb (Silmaril.Proofs.Wasm.Jco.Async.drive_exit M _ ▸ rfl)

/-! ## The stream epilogues -/

/-- **The stream epilogue returns the values faithfully** on a fresh channel. -/
theorem pipeE_epiOk (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (st : Store)
    (hf : st.chans (st.next + 1) = {}) : EpiOk M (pipeE M sty.exitResult) cb sty st := by
  intro ws x
  obtain ⟨st₅, hrun, hr5, -⟩ := pipe_run M (fun _ => pure sty.exitResult) st ws hf x
  have he : epiTail M (pipeE M sty.exitResult) cb sty st.next ws (x, (startSync st).1) =
      (pure ws : RM M.withStore.St (List Val)) (x, st₅) := by
    cases sty
    · unfold epiTail pipeE
      refine (bind_at M hrun _).trans ?_
      simp only [RM.pure_bind, Style.exitResult, List.isEmpty_nil, RM.check_true]
      exact taskResult_apply M _ (x, st₅) _ hr5
    · unfold epiTail pipeE
      refine (bind_at M hrun _).trans ?_
      simp only [RM.pure_bind, Style.exitResult, Silmaril.Proofs.Wasm.Jco.Async.drive_exit]
      exact taskResult_apply M _ (x, st₅) _ hr5
  rw [he]
  exact ⟨fun o h => ⟨st₅, h⟩, st₅, rfl⟩

/-- The store after `waitable-set.new` and `waitable.join w` of it. -/
@[expose] def joinStore (st₅ : Store) (w : Nat) : Store :=
  { st₅ with next := st₅.next + 1, tbl := upd st₅.tbl st₅.next (some .wset),
             joined := upd st₅.joined w (some st₅.next) }

/-- After the pipe, `joinWait` makes a new set with the writable end as its member. -/
theorem joinWait_run (st₅ : Store) (w : Nat) (x : M.St) (hw : w < st₅.next)
    (ht : ∃ s, st₅.tbl w = some (.streamW s)) :
    joinWait M w (x, st₅) =
      (pure (waitCode st₅.next) : RM M.withStore.St (List Flat)) (x, joinStore st₅ w) := by
  obtain ⟨c, hc⟩ := ht
  have hne : w ≠ st₅.next := by omega
  have h6 : step st₅ .wsNew =
      some ({ st₅ with next := st₅.next + 1, tbl := upd st₅.tbl st₅.next (some .wset) },
        .nat st₅.next) := rfl
  have h7 : step { st₅ with next := st₅.next + 1, tbl := upd st₅.tbl st₅.next (some .wset) }
      (.join w st₅.next) = some (joinStore st₅ w, .unit) := by
    simp [step, upd, hne, hc, Silmaril.Wasm.Component.Async.Obj.isWaitable, joinStore]
    omega
  unfold joinWait
  rw [builtin_bind]
  dsimp only
  rw [h6]
  dsimp only
  rw [builtin_bind]
  dsimp only
  rw [h7]

/-- **The stream epilogue that waits returns the values faithfully** from every `Fresh` store:
the loop takes an event of the new set (the writable end's, or of another waitable joined to it)
and ends. -/
theorem pipeWaitE_epiOk (st : Store) (hF : Fresh st) :
    EpiOk M (pipeWaitE M) (exitCb M) .callback st := by
  intro ws x
  obtain ⟨st₅, hrun, hr5, hn5, ht5, he5⟩ := pipe_run M (joinWait M) st ws hF.1 x
  have hj := joinWait_run M st₅ (st.next + 2) x (by omega) ⟨_, ht5⟩
  let st₇ : Store := joinStore st₅ (st.next + 2)
  have hsi : 16 * st₅.next + 2 < 2 ^ 32 := by rw [hn5]; exact hF.2
  have he : epiTail M (pipeWaitE M) (exitCb M) .callback st.next ws (x, (startSync st).1) =
      ((Drive M (exitCb M) (waitCode st₅.next) : RM M.withStore.St Unit) >>= fun _ =>
        taskResult M st.next) (x, st₇) := by
    unfold epiTail pipeWaitE
    refine (bind_at M (hrun.trans hj) _).trans ?_
    rw [RM.pure_bind]
  have hres : ∀ h e st', Waits st₇ st₅.next h e st' → (st'.tasks st.next).result = some ws := by
    rintro h e st' ⟨-, -, -, rfl⟩
    exact hr5
  rw [he]
  constructor
  · intro o ho
    rcases (RM.bind_apply _ _ _ _).1 ho with ⟨a, s', hd, hk⟩ | ⟨hd, -⟩
    · obtain ⟨h, e, st', hw, hs⟩ := (drive_wait_iff M _ hsi _ _).1 hd
      cases hs
      have hk' := (taskResult_apply M st.next (x, st') ws (hres h e st' hw)) ▸ hk
      exact ⟨st', (RM.pure_apply _ _ _).1 hk'⟩
    · obtain ⟨_, _, _, _, hs⟩ := (drive_wait_iff M _ hsi _ _).1 hd
      cases hs
  · have hw : Waits st₇ st₅.next (st.next + 2) _ { st₇ with ev := upd st₇.ev (st.next + 2) none } :=
      ⟨by simp [st₇, joinStore, upd], by simp [st₇, joinStore, upd],
        by simpa [st₇, joinStore] using he5, rfl⟩
    refine ⟨{ st₇ with ev := upd st₇.ev (st.next + 2) none }, (RM.bind_apply _ _ _ _).2 (.inl
      ⟨(), _, (drive_wait_iff M _ hsi _ _).2 ⟨_, _, _, hw, rfl⟩, ?_⟩)⟩
    have ht := congrFun (taskResult_apply M st.next (x, { st₇ with ev := upd st₇.ev (st.next + 2) none })
      ws (hres _ _ _ hw)) (.ok ws (x, { st₇ with ev := upd st₇.ev (st.next + 2) none }))
    exact Eq.mpr ht ((RM.pure_apply _ _ _).2 rfl)

/-- **`WAIT` on a fresh empty set never ends**: when no waitable has joined the handle the set
gets, the tail of `waitE` has no outcome. -/
theorem waitE_stuck (st : Store) (hj : ∀ h, st.joined h ≠ some (st.next + 1))
    (hsi : 16 * (st.next + 1) + 2 < 2 ^ 32) (ws : List Val) (x : M.St)
    (o : Out M.withStore.St (List Val)) :
    ¬ epiTail M (waitE M) (exitCb M) .callback st.next ws (x, (startSync st).1) o := by
  have hr : (((startSync st).1).tasks st.next).result = none := by
    simp [startSync, upd]
  obtain ⟨st₂, h2, -, hn2, -, -, hj2⟩ := step_taskReturn _ st.next ws hr
  have hn : st₂.next = st.next + 1 := hn2
  have h3 : step st₂ .wsNew =
      some ({ st₂ with next := st₂.next + 1, tbl := upd st₂.tbl st₂.next (some .wset) },
        .nat st₂.next) := rfl
  have hrun : waitE M st.next ws (x, (startSync st).1) =
      (pure (waitCode st₂.next) : RM M.withStore.St (List Flat))
        (x, { st₂ with next := st₂.next + 1, tbl := upd st₂.tbl st₂.next (some .wset) }) := by
    unfold waitE
    rw [builtin_bind]
    dsimp only
    rw [h2]
    dsimp only
    rw [builtin_bind]
    dsimp only
    rw [h3]
  have he : epiTail M (waitE M) (exitCb M) .callback st.next ws (x, (startSync st).1) =
      ((Drive M (exitCb M) (waitCode st₂.next) : RM M.withStore.St Unit) >>= fun _ =>
        taskResult M st.next)
        (x, { st₂ with next := st₂.next + 1, tbl := upd st₂.tbl st₂.next (some .wset) }) := by
    unfold epiTail
    refine (bind_at M hrun _).trans ?_
    rw [RM.pure_bind]
  have hsi' : 16 * st₂.next + 2 < 2 ^ 32 := by rw [hn]; exact hsi
  have hnone : ∀ o', ¬ Drive M (exitCb M) (waitCode st₂.next)
      (x, { st₂ with next := st₂.next + 1, tbl := upd st₂.tbl st₂.next (some .wset) }) o' := by
    intro o' hd
    obtain ⟨h, _, _, ⟨-, hjh, -⟩, -⟩ := (drive_wait_iff M _ hsi' _ _).1 hd
    have hjs : st.joined h = some (st.next + 1) := by
      rw [← hn]
      simpa [hj2, startSync] using hjh
    exact hj h hjs
  rw [he]
  rintro (⟨_, _, hd, -⟩ | ⟨hd, -⟩)
  · exact hnone _ hd
  · exact hnone _ hd

/-! ## The yielding epilogue -/

theorem shimRunWith_eq (core : List Flat → RM M.withStore.St (List Flat)) (res : Option PTy) :
    shimRunWith M core res [i32n cbYield] = bodyWith M core res (yieldE M) := rfl

/-- The yielding epilogue with a callback answering `EXIT` returns the values faithfully. -/
theorem yieldE_epiOk (cb : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) (st : Store) : EpiOk M (yieldE M) cb .callback st := by
  intro ws x
  obtain ⟨st', hstep, hres, -⟩ := step_fresh st ws
  have he : epiTail M (yieldE M) cb .callback st.next ws (x, (startSync st).1) =
      (pure ws : RM M.withStore.St (List Val)) (x, st') := by
    simp only [epiTail, yieldE, RM.bind_assoc, RM.pure_bind,
      Silmaril.Proofs.Wasm.Jco.Async.Native.drive_yield_exit M cb hcb]
    rw [builtin_bind]
    simp only [hstep]
    exact taskResult_apply M _ (x, st') _ hres
  rw [he]
  exact ⟨fun o h => ⟨st', h⟩, st', rfl⟩

/-- **The epilogues of `NInst.Inlines` return the values faithfully from every store.** -/
theorem inlines_epilogues (N : NInst M) (md : AMeta) (hN : N.Inlines md) :
    N.Epilogues md fun _ => True := by
  intro s hs sty hst
  rcases hN s hs sty hst with hb | ⟨rfl, hb, hcb⟩
  · exact ⟨retE M sty, hb.trans (shimRun_eq M _ _ sty), fun st _ => retE_epiOk M _ sty st⟩
  · exact ⟨yieldE M, hb.trans (shimRunWith_eq M _ _), fun st _ => yieldE_epiOk M _ hcb st⟩

/-! ## Agreement with `awrap` -/

theorem sameFst_of_fstIs {α : Type} {m₁ m₂ : RM M.withStore.St α} {v : RM M.St α}
    {s : M.withStore.St} (h₁ : FstIs M m₁ v s) (h₂ : FstIs M m₂ v s) : SameFst M m₁ m₂ s :=
  ⟨fun a x => (h₁.1 a x).trans (h₂.1 a x).symm, h₁.2.trans h₂.2.symm⟩

theorem sameFst_refl {α : Type} (m : RM M.withStore.St α) (s : M.withStore.St) :
    SameFst M m m s :=
  ⟨fun _ _ => Iff.rfl, Iff.rfl⟩

/-- The synchronous lift of `M`'s export over `M.withStore` is the lifted C convention. -/
theorem canon_liftFst (md : AMeta) (R : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (hs : inMem sig.result = false)
    (hp : ∀ vs, lowerParams M.withStore R sig.params vs =
      md.sync.specParams M.withStore sig.params vs) (vs : List PVal) :
    canonCall M.withStore R (M.withStore.call sig.name) sig vs =
      RM.liftFst (md.sync.specCall M sig vs) :=
  (canonCall_specCall M.withStore md.sync sig hs hp vs).trans
    (Silmaril.Proofs.Wasm.Jco.Async.Frame.specCall_withStore M md.sync sig vs)

/-- **An async function of `aspec` is `visible` of the C convention over `M`'s state.** -/
theorem aspecCall_fstIs (md : AMeta) (R : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (sty : Style) (hs : inMem sig.result = false)
    (hp : ∀ vs, lowerParams M.withStore R sig.params vs =
      md.sync.specParams M.withStore sig.params vs) (vs : List PVal) (s : M.withStore.St) :
    FstIs M (aspecCall M md ⟨sig, some sty⟩ vs) (visible M (md.sync.specCall M sig vs) sig.result)
      s := by
  rw [← Silmaril.Proofs.Wasm.Jco.Async.Native.asyncCall_shim_spec M md R (AComp.noCallback M) sig sty
    hs hp vs, shimRun_eq]
  exact fstIs_of_epiOk M R _ _ _ sty sig vs _ (canon_liftFst M md R sig hs hp vs) s
    (retE_epiOk M _ sty s.2)

/-- One async function of the native convention, for a module with faithful epilogues. -/
theorem sameFst_async (N : NInst M) (md : AMeta) (r : String) {P : Store → Prop}
    (hN : N.Epilogues md P) (hk : md.sync.thinOk = true)
    (hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs)
    {sig : Sig} {sty : Style} (hsw : ⟨sig, some sty⟩ ∈ md.world) (vs : List PVal)
    (s : M.withStore.St) (hP : P s.2) :
    SameFst M (asyncCall M (M.withStore.call r) (N.body sig.name) (N.callback sig.name) sty sig vs)
      (aspecCall M md ⟨sig, some sty⟩ vs) s := by
  have hs : inMem sig.result = false :=
    thinOk_mem md.sync hk (Silmaril.Proofs.Wasm.Jco.Async.Native.sig_mem hsw)
  obtain ⟨E, hb, hE⟩ := hN _ hsw sty rfl
  have h₁ : FstIs M (asyncCall M (M.withStore.call r) (N.body sig.name) (N.callback sig.name)
      sty sig vs) (visible M (md.sync.specCall M sig vs) sig.result) s := by
    rw [hb]
    exact fstIs_of_epiOk M _ _ _ E sty sig vs _ (canon_liftFst M md _ sig hs (hp _ hsw) vs) s
      (hE s.2 hP)
  exact sameFst_of_fstIs M h₁ (aspecCall_fstIs M md _ sig sty hs (hp _ hsw) vs s)

/-- One synchronous function of the native convention: the same computation. -/
theorem sameFst_sync (md : AMeta) (r : String) (hk : md.sync.thinOk = true)
    (hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs)
    {sig : Sig} (hsw : ⟨sig, none⟩ ∈ md.world) (vs : List PVal) (s : M.withStore.St) :
    SameFst M (canonCall M.withStore (M.withStore.call r) (M.withStore.call sig.name) sig vs)
      (aspecCall M md ⟨sig, none⟩ vs) s := by
  have hs : inMem sig.result = false :=
    thinOk_mem md.sync hk (Silmaril.Proofs.Wasm.Jco.Async.Native.sig_mem hsw)
  rw [canonCall_specCall M.withStore md.sync sig hs (hp _ hsw) vs]
  exact sameFst_refl M _ s

/-- **The native async convention agrees with `aspec` up to the async store**, for a module
whose async bodies have epilogues that return the values faithfully from the stores `P`. -/
theorem canonSpecA_sameFst (N : NInst M) (md : AMeta) (r : String) {P : Store → Prop}
    (hN : N.Epilogues md P) (hk : md.sync.thinOk = true)
    (hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs)
    (name : String) (vs : List PVal) (s : M.withStore.St) (hP : P s.2) :
    SameFst M (canonSpecA N md r name vs) (aspec M md name vs) s := by
  unfold canonSpecA aspec
  cases hf : md.world.find? (·.sig.name == name) with
  | none => exact sameFst_refl M _ s
  | some a =>
    rcases a with ⟨sig, _ | sty⟩
    · exact sameFst_sync M md r hk hp (List.mem_of_find?_eq_some hf) vs s
    · exact sameFst_async M N md r hN hk hp (List.mem_of_find?_eq_some hf) vs s hP

/-! ## Modules whose bodies use streams and wait -/

theorem piped_epilogues (md : AMeta) (hn : (md.world.map (·.sig.name)).Nodup) :
    (NInst.piped M md).Epilogues md fun st => st.chans (st.next + 1) = {} := by
  intro s hs sty hst
  refine ⟨pipeE M sty.exitResult, ?_, fun st hf => pipeE_epiOk M _ sty st hf⟩
  show (match md.world.find? (·.sig.name == s.sig.name) with
    | some ⟨sig, some st⟩ => bodyWith M (M.withStore.call s.sig.name) sig.result
        (pipeE M st.exitResult)
    | _ => fun _ _ => RM.fail) = _
  rw [Silmaril.Proofs.Wasm.Jco.Async.Native.find_name_nodup hn hs]
  rcases s with ⟨sig, _ | st⟩
  · cases hst
  · cases hst
    rfl

theorem pipedWait_epilogues (md : AMeta) (hn : (md.world.map (·.sig.name)).Nodup)
    (hc : ∀ s ∈ md.world, ∀ sty, s.async = some sty → sty = .callback) :
    (NInst.pipedWait M md).Epilogues md Fresh := by
  intro s hs sty hst
  obtain rfl := hc s hs sty hst
  refine ⟨pipeWaitE M, ?_, fun st hf => pipeWaitE_epiOk M st hf⟩
  show (match md.world.find? (·.sig.name == s.sig.name) with
    | some ⟨sig, some _⟩ => bodyWith M (M.withStore.call s.sig.name) sig.result (pipeWaitE M)
    | _ => fun _ _ => RM.fail) = _
  rw [Silmaril.Proofs.Wasm.Jco.Async.Native.find_name_nodup hn hs]
  rcases s with ⟨sig, _ | st⟩
  · cases hst
  · rfl

/-- **A body that returns and then waits on an empty set never returns to its caller**: no
outcome of the call is a value. -/
theorem asyncCall_waitE_noOk (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hj : ∀ h, s.2.joined h ≠ some (s.2.next + 1)) (hsi : 16 * (s.2.next + 1) + 2 < 2 ^ 32)
    (r : Option PVal) (s' : M.withStore.St) :
    ¬ asyncCall M R (bodyWith M core sig.result (waitE M)) (exitCb M) .callback sig vs s
      (.ok r s') := by
  have hA : asyncCall M R (bodyWith M core sig.result (waitE M)) (exitCb M) .callback sig vs s =
      ((RM.liftFst m₀ : RM M.withStore.St _) >>=
        tailK M (waitE M) (exitCb M) .callback s.2.next sig.result) (s.1, (startSync s.2).1) := by
    rw [asyncCall_bodyWith, hc, startTask_bind]
    rfl
  have hL := liftFst_bind_apply_ws M m₀ (tailK M (waitE M) (exitCb M) .callback s.2.next sig.result)
    (s.1, (startSync s.2).1) (.ok r s')
  rw [hA]
  intro h
  rcases hL.1 h with ⟨v, x', -, hk⟩ | ⟨-, he⟩
  · rcases (RM.bind_apply _ _ _ _).1 hk with ⟨ws, s₁, hw, hk'⟩ | ⟨-, he⟩
    · rcases (ofOption_apply _ _ _).1 hw with ⟨_, -, he⟩ | ⟨-, he⟩
      · cases he
        rcases (RM.bind_apply _ _ _ _).1 hk' with ⟨_, _, he', -⟩ | ⟨he', -⟩
        · exact waitE_stuck M s.2 hj hsi ws x' _ he'
        · exact waitE_stuck M s.2 hj hsi ws x' _ he'
      · cases he
    · cases he
  · cases he

end Silmaril.Proofs.Wasm.Jco.Async.Wait
