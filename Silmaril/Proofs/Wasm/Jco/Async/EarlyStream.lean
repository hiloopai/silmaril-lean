module

public import Silmaril.Proofs.Wasm.Jco.Async.Early

/-!
# A function whose result is a stream: proofs

Proofs of the stream part of `Silmaril.Wasm.Jco.Async.Early.Thms`. From a store `st` whose handles
from `st.next` on are `Unused`, the task is `st.next`, the stream's readable end `st.next + 1`
(also the channel), its writable end `st.next + 2` and the waitable set `st.next + 3`.

* `sB`: the store when the caller continues (`task.return` of the readable end done);
  `asyncCallK_stream`: the caller's continuation runs there, with the values of `M`.
* `sD`: after the rest of the body (`stream.write`, pending, and `WAIT` on the joined set);
  `stream_post`.
* `stream_hangs`: from `sD` the callback loop alone has no outcome.
* `sE`: after the caller's `stream.read r m`, which delivers the first `min m |ws|` values
  (`stream_read`); `sF`: after the callback loop with `closeCb` (`stream_close`), where the
  writable end is dropped and the next read reports the end of the stream (`stream_eos`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Early

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event Chan startSync step Waits upd packCopy
  CopyResult EventCode blocked)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait

/-! ## The stores -/

section Stores

variable (st : Store) (ws : List Val)

/-- The readable end's handle as the value `task.return` passes. -/
@[expose] def hVal : Val := Val.u32 (BitVec.ofNat 32 (st.next + 1))

/-- The store when the caller continues. -/
@[expose] def sB : Store :=
  { st₂ st with tasks := upd (st₂ st).tasks st.next { result := some [hVal st] } }

/-- After the pending `stream.write`. -/
@[expose] def sC : Store := (sB st).setChan (st.next + 1) { pend := .write (st.next + 2) ws }

/-- After `waitable-set.new` and `waitable.join` of the writable end. -/
@[expose] def sD : Store := joinStore (sC st ws) (st.next + 2)

/-- The values the caller's read of `m` items delivers. -/
@[expose] def got (m : Nat) : List Val := ws.take (min m ws.length)

/-- After the caller's `stream.read r m`. -/
@[expose] def sE (m : Nat) : Store :=
  ((sD st ws).setChan (st.next + 1) { pend := .idle, sent := got ws m }).post (st.next + 2)
    ⟨.streamWrite, st.next + 2, packCopy .completed (min m ws.length), []⟩

/-- After the wait took the writable end's event. -/
@[expose] def sE' (m : Nat) : Store :=
  { sE st ws m with ev := upd (sE st ws m).ev (st.next + 2) none }

/-- After `closeCb` dropped the writable end. -/
@[expose] def sF (m : Nat) : Store :=
  ((sE' st ws m).setChan (st.next + 1) { pend := .idle, sent := got ws m, wDropped := true }).remove
    (st.next + 2)

end Stores

theorem st₂_tbl (st : Store) (h : Nat) :
    (st₂ st).tbl h = if h = st.next + 2 then some (.streamW (st.next + 1))
      else if h = st.next + 1 then some (.streamR (st.next + 1)) else st.tbl h := by
  simp only [st₂, Store.alloc2, startSync, upd]

theorem st₂_next (st : Store) : (st₂ st).next = st.next + 3 := by
  simp [st₂, Store.alloc2, startSync]

theorem sB_tbl (st : Store) (h : Nat) : (sB st).tbl h = (st₂ st).tbl h := rfl

theorem sC_tbl (st ws) (h : Nat) : (sC st ws).tbl h = (st₂ st).tbl h := rfl

theorem sC_next (st ws) : (sC st ws).next = st.next + 3 := st₂_next st

theorem sC_joined (st ws) : (sC st ws).joined = st.joined := rfl

theorem sC_ev (st ws) : (sC st ws).ev = st.ev := rfl

theorem sD_chan (st ws) : (sD st ws).chans (st.next + 1) = { pend := .write (st.next + 2) ws } := by
  simp [sD, joinStore, sC, Store.setChan, upd]

theorem sD_tbl (st ws) (h : Nat) (hh : h ≠ st.next + 3) : (sD st ws).tbl h = (st₂ st).tbl h := by
  simp only [sD, joinStore, sC_next, upd, hh, ite_false]
  rfl

theorem sD_tbl_si (st ws) : (sD st ws).tbl (st.next + 3) = some .wset := by
  simp [sD, joinStore, sC_next, upd]

theorem sD_joined (st ws) (h : Nat) :
    (sD st ws).joined h = if h = st.next + 2 then some (st.next + 3) else st.joined h := by
  simp only [sD, joinStore, sC_next, sC_joined, upd]

variable (M : CoreInst)

/-! ## The caller's part -/

theorem hVal_toNat (st : Store) (hb : st.next + 1 < 2 ^ 32) :
    (BitVec.ofNat 32 (st.next + 1)).toNat = st.next + 1 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- `task.return` of the readable end on the fresh task. -/
theorem step_retS (st : Store) (hU : Unused st) :
    step (st₂ st) (.taskReturn st.next [hVal st]) = some (sB st, .unit) := by
  have h0 : st.tbl st.next = none := (hU st.next (Nat.le_refl _)).1
  have hr : ((st₂ st).tasks st.next).result = none := by
    simp [st₂, Store.alloc2, startSync, upd]
  have ht : (st₂ st).tbl st.next = none := by
    rw [st₂_tbl]
    simp [h0]
  simp [step, hr, ht, sB]

/-- The caller's view decomposed: the C convention, then the tail. -/
theorem asyncCallK_eq {L β : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : Split M L) (sig : Sig) (vs : List PVal) (k : Nat → List Val → L → RM M.withStore.St β) :
    asyncCallK M R core b sig vs k =
      (startTask M >>= fun t => canonCall M.withStore R core sig vs >>= fun v =>
        RM.ofOption (resVals v) >>= fun ws => b.pre t ws >>= fun p =>
          builtin M (.taskReturn t p.1) >>= fun _ => k t p.1 p.2) := by
  simp only [asyncCallK, canonCall, RM.bind_assoc]

/-- The tail of the stream function after `M` returned `v`. -/
@[expose] def streamK {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (t : Nat) (v : Option PVal) : RM M.withStore.St β :=
  RM.ofOption (resVals v) >>= fun ws => (streamSplit M).pre t ws >>= fun p =>
    builtin M (.taskReturn t p.1) >>= fun _ => k t p.1 p.2

theorem streamK_apply {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (st : Store) (hU : Unused st) (v : Option PVal) (x : M.St) :
    streamK M k st.next v (x, (startSync st).1) =
      match resVals v with
      | some ws => k st.next [hVal st] (st.next + 2, ws) (x, sB st)
      | none => RM.fail (x, (startSync st).1) := by
  unfold streamK
  cases resVals v with
  | none => simp only [RM.ofOption_none, RM.fail_bind]
  | some ws =>
    simp only [RM.ofOption_some, RM.pure_bind, streamSplit, RM.bind_assoc]
    refine (builtin_then M (step_new st) _ x).trans ?_
    simp only [RM.pure_bind]
    exact builtin_then M (step_retS st hU) _ x

/-- The tail of the stream function, as outcomes. -/
theorem streamK_iff {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (st : Store) (hU : Unused st) (v : Option PVal) (x : M.St) (o : Out M.withStore.St β) :
    streamK M k st.next v (x, (startSync st).1) o ↔
      (∃ ws, resVals v = some ws ∧ k st.next [hVal st] (st.next + 2, ws) (x, sB st) o) ∨
        (resVals v = none ∧ o = .trap) := by
  rw [streamK_apply M k st hU v x]
  cases resVals v with
  | none => simp [RM.fail]
  | some ws => simp

/-- **The caller of the stream function**: its continuation runs at `sB` with the readable end
and the values of `M`, or the call traps. -/
theorem asyncCallK_stream {β : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (o : Out M.withStore.St β) :
    asyncCallK M R core (streamSplit M) sig vs k s o ↔
      (∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧
          k s.2.next [hVal s.2] (s.2.next + 2, ws) (x, sB s.2) o) ∨
        (o = .trap ∧ (m₀ s.1 .trap ∨ ∃ v x, m₀ s.1 (.ok v x) ∧ resVals v = none)) := by
  have hA : asyncCallK M R core (streamSplit M) sig vs k s =
      ((RM.liftFst m₀ : RM M.withStore.St _) >>= streamK M k s.2.next) (s.1, (startSync s.2).1) := by
    rw [asyncCallK_eq, hc, startTask_bind]
    rfl
  have hL := liftFst_bind_apply_ws M m₀ (streamK M k s.2.next) (s.1, (startSync s.2).1) o
  have hK := fun v x => streamK_iff M k s.2 hU v x o
  rw [hA]
  refine hL.trans ?_
  constructor
  · rintro (⟨v, x, hm, hk⟩ | ⟨hm, rfl⟩)
    · rcases (hK v x).1 hk with ⟨ws, hv, hk'⟩ | ⟨hv, rfl⟩
      · exact .inl ⟨v, x, ws, hm, hv, hk'⟩
      · exact .inr ⟨rfl, .inr ⟨v, x, hm, hv⟩⟩
    · exact .inr ⟨rfl, .inl hm⟩
  · rintro (⟨v, x, ws, hm, hv, hk⟩ | ⟨rfl, hm | ⟨v, x, hm, hv⟩⟩)
    · exact .inl ⟨v, x, hm, (hK v x).2 (.inl ⟨ws, hv, hk⟩)⟩
    · exact .inr ⟨hm, rfl⟩
    · exact .inl ⟨v, x, hm, (hK v x).2 (.inr ⟨hv, rfl⟩)⟩

/-- The caller's continuation of `asyncCallS` at `sB`: the readable end. -/
theorem handle_k (st : Store) (hb : st.next + 1 < 2 ^ 32) (x : M.St) (h : Nat)
    (s' : M.withStore.St) :
    ((match [hVal st] with
      | [Val.u32 h] => pure h.toNat
      | _ => RM.fail) : RM M.withStore.St Nat) (x, sB st) (.ok h s') ↔
        h = st.next + 1 ∧ s' = (x, sB st) := by
  show (pure (BitVec.ofNat 32 (st.next + 1)).toNat : RM M.withStore.St Nat) _ _ ↔ _
  refine (RM.pure_apply _ _ _).trans ?_
  rw [hVal_toNat st hb]
  constructor
  · intro e
    cases e
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The caller gets the readable end** `s.2.next + 1`, with `M`'s state of its C convention. -/
theorem asyncCallS_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (hb : s.2.next + 1 < 2 ^ 32) (h : Nat) (s' : M.withStore.St) :
    asyncCallS M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next + 1 ∧ s' = (x, sB s.2) := by
  refine (asyncCallK_stream M R core sig vs m₀ hc s hU _ _).trans ?_
  have hk := fun x => handle_k M s.2 hb x h s'
  constructor
  · rintro (⟨v, x, ws, hm, hv, hk'⟩ | ⟨he, -⟩)
    · exact ⟨v, x, ws, hm, hv, (hk x).1 hk'⟩
    · cases he
  · rintro ⟨v, x, ws, hm, hv, hh⟩
    exact .inl ⟨v, x, ws, hm, hv, (hk x).2 hh⟩

/-! ## The callee's part -/

/-- The rest of the body: the write stays pending and the body waits on the joined set. -/
theorem stream_post (st : Store) (hU : Unused st) (ws : List Val) (x : M.St) :
    (streamSplit M).post st.next (st.next + 2, ws) (x, sB st) =
      (pure (waitCode (st.next + 3)) : RM M.withStore.St (List Flat)) (x, sD st ws) := by
  have hc : (sB st).chans (st.next + 1) = {} := by
    have := (hU (st.next + 1) (by omega)).2.1
    simpa [sB, st₂, Store.alloc2, startSync] using this
  have hw : step (sB st) (.streamWrite (st.next + 2) ws) = some (sC st ws, .nat blocked) := by
    simp [step, Silmaril.Wasm.Component.Async.streamWrite, sB_tbl, st₂_tbl, hc, sC]
  show (builtin M (.streamWrite (st.next + 2) ws) >>= fun _ => joinWait M (st.next + 2)) _ = _
  refine (builtin_then M hw _ x).trans ?_
  rw [joinWait_run M (sC st ws) (st.next + 2) x (by rw [sC_next]; omega)
    ⟨st.next + 1, by rw [sC_tbl, st₂_tbl]; simp⟩, sC_next]
  rfl

/-- No member of the set has an event at `sD`. -/
theorem sD_noWaits (st : Store) (hU : Unused st) (ws : List Val) (h : Nat) (e : Event)
    (st' : Store) : ¬ Waits (sD st ws) (st.next + 3) h e st' := by
  rintro ⟨-, hj, he, -⟩
  rw [sD_joined] at hj
  split_ifs at hj with hh
  · subst hh
    have : (sD st ws).ev (st.next + 2) = st.ev (st.next + 2) := rfl
    rw [this, (hU (st.next + 2) (by omega)).2.2.1] at he
    cases he
  · exact (hU (st.next + 3) (by omega)).2.2.2.2 h hj

/-- **Alone, the callee never finishes**: from `sD` the callback loop has no outcome, for any
callback. The body waits for a reader. -/
theorem stream_hangs (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (x : M.St) (cb : List Flat → RM M.withStore.St (List Flat))
    (o : Out M.withStore.St Unit) : ¬ Drive M cb (waitCode (st.next + 3)) (x, sD st ws) o := by
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  intro h
  cases h with
  | exit _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk _ hw => exact sD_noWaits st hU ws _ _ _ (hd ▸ hw)
  | waitTrap _ hw => exact sD_noWaits st hU ws _ _ _ (hd ▸ hw)
  | bad hb' => exact absurd ⟨_, rfl, by rw [hm]⟩ hb'

/-- **The caller's read delivers the values** (the first `m`), completing the rendezvous; the
writable end gets its event. -/
theorem stream_read (st : Store) (ws : List Val) (m : Nat) :
    step (sD st ws) (.streamRead (st.next + 1) m) =
      some (sE st ws m, .read (packCopy .completed (min m ws.length)) (got ws m)) := by
  have ht : (sD st ws).tbl (st.next + 1) = some (.streamR (st.next + 1)) := by
    rw [sD_tbl st ws _ (by omega), st₂_tbl]
    simp
  simp only [step, Silmaril.Wasm.Component.Async.streamRead, ht, sD_chan]
  simp [sE, got]

/-- After the read, the callback loop with `closeCb` takes the writable end's event, drops the
writable end and ends. -/
theorem stream_close (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val)
    (m : Nat) (x : M.St) :
    Drive M (closeCb M) (waitCode (st.next + 3)) (x, sE st ws m) (.ok () (x, sF st ws m)) := by
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  have hw : Waits (sE st ws m) (st.next + 3) (st.next + 2)
      ⟨.streamWrite, st.next + 2, packCopy .completed (min m ws.length), []⟩ (sE' st ws m) := by
    refine ⟨?_, ?_, ?_, rfl⟩
    · simp [sE, Store.setChan, Store.post, sD_tbl_si]
    · simp [sE, Store.setChan, Store.post, sD_joined]
    · simp [sE, Store.post, upd]
  have hw32 : (BitVec.ofNat 32 (st.next + 2)).toNat = st.next + 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htw : (sE' st ws m).tbl (st.next + 2) = some (.streamW (st.next + 1)) := by
    show (sD st ws).tbl (st.next + 2) = _
    rw [sD_tbl st ws _ (by omega), st₂_tbl]
    simp
  have hcw : (sE' st ws m).chans (st.next + 1) = { pend := .idle, sent := got ws m } := by
    simp [sE', sE, Store.setChan, Store.post, upd]
  have hdrop : step (sE' st ws m) (.streamDropW (st.next + 2)) = some (sF st ws m, .unit) := by
    simp only [step, Silmaril.Wasm.Component.Async.streamDropW, htw, hcw]
    rfl
  have hcb : closeCb M [i32n EventCode.streamWrite.toNat, i32n (st.next + 2),
      i32n (packCopy .completed (min m ws.length))] (x, sE' st ws m)
      (.ok [i32n cbExit] (x, sF st ws m)) := by
    show (builtin M (.streamDropW (BitVec.ofNat 32 (st.next + 2)).toNat) >>= fun _ =>
      pure [i32n cbExit]) _ _
    rw [hw32, builtin_then M hdrop _ x]
    rfl
  exact Drive.waitOk hm (hd.symm ▸ hw) hcb
    (Silmaril.Proofs.Wasm.Jco.Async.drive_exit M _ ▸ rfl)

/-- **After the callback, the next read reports the end of the stream.** -/
theorem stream_eos (st : Store) (ws : List Val) (m m' : Nat) :
    step (sF st ws m) (.streamRead (st.next + 1) m') =
      some (sF st ws m, .read (packCopy .dropped 0) []) := by
  have ht : (sF st ws m).tbl (st.next + 1) = some (.streamR (st.next + 1)) := by
    show upd (sD st ws).tbl (st.next + 2) none (st.next + 1) = _
    simp only [upd, show st.next + 1 ≠ st.next + 2 by omega, ite_false]
    rw [sD_tbl st ws _ (by omega), st₂_tbl]
    simp
  have hc : (sF st ws m).chans (st.next + 1) =
      { pend := .idle, sent := got ws m, wDropped := true } := by
    simp [sF, Store.remove, Store.setChan, upd]
  simp only [step, Silmaril.Wasm.Component.Async.streamRead, ht, hc]
  rfl

/-- The task's results stay: the readable end. -/
theorem sF_result (st : Store) (ws : List Val) (m : Nat) :
    ((sF st ws m).tasks st.next).result = some [hVal st] := by
  simp [sF, sE', sE, sD, joinStore, sC, sB, Store.remove, Store.setChan, Store.post, upd]

end Silmaril.Proofs.Wasm.Jco.Async.Early
