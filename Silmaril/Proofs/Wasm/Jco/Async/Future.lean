module

public import Silmaril.Wasm.Jco.Async.Future.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms

/-!
# A function whose result is a future: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Future.Thms`. From a store `st` whose handles from `st.next` on
are `Unused`, the task is `st.next`, the future's readable end `st.next + 1` (also the channel),
its writable end `st.next + 2` and the waitable set `st.next + 3`.

* `fA`: after `future.new`; `fB`: when the caller continues (`task.return` of the readable end);
  `asyncCallK_future`: the caller's continuation runs there, with the values of `M`.
* `fD`: after the rest of the body (`future.write`, pending, and `WAIT` on the joined set);
  `future_post`. `future_hangs`: from `fD` the callback loop alone has no outcome.
* `fE`: after the caller's `future.read r`, which delivers the value (`future_read`); `fF`: after
  the callback loop with `closeFCb` (`future_close`), which has no other outcome
  (`future_close_iff`). There a second read traps (`future_done`).

The uniqueness of the stream's loop (`stream_close_iff`) is in `FutureStream`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Future

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event Chan startSync step Waits upd packCopy
  CopyResult EventCode blocked)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait
open Silmaril.Proofs.Wasm.Jco.Async.Early

/-! ## The stores -/

section Stores

variable (st : Store) (v : Val)

/-- After the task and `future.new`. -/
@[expose] def fA : Store := ((startSync st).1.alloc2 .futureR .futureW).1

/-- The store when the caller continues. -/
@[expose] def fB : Store :=
  { fA st with tasks := upd (fA st).tasks st.next { result := some [hVal st] } }

/-- After the pending `future.write`. -/
@[expose] def fC : Store := (fB st).setChan (st.next + 1) { pend := .write (st.next + 2) [v] }

/-- After `waitable-set.new` and `waitable.join` of the writable end. -/
@[expose] def fD : Store := joinStore (fC st v) (st.next + 2)

/-- After the caller's `future.read r`. -/
@[expose] def fE : Store :=
  ((fD st v).setChan (st.next + 1) { pend := .idle, done := true, sent := [v] }).post (st.next + 2)
    ⟨.futureWrite, st.next + 2, CopyResult.completed.toNat, []⟩

/-- After the wait took the writable end's event. -/
@[expose] def fE' : Store := { fE st v with ev := upd (fE st v).ev (st.next + 2) none }

/-- After `closeFCb` dropped the writable end. -/
@[expose] def fF : Store :=
  ((fE' st v).setChan (st.next + 1)
    { pend := .idle, done := true, sent := [v], wDropped := true }).remove (st.next + 2)

end Stores

theorem fA_tbl (st : Store) (h : Nat) :
    (fA st).tbl h = if h = st.next + 2 then some (.futureW (st.next + 1))
      else if h = st.next + 1 then some (.futureR (st.next + 1)) else st.tbl h := by
  simp only [fA, Store.alloc2, startSync, upd]

theorem fA_next (st : Store) : (fA st).next = st.next + 3 := by
  simp [fA, Store.alloc2, startSync]

theorem fC_next (st : Store) (v : Val) : (fC st v).next = st.next + 3 := fA_next st

theorem fC_tbl (st : Store) (v : Val) (h : Nat) : (fC st v).tbl h = (fA st).tbl h := rfl

theorem fD_tbl (st : Store) (v : Val) (h : Nat) (hh : h ≠ st.next + 3) :
    (fD st v).tbl h = (fA st).tbl h := by
  simp only [fD, joinStore, fC_next, upd, hh, ite_false]
  rfl

theorem fD_tbl_si (st : Store) (v : Val) : (fD st v).tbl (st.next + 3) = some .wset := by
  simp [fD, joinStore, fC_next, upd]

theorem fD_joined (st : Store) (v : Val) (h : Nat) :
    (fD st v).joined h = if h = st.next + 2 then some (st.next + 3) else st.joined h := by
  simp only [fD, joinStore, fC_next, upd]
  rfl

theorem fD_chan (st : Store) (v : Val) :
    (fD st v).chans (st.next + 1) = { pend := .write (st.next + 2) [v] } := by
  simp [fD, joinStore, fC, Store.setChan, upd]

theorem step_fnew (st : Store) :
    step (startSync st).1 .futureNew = some (fA st, .ends (st.next + 1) (st.next + 2)) := rfl

/-- `task.return` of the readable end on the fresh task. -/
theorem step_fret (st : Store) (hU : Unused st) :
    step (fA st) (.taskReturn st.next [hVal st]) = some (fB st, .unit) := by
  have h0 : st.tbl st.next = none := (hU st.next (Nat.le_refl _)).1
  have hr : ((fA st).tasks st.next).result = none := by
    simp [fA, Store.alloc2, startSync, upd]
  have ht : (fA st).tbl st.next = none := by
    rw [fA_tbl]
    simp [h0]
  simp [step, hr, ht, fB]

/-- After the pipe-free tail, `joinWait` makes a new set with the waitable `w` as its member (any
waitable, not only a stream's writable end). -/
theorem joinWait_run' (M : CoreInst) (st₅ : Store) (w : Nat) (x : M.St) (hw : w < st₅.next)
    (ht : ∃ o, st₅.tbl w = some o ∧ o.isWaitable = true) :
    joinWait M w (x, st₅) =
      (pure (waitCode st₅.next) : RM M.withStore.St (List Flat)) (x, joinStore st₅ w) := by
  obtain ⟨o, hc, ho⟩ := ht
  have hne : w ≠ st₅.next := by omega
  have h6 : step st₅ .wsNew =
      some ({ st₅ with next := st₅.next + 1, tbl := upd st₅.tbl st₅.next (some .wset) },
        .nat st₅.next) := rfl
  have h7 : step { st₅ with next := st₅.next + 1, tbl := upd st₅.tbl st₅.next (some .wset) }
      (.join w st₅.next) = some (joinStore st₅ w, .unit) := by
    simp [step, upd, hne, hc, ho, joinStore]
    omega
  unfold joinWait
  rw [builtin_bind]
  dsimp only
  rw [h6]
  dsimp only
  rw [builtin_bind]
  dsimp only
  rw [h7]

variable (M : CoreInst)

/-! ## The caller's part -/

/-- The tail of the future function after `M` returned `v`. -/
@[expose] def futureK {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (t : Nat) (v : Option PVal) : RM M.withStore.St β :=
  RM.ofOption (resVals v) >>= fun ws => (futureSplit M).pre t ws >>= fun p =>
    builtin M (.taskReturn t p.1) >>= fun _ => k t p.1 p.2

theorem futureK_apply {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (st : Store) (hU : Unused st) (v : Option PVal) (x : M.St) :
    futureK M k st.next v (x, (startSync st).1) =
      match resVals v with
      | some ws => k st.next [hVal st] (st.next + 2, ws) (x, fB st)
      | none => RM.fail (x, (startSync st).1) := by
  unfold futureK
  cases resVals v with
  | none => simp only [RM.ofOption_none, RM.fail_bind]
  | some ws =>
    simp only [RM.ofOption_some, RM.pure_bind, futureSplit, RM.bind_assoc]
    refine (builtin_then M (step_fnew st) _ x).trans ?_
    simp only [RM.pure_bind]
    exact builtin_then M (step_fret st hU) _ x

theorem futureK_iff {β : Type} (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (st : Store) (hU : Unused st) (v : Option PVal) (x : M.St) (o : Out M.withStore.St β) :
    futureK M k st.next v (x, (startSync st).1) o ↔
      (∃ ws, resVals v = some ws ∧ k st.next [hVal st] (st.next + 2, ws) (x, fB st) o) ∨
        (resVals v = none ∧ o = .trap) := by
  rw [futureK_apply M k st hU v x]
  cases resVals v with
  | none => simp [RM.fail]
  | some ws => simp

/-- **The caller of the future function**: its continuation runs at `fB` with the readable end
and the values of `M`, or the call traps. -/
theorem asyncCallK_future {β : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (k : Nat → List Val → Nat × List Val → RM M.withStore.St β)
    (o : Out M.withStore.St β) :
    asyncCallK M R core (futureSplit M) sig vs k s o ↔
      (∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧
          k s.2.next [hVal s.2] (s.2.next + 2, ws) (x, fB s.2) o) ∨
        (o = .trap ∧ (m₀ s.1 .trap ∨ ∃ v x, m₀ s.1 (.ok v x) ∧ resVals v = none)) := by
  have hA : asyncCallK M R core (futureSplit M) sig vs k s =
      ((RM.liftFst m₀ : RM M.withStore.St _) >>= futureK M k s.2.next) (s.1, (startSync s.2).1) := by
    rw [asyncCallK_eq, hc, startTask_bind]
    rfl
  have hL := liftFst_bind_apply_ws M m₀ (futureK M k s.2.next) (s.1, (startSync s.2).1) o
  have hK := fun v x => futureK_iff M k s.2 hU v x o
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

/-- The caller's continuation at `fB`: the readable end. -/
theorem handleF_k (st : Store) (hb : st.next + 1 < 2 ^ 32) (x : M.St) (h : Nat)
    (s' : M.withStore.St) :
    ((match [hVal st] with
      | [Val.u32 h] => pure h.toNat
      | _ => RM.fail) : RM M.withStore.St Nat) (x, fB st) (.ok h s') ↔
        h = st.next + 1 ∧ s' = (x, fB st) := by
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
theorem asyncCallF_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (hb : s.2.next + 1 < 2 ^ 32) (h : Nat) (s' : M.withStore.St) :
    asyncCallF M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next + 1 ∧ s' = (x, fB s.2) := by
  refine (asyncCallK_future M R core sig vs m₀ hc s hU _ _).trans ?_
  have hk := fun x => handleF_k M s.2 hb x h s'
  constructor
  · rintro (⟨v, x, ws, hm, hv, hk'⟩ | ⟨he, -⟩)
    · exact ⟨v, x, ws, hm, hv, (hk x).1 hk'⟩
    · cases he
  · rintro ⟨v, x, ws, hm, hv, hh⟩
    exact .inl ⟨v, x, ws, hm, hv, (hk x).2 hh⟩

/-! ## The callee's part -/

/-- The rest of the body: the write stays pending and the body waits on the joined set. -/
theorem future_post (st : Store) (hU : Unused st) (v : Val) (x : M.St) :
    (futureSplit M).post st.next (st.next + 2, [v]) (x, fB st) =
      (pure (waitCode (st.next + 3)) : RM M.withStore.St (List Flat)) (x, fD st v) := by
  have hc : (fB st).chans (st.next + 1) = {} := by
    have := (hU (st.next + 1) (by omega)).2.1
    simpa [fB, fA, Store.alloc2, startSync] using this
  have htw : (fB st).tbl (st.next + 2) = some (.futureW (st.next + 1)) := by
    show (fA st).tbl (st.next + 2) = _
    rw [fA_tbl]
    simp
  have hw : step (fB st) (.futureWrite (st.next + 2) v) = some (fC st v, .nat blocked) := by
    simp [step, Silmaril.Wasm.Component.Async.futureWrite, htw, hc, fC]
  show (builtin M (.futureWrite (st.next + 2) v) >>= fun _ => joinWait M (st.next + 2)) _ = _
  refine (builtin_then M hw _ x).trans ?_
  rw [joinWait_run' M (fC st v) (st.next + 2) x (by rw [fC_next]; omega)
    ⟨.futureW (st.next + 1), by rw [fC_tbl, fA_tbl]; simp, rfl⟩, fC_next]
  rfl

/-- No member of the set has an event at `fD`. -/
theorem fD_noWaits (st : Store) (hU : Unused st) (v : Val) (h : Nat) (e : Event)
    (st' : Store) : ¬ Waits (fD st v) (st.next + 3) h e st' := by
  rintro ⟨-, hj, he, -⟩
  rw [fD_joined] at hj
  split_ifs at hj with hh
  · subst hh
    have : (fD st v).ev (st.next + 2) = st.ev (st.next + 2) := rfl
    rw [this, (hU (st.next + 2) (by omega)).2.2.1] at he
    cases he
  · exact (hU (st.next + 3) (by omega)).2.2.2.2 h hj

/-- **Alone, the callee never finishes**: from `fD` the callback loop has no outcome, for any
callback. The body waits for a reader. -/
theorem future_hangs (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (v : Val) (x : M.St) (cb : List Flat → RM M.withStore.St (List Flat))
    (o : Out M.withStore.St Unit) : ¬ Drive M cb (waitCode (st.next + 3)) (x, fD st v) o := by
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  intro h
  cases h with
  | exit _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk _ hw => exact fD_noWaits st hU v _ _ _ (hd ▸ hw)
  | waitTrap _ hw => exact fD_noWaits st hU v _ _ _ (hd ▸ hw)
  | bad hb' => exact absurd ⟨_, rfl, by rw [hm]⟩ hb'

/-- **The caller's read delivers the value**, completing the rendezvous; the writable end gets
its event. -/
theorem future_read (st : Store) (v : Val) :
    step (fD st v) (.futureRead (st.next + 1)) =
      some (fE st v, .read CopyResult.completed.toNat [v]) := by
  have ht : (fD st v).tbl (st.next + 1) = some (.futureR (st.next + 1)) := by
    rw [fD_tbl st v _ (by omega), fA_tbl]
    simp
  simp only [step, Silmaril.Wasm.Component.Async.futureRead, ht, fD_chan]
  simp [fE]

/-- The only wait from `fE` takes the writable end's event. -/
theorem fE_waits (st : Store) (hU : Unused st) (v : Val) {h : Nat} {e : Event} {st' : Store}
    (hw : Waits (fE st v) (st.next + 3) h e st') :
    h = st.next + 2 ∧ e = ⟨.futureWrite, st.next + 2, CopyResult.completed.toNat, []⟩ ∧
      st' = fE' st v := by
  obtain ⟨-, hj, he, rfl⟩ := hw
  have hj' : (fD st v).joined h = some (st.next + 3) := hj
  rw [fD_joined] at hj'
  split_ifs at hj' with hh
  · subst hh
    refine ⟨rfl, ?_, rfl⟩
    have : (fE st v).ev (st.next + 2) =
        some ⟨.futureWrite, st.next + 2, CopyResult.completed.toNat, []⟩ := by
      simp [fE, Store.post, upd]
    rw [this] at he
    cases he
    rfl
  · exact absurd hj' ((hU (st.next + 3) (by omega)).2.2.2.2 h)

/-- The future's callback on the writable end's event drops it and answers `EXIT`. -/
theorem closeFCb_eq (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (v : Val) (a c : Flat)
    (x : M.St) :
    closeFCb M [a, i32n (st.next + 2), c] (x, fE' st v) =
      (pure [i32n cbExit] : RM M.withStore.St (List Flat)) (x, fF st v) := by
  have hw32 : (BitVec.ofNat 32 (st.next + 2)).toNat = st.next + 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htw : (fE' st v).tbl (st.next + 2) = some (.futureW (st.next + 1)) := by
    show (fD st v).tbl (st.next + 2) = _
    rw [fD_tbl st v _ (by omega), fA_tbl]
    simp
  have hcw : (fE' st v).chans (st.next + 1) = { pend := .idle, done := true, sent := [v] } := by
    simp [fE', fE, Store.setChan, Store.post, upd]
  have hdrop : step (fE' st v) (.futureDropW (st.next + 2)) = some (fF st v, .unit) := by
    simp only [step, Silmaril.Wasm.Component.Async.futureDropW, htw, hcw]
    rfl
  show (builtin M (.futureDropW (BitVec.ofNat 32 (st.next + 2)).toNat) >>= fun _ =>
    pure [i32n cbExit]) _ = _
  rw [hw32, builtin_then M hdrop _ x]

/-- After the read, the callback loop with `closeFCb` takes the writable end's event, drops the
writable end and ends. -/
theorem future_close (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (v : Val) (x : M.St) :
    Drive M (closeFCb M) (waitCode (st.next + 3)) (x, fE st v) (.ok () (x, fF st v)) := by
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  have hw : Waits (fE st v) (st.next + 3) (st.next + 2)
      ⟨.futureWrite, st.next + 2, CopyResult.completed.toNat, []⟩ (fE' st v) := by
    refine ⟨?_, ?_, ?_, rfl⟩
    · simp [fE, Store.setChan, Store.post, fD_tbl_si]
    · simp [fE, Store.setChan, Store.post, fD_joined]
    · simp [fE, Store.post, upd]
  have hcb : closeFCb M [i32n EventCode.futureWrite.toNat, i32n (st.next + 2),
      i32n CopyResult.completed.toNat] (x, fE' st v) (.ok [i32n cbExit] (x, fF st v)) := by
    rw [closeFCb_eq M st hb]
    rfl
  have hw' : Waits (x, fE st v).2 ((BitVec.ofNat 32 (2 + 16 * (st.next + 3))).toNat / 16)
      (st.next + 2) ⟨.futureWrite, st.next + 2, CopyResult.completed.toNat, []⟩ (fE' st v) := by
    rw [hd]
    exact hw
  have hdr : Drive M (closeFCb M) [i32n cbExit] (x, fF st v) (.ok () (x, fF st v)) := by
    rw [Silmaril.Proofs.Wasm.Jco.Async.drive_exit M]
    rfl
  exact Drive.waitOk (c := BitVec.ofNat 32 (2 + 16 * (st.next + 3))) hm hw' hcb hdr

/-- **The callee's loop has exactly one outcome**: from `fE`, with `closeFCb`, it ends at `fF`. -/
theorem future_close_iff (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (v : Val) (x : M.St) (o : Out M.withStore.St Unit) :
    Drive M (closeFCb M) (waitCode (st.next + 3)) (x, fE st v) o ↔ o = .ok () (x, fF st v) := by
  refine ⟨fun h => ?_, fun h => h ▸ future_close M st hb v x⟩
  have ⟨hm, hd⟩ := code_toNat (st.next + 3) hb
  have hex : @Eq (RM M.withStore.St Unit) (Drive M (closeFCb M) [i32n cbExit]) (pure ()) :=
    Silmaril.Proofs.Wasm.Jco.Async.drive_exit M _
  cases h with
  | exit _ hc => exact absurd (hm ▸ hc) (by decide)
  | yieldOk hc => exact absurd (hm ▸ hc) (by decide)
  | yieldTrap hc => exact absurd (hm ▸ hc) (by decide)
  | waitOk _ hw hcb hdr =>
    obtain ⟨rfl, rfl, rfl⟩ := fE_waits st hU v (hd ▸ hw)
    rw [closeFCb_eq M st hb] at hcb
    cases hcb
    exact (RM.pure_apply _ _ _).1 (hex ▸ hdr)
  | waitTrap _ hw hcb =>
    obtain ⟨rfl, rfl, rfl⟩ := fE_waits st hU v (hd ▸ hw)
    rw [closeFCb_eq M st hb] at hcb
    cases hcb
  | bad hb' => exact absurd ⟨_, rfl, by rw [hm]⟩ hb'

/-- **A future is read once**: after the callback, a second read traps. -/
theorem future_done (st : Store) (v : Val) :
    step (fF st v) (.futureRead (st.next + 1)) = none := by
  have ht : (fF st v).tbl (st.next + 1) = some (.futureR (st.next + 1)) := by
    show upd (fD st v).tbl (st.next + 2) none (st.next + 1) = _
    simp only [upd, show st.next + 1 ≠ st.next + 2 by omega, ite_false]
    rw [fD_tbl st v _ (by omega), fA_tbl]
    simp
  have hc : ((fF st v).chans (st.next + 1)).done = true := by
    simp [fF, Store.remove, Store.setChan, upd]
  simp [step, Silmaril.Wasm.Component.Async.futureRead, ht, hc]

/-- The task's results stay: the readable end. -/
theorem fF_result (st : Store) (v : Val) :
    ((fF st v).tasks st.next).result = some [hVal st] := by
  simp [fF, fE', fE, fD, joinStore, fC, fB, Store.remove, Store.setChan, Store.post, upd]

end Silmaril.Proofs.Wasm.Jco.Async.Future
