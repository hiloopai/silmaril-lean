module

public import Silmaril.Wasm.Jco.Async.Future.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Future
public import Silmaril.Proofs.Wasm.Jco.Async.FutureStream

/-!
# A function whose result is a future: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Future` and `Silmaril.Proofs.Wasm.Jco.Async.FutureStream`.
From a store whose handles from `st.next` on are `Unused`, the task is `st.next`, the future's
readable end `st.next + 1`, its writable end `st.next + 2` and the waitable set `st.next + 3`.

**The caller.** **`asyncCallF_ok`**: the caller of a function whose result is `future<T>` gets
the readable end `st.next + 1` and `M`'s state of its C convention as soon as `task.return` ran
(store `fB`). Its traps are characterised in the proofs (`asyncCallK_future`).

**The callee and the caller's read.**

* `future_post`: the rest of the body writes `M`'s value (pending) and waits on a set joined by
  the writable end (store `fD`).
* **`future_hangs`**: alone, the callee's loop has no outcome, for any callback.
* **`future_read`**: the caller's `future.read r` delivers the value.
* **`future_close`**, **`future_close_iff`**: then the loop with the future's callback `closeFCb`
  (which drops the writable end) ends at `fF`, and **has no other outcome**.
* **`future_done`**: a second read traps (a future is read once); the task's results stay.
* `future_rest`: the whole rest of the body as a `Rest` run, the caller's read interleaved.

**Uniqueness for the stream** (the item left open by `Async/Early`): **`stream_close_iff`**: from
`sE` the stream callee's loop with `closeCb` has exactly one outcome, `sF`. With the equations
`stream_post`, `stream_read` and `asyncCallS_ok` (an `↔`), every step of the stream function
without other parties is determined. `Finish`, which interleaves other parties, is not
deterministic by design.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Waits step CopyResult)
open Silmaril.Proofs.Wasm.Jco.Async.Early
open Silmaril.Proofs.Wasm.Jco.Async.Future

variable (M : CoreInst)

/-- **The caller of a function whose result is a future gets the readable end** `s.2.next + 1`
as soon as `task.return` ran, with `M`'s state of its C convention. -/
theorem asyncCallF_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (hb : s.2.next + 1 < 2 ^ 32) (h : Nat) (s' : M.withStore.St) :
    asyncCallF M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next + 1 ∧ s' = (x, fB s.2) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.asyncCallF_ok M R core sig vs m₀ hc s hU hb h s'

/-- The rest of the body writes the value (pending) and waits on the set of the writable end. -/
theorem future_post (st : Store) (hU : Unused st) (v : Val) (x : M.St) :
    (futureSplit M).post st.next (st.next + 2, [v]) (x, fB st) =
      (pure (waitCode (st.next + 3)) : RM M.withStore.St (List Flat)) (x, fD st v) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.future_post M st hU v x

/-- **Alone, the callee waits for ever**: no outcome of the loop, for any callback. -/
theorem future_hangs (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (v : Val) (x : M.St) (cb : List Flat → RM M.withStore.St (List Flat))
    (o : Out M.withStore.St Unit) : ¬ Drive M cb (waitCode (st.next + 3)) (x, fD st v) o :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.future_hangs M st hU hb v x cb o

/-- **The caller's read delivers the value.** -/
theorem future_read (st : Store) (v : Val) :
    step (fD st v) (.futureRead (st.next + 1)) =
      some (fE st v, .read CopyResult.completed.toNat [v]) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.future_read st v

/-- **Then the future's callback drops the writable end and the loop ends.** -/
theorem future_close (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (v : Val) (x : M.St) :
    Drive M (closeFCb M) (waitCode (st.next + 3)) (x, fE st v) (.ok () (x, fF st v)) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.future_close M st hb v x

/-- **The callee's loop has no other outcome.** -/
theorem future_close_iff (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (v : Val) (x : M.St) (o : Out M.withStore.St Unit) :
    Drive M (closeFCb M) (waitCode (st.next + 3)) (x, fE st v) o ↔ o = .ok () (x, fF st v) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.future_close_iff M st hU hb v x o

/-- **A future is read once**: a second read traps; the task's results stay. -/
theorem future_done (st : Store) (v : Val) :
    step (fF st v) (.futureRead (st.next + 1)) = none ∧
      ((fF st v).tasks st.next).result = some [hVal st] :=
  ⟨Silmaril.Proofs.Wasm.Jco.Async.Future.future_done st v, fF_result st v⟩

/-- **The rest of the future function's body, with the caller's read interleaved**: from `fB`
it runs to `fF`. -/
theorem future_rest (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (v : Val) (x : M.St) :
    Rest M (futureSplit M) (closeFCb M) st.next (st.next + 2, [v]) (x, fB st) (x, fF st v) := by
  refine ⟨waitCode (st.next + 3), (x, fD st v), ?_, ?_⟩
  · rw [future_post M st hU v x]
    rfl
  · exact .env (.futureRead (st.next + 1)) (future_read st v)
      (drive_finish M _ _ _ _ (future_close M st hb v x))

/-- **The stream callee's loop has exactly one outcome**: from `sE`, with `closeCb`, it ends at
`sF` (compare `stream_close`, existence only). -/
theorem stream_close_iff (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (m : Nat) (x : M.St) (o : Out M.withStore.St Unit) :
    Drive M (closeCb M) (waitCode (st.next + 3)) (x, sE st ws m) o ↔
      o = .ok () (x, sF st ws m) :=
  Silmaril.Proofs.Wasm.Jco.Async.Future.stream_close_iff M st hU hb ws m x o

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.future_rest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.future_rest

/--
info: 'Silmaril.Wasm.Jco.Async.stream_close_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.stream_close_iff
