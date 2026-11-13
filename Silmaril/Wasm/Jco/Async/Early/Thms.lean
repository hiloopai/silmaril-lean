module

public import Silmaril.Wasm.Jco.Async.Early.Defs
public import Silmaril.Wasm.Jco.Async.Wait.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Early
public import Silmaril.Proofs.Wasm.Jco.Async.EarlyStream

/-!
# The caller continues at `task.return`: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Early` and `Silmaril.Proofs.Wasm.Jco.Async.EarlyStream`.

**The caller's view.**

* `asyncCallR_eq`: the caller's view of a split body is `asyncCall` (stackful) of the body cut at
  `task.return`. So the results of `Async/Wait` apply to the first half.
* **`asyncCallR_fstIs`**: for a body that calls `task.return` at once (`Split.ret post`), the
  caller's view is `visible m₀` over `M`'s state, **whatever the rest `post` of the body does**
  (it may wait for ever).
* `asyncCallR_sameFst`: when the whole epilogue is faithful under `asyncCall` (`EpiOk`), the two
  calls agree up to the async store. So for the bodies already proved (`retE`, `yieldE`,
  `pipeE`, `pipeWaitE`) the early return changes nothing the caller sees of `M`.
* **`asyncCallR_waitE_ok`**: the body `waitE` (`task.return`, then `WAIT` on an empty set), which
  never returns under `asyncCall` (`asyncCall_waitE_noOk`), returns every value of `M` here.
* `asyncCallR_pipe_fstIs`, `asyncCallR_pipeWait_sameFst`: the stream epilogue split at its
  `task.return` (`pipeWaitSplit`, `pipeWaitSplit_epi`).

**The callee after the caller continued.** `drive_finish`: the callback loop alone is a run of
`Finish`, which also allows built-ins of other parties.

**A function whose result is a stream** (`streamSplit`, `asyncCallS`), from a store whose handles
from `st.next` on are `Unused`:

* **`asyncCallS_ok`**: the caller gets the readable end `st.next + 1` and `M`'s state of its C
  convention, as soon as `task.return` ran (store `sB`).
* `stream_post`: the rest of the body writes the values (pending) and waits on a set joined by
  the writable end (store `sD`).
* **`stream_hangs`**: alone, the callee's loop has no outcome, for any callback: it waits for a
  reader.
* **`stream_read`**: the caller's `stream.read r m` delivers the first `min m |ws|` values.
* **`stream_close`**: then the loop with `closeCb`, a callback that does work, takes the writable
  end's event, drops the writable end and ends; **`stream_eos`**: the caller's next read reports
  the end of the stream (`DROPPED`). `stream_rest`: the whole rest of the body as a `Rest` run
  with the caller's read interleaved.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Waits step packCopy)
open Silmaril.Proofs.Wasm.Jco.Async.Early
open Silmaril.Proofs.Wasm.Jco.Async.Wait

variable (M : CoreInst)

/-- **The caller's view is the async call of the body cut at `task.return`.** -/
theorem asyncCallR_eq {L : Type} (R core cb : List Flat → RM M.withStore.St (List Flat))
    (b : Split M L) (sig : Sig) (vs : List PVal) :
    asyncCallR M R core b sig vs =
      asyncCall M R (bodyWith M core sig.result b.cutE) cb .stackful sig vs :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.asyncCallR_eq M R core cb b sig vs

/-- **A body that calls `task.return` at once: the caller sees `M`'s C convention**, whatever
the rest of the body does. -/
theorem asyncCallR_fstIs (R core : List Flat → RM M.withStore.St (List Flat))
    (post : Nat → List Val → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀)
    (s : M.withStore.St) :
    FstIs M (asyncCallR M R core (Split.ret post) sig vs) (visible M m₀ sig.result) s := by
  refine fstIs_cut M R core _ sig vs m₀ hc s ?_
  rw [ret_cutE]
  exact retE_epiOk M _ .stackful s.2

/-- **With a faithful whole epilogue, the early return agrees with `asyncCall`** up to the async
store. -/
theorem asyncCallR_sameFst {L : Type} (R core cb : List Flat → RM M.withStore.St (List Flat))
    (b : Split M L) (sty : Style) (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hcut : EpiOk M b.cutE (AComp.noCallback M) .stackful s.2) (hE : EpiOk M b.epi cb sty s.2) :
    SameFst M (asyncCallR M R core b sig vs)
      (asyncCall M R (bodyWith M core sig.result b.epi) cb sty sig vs) s :=
  sameFst_of_fstIs M (fstIs_cut M R core b sig vs m₀ hc s hcut)
    (asyncCall_fstIs M R core cb b.epi sty sig vs m₀ hc s hE)

/-- `task.return`, then `WAIT` on a new set: the split form of `waitE`. -/
theorem ret_waitPost_epi : (Split.ret (waitPost M)).epi = waitE M :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.ret_waitPost_epi M

/-- **A body that returns and then waits on an empty set returns to its caller** when the caller
continues at `task.return` (compare `asyncCall_waitE_noOk`). -/
theorem asyncCallR_waitE_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    {v : Option PVal} {x : M.St} {ws : List Val} {r : Option PVal} (hm : m₀ s.1 (.ok v x))
    (hv : resVals v = some ws) (hr : valsRes sig.result ws = some r) :
    ∃ z, asyncCallR M R core (Split.ret (waitPost M)) sig vs s (.ok r (x, z)) := by
  refine ((asyncCallR_fstIs M R core (waitPost M) sig vs m₀ hc s).1 r x).2 ?_
  refine (RM.bind_apply _ _ _ _).2 (.inl ⟨v, x, hm, ?_⟩)
  rw [hv, RM.ofOption_some, RM.pure_bind, hr]
  rfl

/-- `pipeWaitSplit` is `pipeWaitE` split at its `task.return`. -/
theorem pipeWaitSplit_epi : (pipeWaitSplit M).epi = pipeWaitE M :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.pipeWaitSplit_epi M

/-- **The values through a stream, then the early return**: `visible m₀` on a fresh channel. -/
theorem asyncCallR_pipe_fstIs (R core : List Flat → RM M.withStore.St (List Flat))
    (post : Nat → Nat → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀)
    (s : M.withStore.St) (hf : s.2.chans (s.2.next + 1) = {}) :
    FstIs M (asyncCallR M R core (pipeSplit M post) sig vs) (visible M m₀ sig.result) s := by
  refine fstIs_cut M R core _ sig vs m₀ hc s ?_
  rw [pipeSplit_cutE]
  exact pipeE_epiOk M _ .stackful s.2 hf

/-- **The stream epilogue that waits, with the early return, agrees with `asyncCall`** of
`pipeWaitE` up to the async store, on `Fresh` stores. -/
theorem asyncCallR_pipeWait_sameFst (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hF : Fresh s.2) :
    SameFst M (asyncCallR M R core (pipeWaitSplit M) sig vs)
      (asyncCall M R (bodyWith M core sig.result (pipeWaitE M)) (exitCb M) .callback sig vs) s := by
  have h := asyncCallR_sameFst M R core (exitCb M) (pipeWaitSplit M) .callback sig vs m₀ hc s
    (by rw [show (pipeWaitSplit M).cutE = _ from pipeSplit_cutE M _]
        exact pipeE_epiOk M _ .stackful s.2 hF.1)
    (by rw [pipeWaitSplit_epi]; exact pipeWaitE_epiOk M s.2 hF)
  rwa [pipeWaitSplit_epi] at h

/-- **The callback loop alone is a run of `Finish`.** -/
theorem drive_finish (cb : List Flat → RM M.withStore.St (List Flat)) (rs : List Flat)
    (s s' : M.withStore.St) (h : Drive M cb rs s (.ok () s')) : Finish M cb rs s s' :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.drive_finish M cb rs s s' h

/-! ## A function whose result is a stream -/

/-- The empty store has every handle from `next` on unused. -/
theorem unused_empty : Unused Store.empty := fun _ _ =>
  ⟨rfl, rfl, rfl, rfl, fun _ h => by cases h⟩

/-- **The caller of a function whose result is a stream gets the readable end** `s.2.next + 1`
as soon as `task.return` ran, with `M`'s state of its C convention. -/
theorem asyncCallS_ok (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (hb : s.2.next + 1 < 2 ^ 32) (h : Nat) (s' : M.withStore.St) :
    asyncCallS M R core sig vs s (.ok h s') ↔
      ∃ v x ws, m₀ s.1 (.ok v x) ∧ resVals v = some ws ∧ h = s.2.next + 1 ∧ s' = (x, sB s.2) :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.asyncCallS_ok M R core sig vs m₀ hc s hU hb h s'

/-- The rest of the body writes the values (pending) and waits on the set of the writable end. -/
theorem stream_post (st : Store) (hU : Unused st) (ws : List Val) (x : M.St) :
    (streamSplit M).post st.next (st.next + 2, ws) (x, sB st) =
      (pure (waitCode (st.next + 3)) : RM M.withStore.St (List Flat)) (x, sD st ws) :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.stream_post M st hU ws x

/-- **Alone, the callee waits for ever**: no outcome of the loop, for any callback. -/
theorem stream_hangs (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (x : M.St) (cb : List Flat → RM M.withStore.St (List Flat))
    (o : Out M.withStore.St Unit) : ¬ Drive M cb (waitCode (st.next + 3)) (x, sD st ws) o :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.stream_hangs M st hU hb ws x cb o

/-- **The caller's read delivers the values.** -/
theorem stream_read (st : Store) (ws : List Val) (m : Nat) :
    step (sD st ws) (.streamRead (st.next + 1) m) =
      some (sE st ws m, .read (packCopy .completed (min m ws.length)) (ws.take (min m ws.length))) :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.stream_read st ws m

/-- **Then the callback closes the stream and the loop ends.** -/
theorem stream_close (st : Store) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val)
    (m : Nat) (x : M.St) :
    Drive M (closeCb M) (waitCode (st.next + 3)) (x, sE st ws m) (.ok () (x, sF st ws m)) :=
  Silmaril.Proofs.Wasm.Jco.Async.Early.stream_close M st hb ws m x

/-- **The caller's next read reports the end of the stream**; the task's results stay. -/
theorem stream_eos (st : Store) (ws : List Val) (m m' : Nat) :
    step (sF st ws m) (.streamRead (st.next + 1) m') =
        some (sF st ws m, .read (packCopy .dropped 0) []) ∧
      ((sF st ws m).tasks st.next).result = some [hVal st] :=
  ⟨Silmaril.Proofs.Wasm.Jco.Async.Early.stream_eos st ws m m', sF_result st ws m⟩

/-- **The rest of the stream function's body, with the caller's read interleaved**: from `sB` it
runs to `sF`. -/
theorem stream_rest (st : Store) (hU : Unused st) (hb : 16 * (st.next + 3) + 2 < 2 ^ 32)
    (ws : List Val) (m : Nat) (x : M.St) :
    Rest M (streamSplit M) (closeCb M) st.next (st.next + 2, ws) (x, sB st) (x, sF st ws m) := by
  refine ⟨waitCode (st.next + 3), (x, sD st ws), ?_, ?_⟩
  · rw [stream_post M st hU ws x]
    rfl
  · exact .env (.streamRead (st.next + 1) m) (stream_read st ws m)
      (drive_finish M _ _ _ _ (stream_close M st hb ws m x))

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCallR_waitE_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCallR_waitE_ok

/--
info: 'Silmaril.Wasm.Jco.Async.stream_rest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.stream_rest
