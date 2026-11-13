module

public import Silmaril.Wasm.Jco.Async.CbRet.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.CbRet
public import Silmaril.Proofs.Wasm.Jco.Async.CbRetWait

/-!
# `task.return` called from a callback: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.CbRet` and `Silmaril.Proofs.Wasm.Jco.Async.CbRetWait`.

**The loop up to `task.return`.**

* **`earlyDrive_retCb`**: from a state where the task has no results, the loop with the callback
  of `retCb ex` (which calls `task.return` of the values and returns `ex`) has exactly one
  outcome: the values, the code `ex`, and the store after `task.return`.
* `earlyDrive_of_result`: once the task holds results, the loop stops at once.
* `earlyDrive_exit_noRet`: `EXIT` before `task.return` traps.

**The caller's view** (when the synchronous lift over `M.withStore` is `RM.liftFst m₀`):

* **`asyncCallC_retCb`**: `task.return` from the callback is, for the caller, the stackful async
  shim of the adaptor (`shimRun … .stackful`, the call `awrap` makes);
* **`asyncCallC_retCb_eq_asyncCallR`**: hence the early return of `Async/Early` for a body that
  calls `task.return` at once (`Split.ret post`), for every rest `post`;
* **`asyncCallC_retCb_fstIs`**: the caller sees `visible m₀`, `M`'s C convention;
* `asyncCallC_retCb_sameFst_yield`: it agrees up to the async store with `asyncCall` of the
  yielding epilogue of `NInst.Inlines` (`task.return` in the core function, then `YIELD`, then a
  callback answering `EXIT`).

**Every body, and `task.return` after a wait.**

* **`asyncCallC_eq_asyncCall`**: for every `CbSplit`, the caller's view is `asyncCall`
  (stackful) of the body as an epilogue (`CbSplit.asEpi`): when the loop stops at `task.return`,
  the task holds the values (`earlyDrive_result`). So `fstIs_of_epiOk` of `Async/Wait` applies.
* `earlyDrive_waitRet_out`: on `WAIT si` with a callback that calls `task.return`, every outcome
  takes an event of a member of `si` and stops with the values.
* **`asyncCallC_pipeCb_fstIs`**: the body `pipeCb ex` (the values through a stream, `WAIT` on the
  writable end, `task.return` from the callback on its event) shows the caller `visible m₀`, on
  stores whose handles from `st.next` on are `Unused`;
  `asyncCallC_pipeCb_sameFst`: it agrees up to the async store with `pipeWaitE` of `Async/Wait`,
  which calls `task.return` before the wait.

**The callee after the caller continued**: `retCb_finish`: with `ex = EXIT` the rest of the loop
ends at once.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store step Waits)
open Silmaril.Proofs.Wasm.Jco.Async.Wait
open Silmaril.Proofs.Wasm.Jco.Async.Early
open Silmaril.Proofs.Wasm.Jco.Async.CbRet

variable (M : CoreInst)

/-- **The loop with a callback that calls `task.return`** has exactly one outcome. -/
theorem earlyDrive_retCb (ex : List Flat) (t : Nat) (ws : List Val) (x : M.St) {st st' : Store}
    (hr : (st.tasks t).result = none) (hs : step st (.taskReturn t ws) = some (st', .unit)) :
    EarlyDrive M ((retCb M ex).cb t ws) t [i32n cbYield] (x, st) =
      (pure (ws, ex) : RM M.withStore.St (List Val × List Flat)) (x, st') :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.earlyDrive_retCb M ex t ws x hr hs

/-- Once the task holds results, the loop stops at once. -/
theorem earlyDrive_of_result (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (rs : List Flat) (s : M.withStore.St) {ys : List Val} (hr : (s.2.tasks t).result = some ys)
    (o : Out M.withStore.St (List Val × List Flat)) :
    EarlyDrive M cb t rs s o ↔ o = .ok (ys, rs) s :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.earlyDrive_of_result M cb t rs s hr o

/-- **`EXIT` before `task.return` traps.** -/
theorem earlyDrive_exit_noRet (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (s : M.withStore.St) (hr : (s.2.tasks t).result = none)
    (o : Out M.withStore.St (List Val × List Flat)) :
    EarlyDrive M cb t [i32n cbExit] s o ↔ o = .trap :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.earlyDrive_exit_noRet M cb t s hr o

/-- **`task.return` from the callback is, for the caller, the adaptor's stackful async shim.** -/
theorem asyncCallC_retCb (ex : List Flat) (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) :
    asyncCallC M R core (retCb M ex) sig vs =
      asyncCall M R (shimRun M core sig.result .stackful) (AComp.noCallback M) .stackful sig vs :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.asyncCallC_retCb M ex R core sig vs m₀ hc

/-- **`task.return` from the callback is the early return of a body that calls `task.return` at
once**, whatever that body does afterwards. -/
theorem asyncCallC_retCb_eq_asyncCallR (ex : List Flat)
    (R core : List Flat → RM M.withStore.St (List Flat))
    (post : Nat → List Val → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) :
    asyncCallC M R core (retCb M ex) sig vs = asyncCallR M R core (Split.ret post) sig vs := by
  rw [asyncCallC_retCb M ex R core sig vs m₀ hc,
    asyncCallR_eq M R core (AComp.noCallback M) (Split.ret post) sig vs, ret_cutE, shimRun_eq]

/-- **The caller sees `M`'s C convention.** -/
theorem asyncCallC_retCb_fstIs (ex : List Flat) (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St) :
    FstIs M (asyncCallC M R core (retCb M ex) sig vs) (visible M m₀ sig.result) s := by
  rw [asyncCallC_retCb_eq_asyncCallR M ex R core (fun _ _ => pure []) sig vs m₀ hc]
  exact asyncCallR_fstIs M R core _ sig vs m₀ hc s

/-- **It agrees with the yielding epilogue of `NInst.Inlines`** (`task.return` in the core
function, then `YIELD`, a callback answering `EXIT`) up to the async store. -/
theorem asyncCallC_retCb_sameFst_yield (ex : List Flat)
    (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀)
    (s : M.withStore.St) :
    SameFst M (asyncCallC M R core (retCb M ex) sig vs)
      (asyncCall M R (bodyWith M core sig.result (yieldE M)) (exitCb M) .callback sig vs) s :=
  sameFst_of_fstIs M (asyncCallC_retCb_fstIs M ex R core sig vs m₀ hc s)
    (fstIs_of_epiOk M R core _ _ .callback sig vs m₀ hc s
      (yieldE_epiOk M (exitCb M) (fun _ => rfl) s.2))

/-- **When the loop up to `task.return` stops, the task holds the values.** -/
theorem earlyDrive_result (cb : List Flat → RM M.withStore.St (List Flat)) (t : Nat)
    (rs : List Flat) (s s' : M.withStore.St) (q : List Val × List Flat)
    (h : EarlyDrive M cb t rs s (.ok q s')) : (s'.2.tasks t).result = some q.1 :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.earlyDrive_result M cb t rs s s' q h

/-- **The caller's view of every `CbSplit` is `asyncCall` of the body as a stackful epilogue.** -/
theorem asyncCallC_eq_asyncCall {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : CbSplit M L) (sig : Sig) (vs : List PVal) :
    asyncCallC M R core b sig vs =
      asyncCall M R (bodyWith M core sig.result b.asEpi) (AComp.noCallback M) .stackful sig vs :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.asyncCallC_eq_asyncCall M R core b sig vs

/-- `WAIT si` with a callback that calls `task.return`: every outcome takes a member's event. -/
theorem earlyDrive_waitRet_out (ex : List Flat) (t : Nat) (ys : List Val) (si : Nat)
    (hsi : 16 * si + 2 < 2 ^ 32) (x : M.St) (st : Store) (hr : (st.tasks t).result = none)
    {o : Out M.withStore.St (List Val × List Flat)}
    (h : EarlyDrive M ((retCb M ex).cb t ys) t (waitCode si) (x, st) o) :
    ∃ h e st' st'', Waits st si h e st' ∧ step st' (.taskReturn t ys) = some (st'', .unit) ∧
      o = .ok (ys, ex) (x, st'') :=
  Silmaril.Proofs.Wasm.Jco.Async.CbRet.earlyDrive_waitRet_out M ex t ys si hsi x st hr h

/-- **`task.return` from the callback after a wait: the caller sees `M`'s C convention.** -/
theorem asyncCallC_pipeCb_fstIs (ex : List Flat) (R core : List Flat → RM M.withStore.St (List Flat))
    (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hU : Unused s.2) (hb : 16 * (s.2.next + 3) + 2 < 2 ^ 32) :
    FstIs M (asyncCallC M R core (pipeCb M ex) sig vs) (visible M m₀ sig.result) s := by
  rw [asyncCallC_eq_asyncCall]
  exact fstIs_of_epiOk M R core _ _ .stackful sig vs m₀ hc s
    (Silmaril.Proofs.Wasm.Jco.Async.CbRet.pipeCb_epiOk M ex _ s.2 hU hb)

/-- **It agrees with `pipeWaitE`**, which calls `task.return` before the wait, up to the async
store. -/
theorem asyncCallC_pipeCb_sameFst (ex : List Flat)
    (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig) (vs : List PVal)
    (m₀ : RM M.St (Option PVal)) (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀)
    (s : M.withStore.St) (hU : Unused s.2) (hb : 16 * (s.2.next + 3) + 2 < 2 ^ 32) :
    SameFst M (asyncCallC M R core (pipeCb M ex) sig vs)
      (asyncCall M R (bodyWith M core sig.result (pipeWaitE M)) (exitCb M) .callback sig vs) s :=
  sameFst_of_fstIs M (asyncCallC_pipeCb_fstIs M ex R core sig vs m₀ hc s hU hb)
    (fstIs_of_epiOk M R core _ _ .callback sig vs m₀ hc s
      (pipeWaitE_epiOk M s.2 ⟨(hU (s.2.next + 1) (by omega)).2.1, hb⟩))

/-- **With `ex = EXIT`, the callee's rest of the loop ends at once.** -/
theorem retCb_finish (t : Nat) (ws : List Val) (s : M.withStore.St) :
    Finish M ((retCb M [i32n cbExit]).cb t ws) [i32n cbExit] s s :=
  Finish.exit (c := BitVec.ofNat 32 cbExit) s (by decide)

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCallC_retCb_eq_asyncCallR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCallC_retCb_eq_asyncCallR

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCallC_pipeCb_sameFst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCallC_pipeCb_sameFst
