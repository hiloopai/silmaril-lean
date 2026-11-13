module

public import Silmaril.Wasm.Jco.Async.Early.Defs
public import Silmaril.Wasm.Jco.Async.Wait.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Wait

/-!
# The caller continues at `task.return`: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Early.Thms` (general part).

* `taskReturn_then`: after a `task.return` that succeeded, reading the task's results gives its
  values.
* `asyncCallR_eq`: the caller's view of a split body is `asyncCall` (stackful) of the body cut at
  `task.return`.
* `fstIs_cut`: so it is `visible m₀` over `M`'s state when the cut epilogue is faithful.
* `ret_cutE`, `ret_waitPost_epi`, `pipeSplit_epi`, `pipeSplit_cutE`: the split forms of the
  epilogues of `Async/Wait`.
* `drive_finish`: a run of the callback loop alone is a run of `Finish`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Early

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event startSync step Waits upd)
open Silmaril.Proofs.Wasm.Jco.Async.Frame
open Silmaril.Proofs.Wasm.Jco.Async.Wait

/-- A `task.return` that succeeded stored its values. -/
theorem step_taskReturn_result {st st' : Store} {t : Nat} {vs : List Val} {r : Res}
    (h : step st (.taskReturn t vs) = some (st', r)) : (st'.tasks t).result = some vs := by
  simp only [step] at h
  split_ifs at h with h1 h2
  · cases h
    simp [Store.post, upd]
  · cases h
    simp [upd]

variable (M : CoreInst)

/-- After a `task.return` that succeeded, reading the task's results gives its values. -/
theorem taskReturn_then {β : Type} (t : Nat) (ys : List Val) (k : List Val → RM M.withStore.St β) :
    (builtin M (.taskReturn t ys) >>= fun _ => taskResult M t >>= k) =
      (builtin M (.taskReturn t ys) >>= fun _ => k ys) := by
  rw [builtin_bind, builtin_bind]
  funext s
  cases h : step s.2 (.taskReturn t ys) with
  | none => rfl
  | some p =>
    dsimp only
    rw [taskResult_bind]
    dsimp only
    rw [step_taskReturn_result (r := p.2) (st' := p.1) (by rw [h])]

/-- **The caller's view is the async call of the body cut at `task.return`.** -/
theorem asyncCallR_eq {L : Type} (R core cb : List Flat → RM M.withStore.St (List Flat))
    (b : Split M L) (sig : Sig) (vs : List PVal) :
    asyncCallR M R core b sig vs =
      asyncCall M R (bodyWith M core sig.result b.cutE) cb .stackful sig vs := by
  simp only [asyncCallR, asyncCallK, asyncCall, bodyWith, Split.cutE, RM.bind_assoc,
    RM.pure_bind, List.isEmpty_nil, RM.check_true, taskReturn_then]

/-- **The caller's view is `visible m₀`** when the cut epilogue is faithful. -/
theorem fstIs_cut {L : Type} (R core : List Flat → RM M.withStore.St (List Flat))
    (b : Split M L) (sig : Sig) (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hE : EpiOk M b.cutE (AComp.noCallback M) .stackful s.2) :
    FstIs M (asyncCallR M R core b sig vs) (visible M m₀ sig.result) s := by
  rw [asyncCallR_eq M R core (AComp.noCallback M) b sig vs]
  exact fstIs_of_epiOk M R core _ b.cutE .stackful sig vs m₀ hc s hE

/-- The cut of `Split.ret post` is the adaptor's stackful epilogue. -/
theorem ret_cutE (post : Nat → List Val → RM M.withStore.St (List Flat)) :
    (Split.ret post).cutE = retE M .stackful := by
  funext t ws
  simp only [Split.cutE, Split.ret, retE, RM.pure_bind, Style.exitResult]

/-- `task.return`, then `WAIT` on a new set, is `waitE`. -/
theorem ret_waitPost_epi : (Split.ret (waitPost M)).epi = waitE M := by
  funext t ws
  simp only [Split.epi, Split.ret, waitPost, waitE, RM.pure_bind]
  refine RM.bind_congr fun _ => RM.bind_congr fun r => ?_
  cases r <;> rfl

/-- The cut of a split body is the whole epilogue of the same split with an empty rest. -/
theorem cutE_eq_epi {L : Type} (b : Split M L) :
    b.cutE = ({ b with post := fun _ _ => pure [] } : Split M L).epi := rfl

/-- `pipeSplit` is `pipeWith` split at its `task.return`. -/
theorem pipeSplit_epi (k : Nat → RM M.withStore.St (List Flat)) :
    (pipeSplit M fun _ w => k w).epi = pipeWith M k := by
  funext t ws
  simp only [Split.epi, pipeSplit, pipePre, pipeWith, RM.bind_assoc]
  refine RM.bind_congr fun e => ?_
  cases e with
  | ends r w =>
    simp only [RM.bind_assoc]
    refine RM.bind_congr fun _ => RM.bind_congr fun rd => ?_
    cases rd <;> simp only [RM.pure_bind, RM.fail_bind]
  | _ => simp only [RM.fail_bind]

/-- The cut of a pipe is the stream epilogue `pipeE` ending at once. -/
theorem pipeSplit_cutE (post : Nat → Nat → RM M.withStore.St (List Flat)) :
    (pipeSplit M post).cutE = pipeE M Style.stackful.exitResult := by
  rw [cutE_eq_epi]
  exact pipeSplit_epi M fun _ => pure []

/-- `pipeWaitSplit` is `pipeWaitE` split at its `task.return`. -/
theorem pipeWaitSplit_epi : (pipeWaitSplit M).epi = pipeWaitE M :=
  pipeSplit_epi M (joinWait M)

/-- **A run of the callback loop alone is a run of `Finish`** (with no other party). -/
theorem drive_finish (cb : List Flat → RM M.withStore.St (List Flat)) (rs : List Flat)
    (s s' : M.withStore.St) (h : Drive M cb rs s (.ok () s')) : Finish M cb rs s s' := by
  generalize ho : (Out.ok () s' : Out M.withStore.St Unit) = o at h
  induction h with
  | exit s hc =>
    cases ho
    exact Finish.exit (cb := cb) _ hc
  | yieldOk hc h _ ih => exact .yield hc h (ih ho)
  | yieldTrap _ _ => cases ho
  | waitOk hc hw hcb _ ih => exact .wait hc hw hcb (ih ho)
  | waitTrap _ _ _ => cases ho
  | bad _ => cases ho

end Silmaril.Proofs.Wasm.Jco.Async.Early
