module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.CanonicalEntry.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open PayloadRoot ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish : Config (core3 grow) (HostState sig)}

private theorem enterWithTail (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) {labels}
    (tail : Steps profile ready (specDispatch ready (site.referenceHost base))
      (HostFrame.replace (site.reference site.referenceReply) other) labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace site.start other)
      (.tau :: .tau :: .tau :: labels) finish := by
  have leaves := Plain.thread_may_leave linked.caller linked.mayLeave
  have select : site.EntryRequest (.hostCallout (.embedder site.name site.functionType) (route.args site.handle)) :=
    ⟨rfl, rfl, rfl⟩
  refine Plain.prepend_embedder_callout (start := HostFrame.replace site.start other) linked.parked linked.calling ?_
  have words : (site.referenceHost base).embedder site.name site.functionType (route.args site.handle) = site.referenceWords := by
    simp only [Site.referenceHost, ite_eq_left select]
  have body : calloutBody Limits.spec Quirks.none ready (site.referenceHost base) site.start.store site.thread
      (.embedder site.name site.functionType) (route.args site.handle) = site.referenceProgram >>= site.referenceReply := by
    simp only [calloutBody, leaves, ↓reduceIte, words, Site.referenceWords,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    rfl
  rw [show (HostFrame.replace site.start other).store = site.start.store from rfl, body]
  exact tail

theorem entered (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace site.start other)
      [.tau, .tau, .tau] (HostFrame.replace (site.reference site.referenceReply) other) :=
  enterWithTail site linked other (.refl _)

private theorem unchanged (site : Site grow sig route) {request : Call (core3 grow)}
    (closed : ¬ site.EntryRequest request) :
    specDispatch ready base request = specDispatch ready (site.referenceHost base) request := by
  cases request with
  | hostCallout callee args =>
    cases callee with
    | embedder name kind => simp only [specDispatch, dispatch, hostCalloutProg, calloutBody, Site.referenceHost, ite_eq_right closed]
    | lowered | builtin => rfl
  | threadBody body => cases body <;> rfl
  | onCancel cancel => cases cancel <;> rfl
  | _ => rfl

theorem replayStep (site : Site grow sig route) {label}
    (step : Step profile ready (specDispatch ready base) start label finish) (closed : site.NoEntryAt start) :
    Step profile ready (specDispatch ready (site.referenceHost base)) start label finish := by
  cases step with
  | call focused => rw [unchanged site (closed.direct focused)]; exact .call focused
  | coreCallout focused calling => rw [unchanged site (closed.core focused calling)]; exact .coreCallout focused calling
  | newThread focused allocated =>
    unfold StepDefs.threadAct
    rw [unchanged site (request := .threadBody _) (fun impossible => impossible)]
    exact .newThread focused allocated
  | popProg focused => exact .popProg focused
  | popCore focused => exact .popCore focused
  | threadExit focused => exact .threadExit focused
  | hostDone focused => exact .hostDone focused
  | callCore focused => exact .callCore focused
  | coreInternal focused status inner => exact .coreInternal focused status inner
  | coreReturned focused status => exact .coreReturned focused status
  | coreTrap focused status => exact .coreTrap focused status
  | get focused => exact .get focused
  | modify focused => exact .modify focused
  | trap focused => exact .trap focused
  | choose answer focused allowed => exact .choose answer focused allowed
  | currentThread focused => exact .currentThread focused
  | block focused => exact .block focused
  | blockSwitch focused saved => exact .blockSwitch focused saved
  | resumeThread focused saved => exact .resumeThread focused saved
  | hostGet focused => exact .hostGet focused
  | hostSet focused => exact .hostSet focused
  | emit focused => exact .emit focused
  | fault failed => exact .fault failed
  | hostInvoke enabled fresh => exact .hostInvoke enabled fresh
  | hostTick enabled => exact .hostTick enabled
  | hostCancel enabled pending unresolved => exact .hostCancel enabled pending unresolved
  | hostRun enabled => exact .hostRun enabled

theorem replayOrRequest (site : Site grow sig route) {labels}
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start labels finish ∨
      ∃ leading label trailing reached, labels = leading ++ label :: trailing ∧
        Steps profile ready (specDispatch ready base) start leading reached ∧
        Steps profile ready (specDispatch ready (site.referenceHost base)) start leading reached ∧
        Steps profile ready (specDispatch ready base) reached (label :: trailing) finish ∧ ¬ site.NoEntryAt reached := by
  classical
  induction run with
  | refl => exact .inl (.refl _)
  | @cons before middle after label labels head tail ih =>
    by_cases closed : site.NoEntryAt before
    · have step := replayStep site head closed
      rcases ih with whole | ⟨leading, next, trailing, reached, split, baseline, replayed, remaining, boundary⟩
      · exact .inl (.cons step whole)
      · exact .inr ⟨label :: leading, next, trailing, reached, congrArg (List.cons label) split, .cons head baseline,
          .cons step replayed, remaining, boundary⟩
    · exact .inr ⟨[], label, labels, before, rfl, .refl _, .refl _, .cons head tail, closed⟩

theorem replay (site : Site grow sig route) {labels}
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : site.NoEntryThrough profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start labels finish := by
  rcases replayOrRequest site run with whole | ⟨_, _, _, _, split, baseline, _, remaining, boundary⟩
  · exact whole
  · exact False.elim (boundary (closed split baseline remaining))

theorem replayCore (site : Site grow sig route) {count : Nat}
    (run : Steps profile ready (specDispatch ready base) start (List.replicate count .core) finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start (List.replicate count .core) finish := by
  induction count generalizing start with
  | zero => cases run; exact .refl _
  | succ count ih =>
    cases run with
    | cons first tail =>
      cases first with
      | coreInternal focused status inner => exact .cons (.coreInternal focused status inner) (ih tail)

theorem execute (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) {labels}
    (body : Steps profile ready (specDispatch ready base) (HostFrame.replace (site.reference site.referenceReply) other) labels finish)
    (closed : site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) other) labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace site.start other)
      (.tau :: .tau :: .tau :: labels) finish :=
  enterWithTail site linked other (replay site body closed)

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {middle : Config (core3 grow) (HostState sig)} {leading trailing}
    (first : Steps profile ready dispatch start leading middle) (tail : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem executeAfter (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) {leading labels}
    (prior : Steps profile ready (specDispatch ready base) start leading (HostFrame.replace site.start other))
    (priorClosed : site.NoEntryThrough profile ready base start leading (HostFrame.replace site.start other))
    (body : Steps profile ready (specDispatch ready base) (HostFrame.replace (site.reference site.referenceReply) other) labels finish)
    (bodyClosed : site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) other) labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start (leading ++ .tau :: .tau :: .tau :: labels) finish :=
  appendSteps (replay site prior priorClosed) (execute site linked other body bodyClosed)

theorem executeInterleaved (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    {incoming outgoing actions leading labels}
    (between : JournalInterleaving profile ready base start incoming actions leading site.start outgoing)
    (journal : JournalReplay profile ready (specDispatch ready base) (site.reference site.referenceReply) outgoing labels finish)
    (reads : ReachedReadsAgree (profile := profile) (ready := ready) (specDispatch ready base)
      (site.reference site.referenceReply) outgoing labels finish)
    (priorClosed : site.NoEntryThrough profile ready base (HostFrame.replace start incoming) leading
      (HostFrame.replace site.start outgoing))
    (bodyClosed : ∀ {after}, Steps profile ready (specDispatch ready base)
      (HostFrame.replace (site.reference site.referenceReply) outgoing) labels (HostFrame.replace finish after) →
      site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) outgoing) labels
        (HostFrame.replace finish after)) :
    ∃ after, Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace start incoming)
      (leading ++ .tau :: .tau :: .tau :: labels) (HostFrame.replace finish after) := by
  obtain ⟨after, body⟩ := journal.complete_of_reads_agree reads
  exact ⟨after, executeAfter site linked outgoing between.runs.2.steps priorClosed body (bodyClosed body)⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry
