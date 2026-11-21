module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Silent.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery.FiniteSession ComponentCall.Delivery.FiniteSession.Dispatch
open Silmaril.Proofs.Wasm.Component.Reference (DetRun UniqueStep)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {callees : List (Callee sig)}
  {start finish : Config (core3 grow) (HostState sig)}

theorem closedDispatch {call : Call (core3 grow)} (closed : ¬ UsesComponent call) :
    coreOnly ready bindings call = linked ready bindings callees call := by
  cases call with
  | funcInst | hostFunc => exact False.elim (closed trivial)
  | hostCallout callout => cases callout <;> rfl
  | threadBody body => cases body <;> rfl
  | onCancel cancel => cases cancel <;> rfl
  | _ => rfl

theorem closedAgrees (closed : ClosedAt start) : AgreesAt ready bindings callees start :=
  fun focus => closedDispatch (closed focus)

theorem blockPrefix {thread : ThreadId} {next frames rest}
    (focused : start.ctl = ⟨some thread, .prog (.op (.block none) next), frames⟩ :: rest) :
    Compatible profile ready bindings callees start [.tau]
      { (start.setCont thread (some (StepDefs.blockedAct thread next frames))) with
        store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest } := by
  refine .next (closedAgrees ?_) (.block focused) (.done _)
  intro _ _ _ _ _ callAt
  rw [focused] at callAt
  cases callAt

theorem resumePrefix {thread : Option ThreadId} {target : ThreadId} {next frames rest blocked}
    (focused : start.ctl = ⟨thread, .prog (.op (.resumeThread target) next), frames⟩ :: rest)
    (saved : start.cont? target = some blocked) :
    Compatible profile ready bindings callees start [.tau]
      { (start.setCont target none) with
        store := StepDefs.threadStatusSt target .running start.store,
        ctl := blocked :: ⟨thread, .prog (next ()), frames⟩ :: rest } := by
  refine .next (closedAgrees ?_) (.resumeThread focused saved) (.done _)
  intro _ _ _ _ _ callAt
  rw [focused] at callAt
  cases callAt

theorem overlayStep {label} (agrees : AgreesAt ready bindings callees start)
    (step : Step profile ready (coreOnly ready bindings) start label finish) :
    Step profile ready (linked ready bindings callees) start label finish := by
  cases step with
  | call focus =>
    rw [agrees focus]
    exact .call focus
  | coreCallout focus status =>
    rw [closedDispatch (ready := ready) (bindings := bindings) (callees := callees) (call := .hostCallout _ _) (fun impossible => impossible)]
    exact .coreCallout focus status
  | newThread focus alloc =>
    unfold StepDefs.threadAct
    rw [closedDispatch (ready := ready) (bindings := bindings) (callees := callees) (call := .threadBody _) (fun impossible => impossible)]
    exact .newThread focus alloc
  | popProg focus => exact .popProg focus
  | popCore focus => exact .popCore focus
  | threadExit focus => exact .threadExit focus
  | hostDone focus => exact .hostDone focus
  | callCore focus => exact .callCore focus
  | coreInternal focus status advance => exact .coreInternal focus status advance
  | coreReturned focus status => exact .coreReturned focus status
  | coreTrap focus status => exact .coreTrap focus status
  | get focus => exact .get focus
  | modify focus => exact .modify focus
  | trap focus => exact .trap focus
  | choose answer focus allowed => exact .choose answer focus allowed
  | currentThread focus => exact .currentThread focus
  | block focus => exact .block focus
  | blockSwitch focus saved => exact .blockSwitch focus saved
  | resumeThread focus saved => exact .resumeThread focus saved
  | hostGet focus => exact .hostGet focus
  | hostSet focus => exact .hostSet focus
  | emit focus => exact .emit focus
  | fault reason => exact .fault reason
  | hostInvoke hostReady fresh => exact .hostInvoke hostReady fresh
  | hostTick hostReady => exact .hostTick hostReady
  | hostCancel hostReady cancel unresolved => exact .hostCancel hostReady cancel unresolved
  | hostRun hostReady => exact .hostRun hostReady

private theorem liftedLookupRun {impl : HostImpl (core3 grow) (HostState sig)}
    {thread func caller next frames rest core fnType opts inst}
    (focus : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    DetRun profile ready (specDispatch ready impl) start [.tau, .tau]
      { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
        .prog next :: frames⟩ :: rest } := by
  refine .cons (.of_prog focus (fun _ _ different => by cases different) (.call focus)) ?_
  let read : CStore (core3 grow) → P (core3 grow) (HostState sig) (Ret (core3 grow)) := fun store =>
    (match store.func? func with
      | some entry => pure entry
      | none => internal "dangling arena id") >>= fun
    | .lifted liftedCore liftedType liftedOpts liftedInst =>
      canonLift Limits.spec Quirks.none liftedCore liftedType liftedOpts liftedInst caller
    | .host _ hostFn => impl.funcs hostFn caller
  have readReached : read start.store = canonLift Limits.spec Quirks.none core fnType opts inst caller := by
    simp [read, lookup]
  have installed : specDispatch ready impl (.funcInst func caller) = .op .get read := by
    simp only [dispatch, funcInstProg, getObj, getStore, perform, Prog.lift, bind, Prog.bind, pure, read, CStore.func?]
    apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .get)
    funext store
    cases ArenaField.funcs.get? store func with
    | none =>
      simp only [internal, trap, Prog.bind]
      apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap (.internal "dangling arena id")))
      funext response
      cases response
    | some entry => cases entry <;> rfl
  let middle := { start with ctl := ⟨thread, .prog (specDispatch ready impl (.funcInst func caller)),
    .prog next :: frames⟩ :: rest }
  have focused : middle.ctl = ⟨thread, .prog (.op .get read), .prog next :: frames⟩ :: rest := by
    simp only [middle, installed]
  have unique := UniqueStep.of_prog (prof := profile) (hr := ready) (dispatch := specDispatch ready impl)
    focused (fun _ _ different => by cases different) (.get focused)
  rw [readReached] at unique
  exact .single unique

theorem liftedLookupSteps {impl : HostImpl (core3 grow) (HostState sig)}
    {thread func caller next frames rest core fnType opts inst}
    (focus : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    Steps profile ready (specDispatch ready impl) start [.tau, .tau]
      { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
        .prog next :: frames⟩ :: rest } :=
  (liftedLookupRun focus lookup).steps

theorem peelLiftedLookup {labels thread func caller next frames rest core fnType opts inst}
    (focus : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst))
    (run : Steps profile ready (coreOnly ready bindings) start labels finish) (two : 2 ≤ labels.length) :
    ∃ trailing, labels = .tau :: .tau :: trailing ∧
      Steps profile ready (coreOnly ready bindings)
        { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
          .prog next :: frames⟩ :: rest } trailing finish := by
  rcases (liftedLookupRun (profile := profile) (ready := ready) (impl := host bindings) focus lookup).inv run with short | extended
  · obtain ⟨tail, split, restRun⟩ := short
    have lengths := congrArg List.length split
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.length_append] at lengths
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    cases restRun
    exact ⟨[], by simpa using split.symm, .refl _⟩
  · exact extended

private theorem appendSteps {middle : Config (core3 grow) (HostState sig)} {leading trailing}
    {dispatch : Call (core3 grow) → P (core3 grow) (HostState sig) (Ret (core3 grow))}
    (before : Steps profile ready dispatch start leading middle)
    (after : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction before with
  | refl => exact after
  | cons step _ ih => exact .cons step (ih after)

theorem compatibleSteps {labels} (run : Compatible profile ready bindings callees start labels finish) :
    Steps profile ready (linked ready bindings callees) start labels finish := by
  induction run with
  | done => exact .refl _
  | next agrees step _ ih => exact .cons (overlayStep agrees step) ih
  | liftedLookup focus lookup _ ih => exact appendSteps (liftedLookupSteps focus lookup) ih

theorem compatibleAppend {middle : Config (core3 grow) (HostState sig)} {leading trailing}
    (before : Compatible profile ready bindings callees start leading middle)
    (after : Compatible profile ready bindings callees middle trailing finish) :
    Compatible profile ready bindings callees start (leading ++ trailing) finish := by
  induction before with
  | done => exact after
  | next agrees step _ ih => exact .next agrees step (ih after)
  | liftedLookup focus lookup _ ih => exact .liftedLookup focus lookup (ih after)

theorem closedPrefix {labels} (run : Steps profile ready (coreOnly ready bindings) start labels finish)
    (closed : ClosedThrough profile ready bindings start labels finish) : Compatible profile ready bindings callees start labels finish := by
  induction run with
  | refl => exact .done _
  | cons step tail ih =>
    refine .next (closedAgrees (closed (leading := []) rfl (.refl _) (.cons step tail))) step (ih ?_)
    intro leading cut label trailing eq before after
    exact closed (leading := _ :: leading) (congrArg (_ :: ·) eq) (.cons step before) after

theorem compatibleOrLookup {labels} (run : Steps profile ready (coreOnly ready bindings) start labels finish) :
    Compatible profile ready bindings callees start labels finish ∨ LookupCut profile ready bindings callees start labels finish := by
  classical
  generalize countEq : labels.length = count
  induction count using Nat.strong_induction_on generalizing start labels with
  | _ count smaller =>
    cases run with
    | refl => exact .inl (.done _)
    | @cons _ middle _ label trailing step tail =>
      by_cases agrees : AgreesAt ready bindings callees start
      · have less : trailing.length < count := by simp [← countEq]
        rcases smaller trailing.length less tail rfl with whole | openCall
        · exact .inl (.next agrees step whole)
        · cases openCall with
          | reached common focus component different pending suffix =>
            exact .inr (.reached (.next agrees step common) focus component different pending suffix)
      · have request : ∃ thread call next frames rest,
            start.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest ∧
            coreOnly ready bindings call ≠ linked ready bindings callees call := by
          by_contra absent
          exact agrees (fun focused => Classical.byContradiction fun different => absent ⟨_, _, _, _, _, focused, different⟩)
        obtain ⟨_, call, _, _, _, focus, different⟩ := request
        have component : UsesComponent call := Classical.byContradiction fun closed => different (closedDispatch closed)
        by_cases pending : trailing = [] ∨ ¬ SelectsLifted start call
        · exact .inr (.reached (.done _) focus component different pending (.cons step tail))
        · have selected : SelectsLifted start call := Classical.byContradiction fun missing => pending (.inr missing)
          have two : 2 ≤ (label :: trailing).length := by
            cases trailing with
            | nil => exact (pending (.inl rfl)).elim
            | cons => simp
          cases call <;> simp only [SelectsLifted] at selected
          case funcInst =>
            obtain ⟨_, _, _, _, lookup⟩ := selected
            obtain ⟨remaining, split, rest⟩ := peelLiftedLookup focus lookup (.cons step tail) two
            have less : remaining.length < count := by
              simp only [← countEq, split, List.length_cons]
              omega
            rw [split]
            rcases smaller remaining.length less rest rfl with whole | openCall
            · exact .inl (.liftedLookup focus lookup whole)
            · cases openCall with
              | reached common reachedAt uses different pending suffix =>
                exact .inr (.reached (.liftedLookup focus lookup common) reachedAt uses different pending suffix)

theorem closedOccurrence {labels origin mark}
    (path : ReturnFrame.Occurrence.Prefix profile ready (coreOnly ready bindings) start origin labels finish mark)
    (closed : ClosedThrough profile ready bindings start labels finish) :
    ReturnFrame.Occurrence.Prefix profile ready (linked ready bindings callees) start origin labels finish mark := by
  induction path with
  | done => exact .done _ _
  | step step follows tail ih =>
    have suffix := (ReturnFrame.Occurrence.prefix_survives tail).1
    refine .step (overlayStep (closedAgrees (closed (leading := []) rfl (.refl _) (.cons step suffix))) step)
      follows (ih ?_)
    intro leading cut label trailing eq before after
    exact closed (leading := _ :: leading) (congrArg (_ :: ·) eq) (.cons step before) after

theorem corePrefix {count : Nat}
    (run : Steps profile ready (coreOnly ready bindings) start (List.replicate count .core) finish) :
    Compatible profile ready bindings callees start (List.replicate count .core) finish := by
  induction count generalizing start with
  | zero => cases run; exact .done _
  | succ count ih =>
    cases run with
    | cons step tail =>
      cases step with
      | coreInternal focused status advance =>
        refine .next (closedAgrees ?_) (.coreInternal focused status advance) (ih tail)
        intro thread call next frames rest focus
        rw [focused] at focus
        cases focus

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch
