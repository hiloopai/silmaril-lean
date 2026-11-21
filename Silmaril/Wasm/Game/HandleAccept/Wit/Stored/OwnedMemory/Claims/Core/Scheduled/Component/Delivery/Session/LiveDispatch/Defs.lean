module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.CanonicalEntry.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def admit {Result : Type} (inst : InstId) (selection : Session grow sig (Except Issue Result)) :
    Session grow sig (Except Issue Result) := do
  if (← currentInst?) != some inst || !((← getStore).inst? inst).any (·.mayLeave) then
    return .error .wrongContext
  selection

noncomputable def memoryBody (inst : InstId) (destination : RecordDestination) (tree : Tree sig) (ptr : Nat) :
    Session grow sig (List FlatValue) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ =>
    store Limits.spec Quirks.none (destination.context inst) payload.2.val.value (sig.payload payload.1) ptr >>=
      fun _ => pure (completion 0 (.ok 0)).2

noncomputable def flatBody (inst : InstId) (destination : RecordDestination) (schema : Stored.TypeOf) (tree : Tree sig) :
    Session grow sig (List FlatValue) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ =>
    lowerFlatAt Limits.spec Quirks.none (destination.context inst) destination.width payload.2.val.value
        (sig.payload payload.1) >>= fun words => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.ok words)).2

/-- Caller, ABI and root-selection failures return the existing boundary status words.
Recursive checked guards are compared as stopped prefixes, not simulated by a canonical error. -/
noncomputable def memoryWords (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    Session grow sig (List FlatValue) :=
  admit inst (selectMemoryDestination destination args) >>= fun
    | .error issue => pure (completion 0 (.error issue)).2
    | .ok (tree, ptr) => memoryBody inst destination tree ptr

noncomputable def flatWords (inst : InstId) (destination : RecordDestination) (schema : Stored.TypeOf)
    (args : List FlatValue) : Session grow sig (List FlatValue) :=
  admit inst (selectFlatDestination destination schema args) >>= fun
    | .error issue => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.error issue)).2
    | .ok tree => flatBody inst destination schema tree

def selectBinding (bindings : List (Binding sig)) (name : String) (kind : V1.FuncType) :
    Option (InstId × RecordDestination × Option Stored.TypeOf) :=
  match resolveBinding bindings name kind with
  | .ok ⟨_, inst, .givePayload destination⟩ => some (inst, destination, none)
  | .ok ⟨_, inst, .giveFlat destination schema⟩ => some (inst, destination, some schema)
  | _ => none

/-- Each occurrence resolves the link and reads the live caller, memory and accepted roots.
Non-give handlers retain the underlying dispatcher, including its open hooks. Reference
gives do not append checked entry/completion events. Reply words do not encode the ticket. -/
noncomputable def host (bindings : List (Binding sig)) (base : HostImpl (core3 grow) (HostState sig)) :
    HostImpl (core3 grow) (HostState sig) :=
  { base with embedder := fun name kind args =>
      match selectBinding bindings name kind with
      | none => base.embedder name kind args
      | some (inst, destination, none) => memoryWords inst destination args
      | some (inst, destination, some schema) => flatWords inst destination schema args }

def Unchanged (bindings : List (Binding sig)) : Call (core3 grow) → Prop
  | .hostCallout (.embedder name kind) _ => selectBinding bindings name kind = none
  | _ => True

/-- Only a give request about to be dispatched is excluded. A suspended give,
allocator frame, or a future give in ordinary guest code is not excluded. -/
structure UnchangedAt (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) : Prop where
  direct : ∀ {thread call next frames rest}, state.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest →
    Unchanged bindings call
  core : ∀ {thread core next frames rest callee args}, state.ctl = ⟨thread, .core core next, frames⟩ :: rest →
    (core3 grow).status state.store.core core = .callout callee args → Unchanged bindings (.hostCallout callee args)

def UnchangedThrough (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (start : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {leading cut label trailing}, labels = leading ++ label :: trailing →
    Steps profile ready (specDispatch ready base) start leading cut →
    Steps profile ready (specDispatch ready base) cut (label :: trailing) finish → UnchangedAt bindings cut

/-- A compared nested give either rejoins its local caller with the older
frames still paired, or reaches an actual read or older-frame pop. In the
second case only the executed prefix (including the boundary) has replayed. -/
inductive NestedReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (body incoming : Config (core3 grow) (HostState sig))
    (labels : List (Label (core3 grow) (HostState sig))) (checked : Config (core3 grow) (HostState sig)) : Prop where
  | rejoined {reached}
      (run : Steps profile ready dispatch incoming labels reached)
      (paired : HostFrame.Related.Paired older checked reached)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready dispatch body leading beforeLeft)
      (replay : Steps profile ready dispatch incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (baselineStep : Step profile ready dispatch beforeLeft label afterLeft)
      (replayedStep : Step profile ready dispatch beforeRight label afterRight)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
