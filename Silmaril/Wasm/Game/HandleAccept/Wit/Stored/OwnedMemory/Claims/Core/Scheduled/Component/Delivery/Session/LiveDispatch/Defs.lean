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

/-- The actual step about to install an overlaid give. Suspended calls and
unexecuted requests in a continuation do not count as installations. -/
inductive GiveInstall (bindings : List (Binding sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    Config (core3 grow) (HostState sig) → Label (core3 grow) (HostState sig) →
      Config (core3 grow) (HostState sig) → Prop where
  | direct {state thread call next frames rest}
      (focused : state.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest)
      (give : ¬ Unchanged bindings call) :
      GiveInstall bindings dispatch state .tau
        { state with ctl := ⟨thread, .prog (dispatch call), .prog next :: frames⟩ :: rest }
  | core {state thread core next frames rest callee args}
      (focused : state.ctl = ⟨thread, .core core next, frames⟩ :: rest)
      (calling : (core3 grow).status state.store.core core = .callout callee args)
      (give : ¬ Unchanged bindings (.hostCallout callee args)) :
      GiveInstall bindings dispatch state .tau
        { state with ctl := ⟨thread, .prog (dispatch (.hostCallout callee args)), .core core next :: frames⟩ :: rest }

/-- The exact Core request at a pending public give. No caller, selection,
preflight, or return verdict is inferred from resolving the binding. -/
structure CoreGiveRequest (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) where
  name : String
  kind : V1.FuncType
  args : List FlatValue
  inst : InstId
  destination : RecordDestination
  schema : Option Stored.TypeOf
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : state.ctl = ⟨thread, .core core next, frames⟩ :: rest
  calling : (core3 grow).status state.store.core core = .callout (.embedder name kind) args
  linked : resolveBinding bindings name kind = .ok ⟨name, inst,
    schema.elim (.givePayload destination) (.giveFlat destination)⟩

/-- The public selector's result before entering the recursive emitter. -/
abbrev SelectionValue (sig : Signature) : Option Stored.TypeOf → Type
  | none => Tree sig × Nat
  | some _ => Tree sig

def CoreGiveRequest.selectionProgram {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) : Session grow sig (Except Issue (SelectionValue sig request.schema)) :=
  match request.schema with
  | none => admit request.inst (selectMemoryDestination request.destination request.args)
  | some schema => admit request.inst (selectFlatDestination request.destination schema request.args)

/-- The one journal read actually demanded by the guarded selector. Wrong
callers, invalid argument words and invalid destinations do not consult it.
The flat schema check itself comes after this read. -/
def CoreGiveRequest.lookupDemand {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) : Option (BitVec IntType.i32.width) :=
  match Plain.callerInstance state.store request.thread with
  | .error _ => none
  | .ok caller =>
    if caller != some request.inst || !(state.store.inst? request.inst).any (·.mayLeave) then none
    else match request.schema, request.args with
    | none, [.int .i32 handle, pointer] =>
      if Stored.flatType pointer != ABI.pointerType request.destination.width then none
      else if let .error _ := request.destination.check state.store then none else some handle
    | some _, [.int .i32 handle] =>
      if let .error _ := request.destination.check state.store then none else some handle
    | _, _ => none

/-- A direct program call has a program return frame, not the parked Core
caller of the two public give routes. Its actual focus is kept separate. -/
def DirectGiveAt (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ name kind args thread next frames rest inst destination schema,
    state.ctl = ⟨thread, .prog (.op (.call (.hostCallout (.embedder name kind) args)) next), frames⟩ :: rest ∧
    resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩

/-- The result of the read-only admission and selection prefix. The tree is
an observation from the live journal, not evidence of a live transfer claim. -/
structure CoreGiveRequest.Selected {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) (route : GiveEffectRoute) where
  handle : BitVec IntType.i32.width
  tree : Tree sig
  args : request.args = route.args handle
  linked : resolveBinding bindings request.name request.kind =
    .ok ⟨request.name, request.inst, route.action request.destination⟩
  caller : Plain.callerInstance state.store request.thread = .ok (some request.inst)
  mayLeave : (state.store.inst? request.inst).any (·.mayLeave) = true
  destination : request.destination.check state.store = .ok ()
  selected : Stored.Endpoints.Core.childFromHistory state.host.writer.accepted handle = some tree
  admitted : route.admits request.destination tree

def CoreGiveRequest.Selected.site {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag))
    (arity : Nat) (children : Fin arity → Tree sig) (field : RecordLower.Field) : PayloadRoot.Site grow sig route :=
  ⟨state, request.destination, request.inst, request.name, request.kind, selection.handle, tag, payload, arity,
    children, field, request.thread, request.core, request.next, request.frames, request.rest⟩

/-- The actual selected payload's pure compiler check, before any memory
placement, claim preparation, or realloc action. -/
def CoreGiveRequest.Selected.preflight {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route) :
    Except RecordLower.Issue (RecordLower.Field × List RecordLower.Object) :=
  match selection.tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Record.preflightValue (request.destination.context (grow := grow) request.inst)
    (sig.payload payload.1) payload.2 route.output

/-- A compiler rejection writes the checked ticketed error and rejoins the
parked Core caller without starting the recursive body. -/
def CoreGiveRequest.Selected.compilerRefused {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route)
    (issue : RecordLower.Issue) : Config (core3 grow) (HostState sig) :=
  let reply := route.reply request.destination state.host.nextTicket (.error issue)
  { state with host := (state.host.enter request.name request.kind (route.args selection.handle)).record reply.1
               ctl := ⟨request.thread, .core ((core3 grow).resume state.store.core request.core (.values reply.2))
                 request.next, request.frames⟩ :: request.rest }

/-- Replay up to the first reached give installation, divergent host read, or
substituted return. At an installation the live run stops before installing any
body. At a read or return both actual steps execute. The rest is evidence about
the baseline only and is not claimed for the live run. -/
inductive PairedReplay (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {other}
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming labels other)
      (paired : HostFrame.Related.Paired older finish other)
  | request {leading label trailing beforeLeft beforeRight afterLeft}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready (specDispatch ready base) start leading beforeLeft)
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (install : GiveInstall bindings (specDispatch ready base) beforeLeft label afterLeft)
      (tail : Steps profile ready (specDispatch ready base) afterLeft trailing finish)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready (specDispatch ready base) start leading beforeLeft)
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (baselineStep : Step profile ready (specDispatch ready base) beforeLeft label afterLeft)
      (replayedStep : Step profile ready (specDispatch ready (host bindings base)) beforeRight label afterRight)
      (tail : Steps profile ready (specDispatch ready base) afterLeft trailing finish)

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
