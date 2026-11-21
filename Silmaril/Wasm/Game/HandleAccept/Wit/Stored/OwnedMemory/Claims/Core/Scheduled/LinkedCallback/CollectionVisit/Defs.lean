module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def afterAllocation (index : Nat) : RecordLower.Issue → RecordLower.Issue
  | .preflight issue => .field index (.afterAllocation issue)
  | issue => .nested index issue

/-- Only a valid reached range and a successful live dry run enter the
children. In particular, the region is from the callback's reached store,
not from a prediction made before invoking it. -/
structure Admitted (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (area : Layout) (entries : List Field) (pointer bytes : Nat)
    (initial checked canonical : State grow sig) (check canon : Cursor (E := core3 grow) (HostState sig)) : Prop where
  width : (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width
  sized : (core3 grow).memSize? checked.store.core destination.memory = some bytes
  aligned : pointer = alignTo pointer area.alignment
  bounds : pointer + entries.length * area.size ≤ bytes
  frame : ChildFrameOver older checked canonical check canon
  growth : Core3.Grows initial.store.core checked.store.core
  prepared : Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .ok ()

abbrev Next (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Nat → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
    Cursor (E := core3 grow) (HostState sig) → Prop

def reachesNext {Result : Type} (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (origin : CStore (core3 grow)) (checkNext : Except RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) : Next grow sig :=
  fun _ left right check canon => ReachesKeeping profile ready (specDispatch ready (host bindings))
    (fun store => Core3.Grows origin.core store.core) left right check canon checkNext canonNext

/-- Consume the marked allocator's range cut. The canonical side stops
at its real entry tail on a typed refusal. Neither that stop nor a range
trap demands a continuation proof for an unvisited element. -/
inductive Outcome (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (type : TypeOf) (area : Layout) (entries : List Field) (index pointer : Nat) (output : Lower.Output)
    (left right last : State grow sig) (check : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (seen : List (Label (core3 grow) (HostState sig))) (next : Next grow sig) : Prop where
  | admitted {reference : State grow sig} {canon : Cursor (E := core3 grow) (HostState sig)}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))} {bytes : Nat}
      (region : Admitted older destination area entries pointer bytes left last reference check canon)
      (checked : ReturnRangeTrace profile ready bindings left last checkLabels
        { last with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
        (some (.active 0 0)))
      (canonical : ReturnRangeTrace profile ready bindings right reference canonLabels
        { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) } (some (.active 0 0)))
      (classified : ReplayTrace profile ready bindings left checkLabels
        { last with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
        right canonLabels { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen)
      (visit : next bytes
        { last with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
        { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) } check canon) :
      Outcome profile ready bindings older destination inst type area entries index pointer output left right last check checkNext canonNext seen next
  | refused {reference : State grow sig} {canon : Cursor (E := core3 grow) (HostState sig)} {issue : RecordLower.Issue}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (live : Record.prepare last.store last.host.writer (Field.listObjects entries) = .error issue)
      (frame : ChildFrameOver older last reference check canon)
      (checked : ReturnRangeTrace profile ready bindings left last checkLabels
        { last with ctl := check.control (checkNext (.error (afterAllocation index issue))) } (some (.active 0 0)))
      (canonical : ReturnRangeTrace profile ready bindings right reference canonLabels
        { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) } (some (.active 0 0)))
      (classified : ReplayTrace profile ready bindings left checkLabels
        { last with ctl := check.control (checkNext (.error (afterAllocation index issue))) }
        right canonLabels { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) })
      (checkSeen : visible checkLabels = seen) (canonSeen : visible canonLabels = seen) :
      Outcome profile ready bindings older destination inst type area entries index pointer output left right last check checkNext canonNext seen next
  | rangeTrap {reference : State grow sig} {reason : TrapReason}
      {checkLabels canonLabels : List (Label (core3 grow) (HostState sig))}
      (same : last.store = reference.store)
      (checked : Steps profile ready (specDispatch ready (host bindings)) left checkLabels (StepDefs.trapCfg last))
      (canonical : Steps profile ready (specDispatch ready (host bindings)) right canonLabels (StepDefs.trapCfg reference))
      (classified : ReplayTrace profile ready bindings left checkLabels (StepDefs.trapCfg last)
        right canonLabels (StepDefs.trapCfg reference))
      (checkSeen : visible checkLabels = seen ++ [.trap reason]) (canonSeen : visible canonLabels = seen ++ [.trap reason]) :
      Outcome profile ready bindings older destination inst type area entries index pointer output left right last check checkNext canonNext seen next

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit
