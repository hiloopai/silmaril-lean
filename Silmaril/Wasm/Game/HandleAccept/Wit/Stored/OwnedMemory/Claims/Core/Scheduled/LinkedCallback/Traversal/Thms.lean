module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Traversal.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LinkedCallback PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

theorem TrackedAdvance.refl (left right : State grow sig) : TrackedAdvance profile ready bindings left right left right :=
  ⟨[], [], rfl, fun _ => .done _ _, fun _ => .done _ _⟩

/-- Concatenate reached paths without counting silent carrier steps as observations. -/
theorem TrackedAdvance.append {left right middle other reached reference : State grow sig}
    (leading : TrackedAdvance profile ready bindings left right middle other)
    (trailing : TrackedAdvance profile ready bindings middle other reached reference) :
    TrackedAdvance profile ready bindings left right reached reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal.advanceAppend leading trailing

theorem LocalFieldThen.track_finish {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {output : Lower.Output} {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : LocalFieldThen profile ready bindings output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    LocalFieldThen profile ready bindings output left right check canon checkNext canonNext target :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal.localFieldTrackFinish leading run next

theorem HandleFieldThen.track_finish {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {item : Field} {index : Nat} {output : Lower.Output}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext target :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal.handleTrackFinish leading run next

/-- Carry the original slots through every reached string realloc, then through the descriptor. -/
theorem StringFieldThen.track_finish {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {str : Value.StrVal} {output : Lower.Output}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : StringFieldThen profile ready bindings older destination inst str output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    StringFieldThen profile ready bindings older destination inst str output left right check canon checkNext canonNext target :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal.stringFieldTrackFinish leading run next

/-- Enter the real child traversal only after the marked return, reached range check and live recheck. -/
theorem CollectionReplayFor.track_entries {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {type element : TypeOf} {entries : List Field}
    {index : Nat} {output : Lower.Output} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {checkNext canonNext}
    {next target : Nat → CollectionVisit.Next grow sig}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon
      checkNext canonNext (fun lhs rhs last cursor pointer seen => CollectionVisit.Outcome profile ready bindings older destination inst
        type (layout destination.width element) entries index pointer output lhs rhs last cursor checkNext canonNext seen (next pointer)))
    (visit : ∀ pointer bytes lhs rhs check canon,
      TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      next pointer bytes lhs rhs check canon → target pointer bytes lhs rhs check canon) :
    CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon
      checkNext canonNext (fun lhs rhs last cursor pointer seen => CollectionVisit.Outcome profile ready bindings older destination inst
        type (layout destination.width element) entries index pointer output lhs rhs last cursor checkNext canonNext seen (target pointer)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal.collectionTrackEntries leading run visit

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
