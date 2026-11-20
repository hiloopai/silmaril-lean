module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Carry the older caller slots from the actual allocation install through
the same marked callback path and valid range/recheck suffix. The checked
suffix may enter its children or stop with a typed live-claim refusal. -/
theorem ReturnRangeTrace.through_install {start entered reached after : State grow sig} {leading labels}
    (install : ∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings))
      start (.active 0 depth) leading entered (.active 0 (depth + 1)))
    (run : ReturnRangeTrace profile ready bindings entered reached labels after (some (.active 0 0))) :
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) start (leading ++ labels) after :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit.returnRangeThroughInstall install run

/-- On the marked return, continue only if both range validation and the
fresh checked authority plan succeed. A refusal reaches the real typed
error continuation and leaves the reference at its reached entry prefix. -/
theorem RangeCutOver.visit_collection {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (area : Layout) (entries : List Field)
    (index pointer : Nat) (output : Lower.Output) {left right last : State grow sig}
    {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) (next : CollectionVisit.Next grow sig)
    (cut : RangeCutOver profile ready bindings older resume left right last check destination area entries.length pointer
      (Field.listObjects entries) (fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)
      (fun ptr => canonicalCollectionTail destination inst entries area output ptr
        (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) seen False (some (.active 0 0)))
    (visit : ∀ bytes reference canon, CollectionVisit.Admitted older destination area entries pointer bytes left last reference check canon →
      next bytes
        { last with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
        { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) } check canon) :
    CollectionVisit.Outcome profile ready bindings older destination inst type area entries index pointer output
      left right last check checkNext canonNext seen next :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit.afterRange
    destination inst type area entries index pointer output checkNext canonNext next cut visit

/-- Use the allocation-time map placement at the reached return. Compare the
actual map entries and final descriptor, or stop before entries on refusal
or range trap. Key and value comparisons run only after admission. -/
theorem RangeCutOver.visit_memory_map {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entries : List Field)
    (index pointer address : Nat) {left right last : State grow sig}
    {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (children : ∀ entry ∈ entries, MapEntryRules (grow := grow) profile ready (specDispatch ready (host bindings))
      destination inst key element entry)
    (cut : let area := layout destination.width (.record (mapEntryFields key element))
      RangeCutOver profile ready bindings older resume left right last check destination area entries.length pointer
        (Field.listObjects entries) (fun ptr live => checkedCollectionTail destination inst entries area index (.memory address) ptr live >>= checkNext)
        (fun ptr => canonicalCollectionTail destination inst entries area (.memory address) ptr
          (.memoryMap destination.width key element) >>= canonNext) seen False (some (.active 0 0))) :
    let area := layout destination.width (.record (mapEntryFields key element))
    CollectionVisit.Outcome profile ready bindings older destination inst (.map key element) area entries index pointer (.memory address)
      left right last check checkNext canonNext seen (CollectionVisit.reachesNext profile ready bindings left.store checkNext canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit.memoryMap
    destination inst key element entries index pointer address checkNext canonNext children cut

/-- Join the marked return with its tail comparison. A refused entry keeps
the canonical trace at the real entry prefix; a range trap ends both. -/
theorem CollectionVisit.Outcome.reaches {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {type : TypeOf} {area : Layout} {entries : List Field}
    {index pointer : Nat} {output : Lower.Output} {left right last : State grow sig}
    {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    {checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))}
    {canonNext : output.Result → Session grow sig (Ret (core3 grow))}
    (cut : CollectionVisit.Outcome profile ready bindings older destination inst type area entries index pointer output
      left right last check checkNext canonNext seen (CollectionVisit.reachesNext profile ready bindings left.store checkNext canonNext)) :
    ∃ canon, ReachesKeeping profile ready (specDispatch ready (host bindings))
      (fun store => Core3.Grows left.store.core store.core) left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit.reaches cut

/-- Replay every classified finite allocator prefix. On a natural return to
the marked occurrence, compare the actual indirect map with local scalar or
handle descendants, derived from their compiled layouts. No child comparison
or return guarantee is assumed. -/
theorem CollectionReplay.local_memory_map {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entries : List Field)
    (index address : Nat) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (localEntries : ∀ entry ∈ entries, LocalMemory entry)
    (replay : CollectionReplay profile ready bindings older destination inst (.map key element)
      (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst (.map key element)
      (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext
      (fun installed reference _ cursor _ _ => ∃ canonCursor, ReachesKeeping profile ready (specDispatch ready (host bindings))
        (fun store => Core3.Grows installed.store.core store.core) installed reference cursor canonCursor checkNext canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit.memoryMapReplay
    destination inst key element entries index address checkNext canonNext matched localEntries replay

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
