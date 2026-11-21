module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

/-- The canonical width read at a reached collection cursor supplies the same
layout as the linked destination. The two steps install the exact realloc
request and save validation, element stores, and descriptor publication. -/
theorem RecordDestination.canonical_dynamic_call (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (element : Stored.TypeOf) (entries : List Field) (output : Stored.Lower.Output)
    (storeEntry : AddrType → Field → Nat → P (core3 grow) Host Unit)
    (finish : output.Result → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (canonicalDynamic (destination.context inst) destination.width
      element entries storeEntry output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        elementSequence (fun _ => storeEntry destination.width) entries area.size ptr 0
        let result ← Endpoints.ListLower.publish cx destination.width ptr entries.length output
        finish result)) ∧
      Machine.Steps profile ready dispatch after [.tau, .tau]
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.canonical_dynamic_call
    run destination inst checked element entries output storeEntry finish focused

/-- After the checked traversal's initial live dry run succeeds, it installs
the same realloc request. Its continuation inserts plan revalidation after
canonical range validation and before either element or descriptor writes. -/
theorem RecordDestination.checked_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (prepared : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .ok ())
    {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Internal.runField Limits.spec Quirks.none (destination.context inst)
      (Record.authority recordClaims Limits.spec (destination.context inst)) destination.width
      (.dynamic type element entries) index output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let verdict ← authority.prepare (Field.listObjects entries)
        let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
          element entries index output ptr verdict
        finish result)) ∧
      Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.checked_dynamic_call
    reached destination inst type element entries index output finish prepared focused

/-- At matching reached dynamic cursors, both paths dispatch the identical
linked realloc program even if their writers differ after earlier spends.
`HostFrame.paired_steps` shares its actual prefix up to a changed host read
or the common result. The checked continuation then revalidates the live plan. -/
theorem RecordDestination.paired_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig))
    {initial canonical checked : Machine.Config (core3 grow) (HostState sig)} {trace}
    (canonicalRun : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) initial trace canonical)
    (destination : RecordDestination) (inst : InstId) (checkedDestination : destination.check initial.store = .ok ())
    (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (storeEntry : AddrType → Field → Nat → Session grow sig Unit)
    (finishCanonical : output.Result → Session grow sig (Ret (core3 grow)))
    (finishChecked : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (prepared : Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .ok ())
    {thread segments rest}
    (canonicalAt : canonical.ctl = ⟨thread, .prog (canonicalDynamic (destination.context inst) destination.width
      element entries storeEntry output >>= finishCanonical), segments⟩ :: rest)
    (checkedAt : checked.ctl = ⟨thread, .prog (Internal.runField Limits.spec Quirks.none (destination.context inst)
      (Record.authority recordClaims Limits.spec (destination.context inst)) destination.width
      (.dynamic type element entries) index output >>= finishChecked), segments⟩ :: rest)
    (same : { checked with ctl := canonical.ctl, host := canonical.host } = canonical) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let body := dispatch (.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size))
    ∃ checkedResume canonicalResume : Machine.ReturnFrame.Continuation (core3 grow) (HostState sig),
      let checkedCall := { checked with ctl := ⟨thread, .prog body, .prog checkedResume :: segments⟩ :: rest }
      let canonicalCall := { canonical with ctl := ⟨thread, .prog body, .prog canonicalResume :: segments⟩ :: rest }
      (∀ pointer, checkedResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let authority := Record.authority recordClaims Limits.spec cx
        let verdict ← authority.prepare (Field.listObjects entries)
        let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
          element entries index output ptr verdict
        finishChecked result)) ∧
      (∀ pointer, canonicalResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        elementSequence (fun _ => storeEntry destination.width) entries area.size ptr 0
        let result ← Endpoints.ListLower.publish cx destination.width ptr entries.length output
        finishCanonical result)) ∧
      Machine.Steps profile ready dispatch checked [.tau, .tau, .tau] checkedCall ∧
      Machine.Steps profile ready dispatch canonical [.tau, .tau] canonicalCall ∧
      Machine.HostFrame.Paired checkedResume canonicalResume checkedCall canonicalCall :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.paired_dynamic_call
    bindings canonicalRun destination inst checkedDestination type element entries index output storeEntry
    finishCanonical finishChecked prepared canonicalAt checkedAt same

/-- On a shared allocator return, the same invalid range traps both sides
from the reached state. For a valid range the canonical path enters its
suffix while the checked path obtains a fresh, possibly refusing verdict. -/
theorem RecordDestination.paired_range_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {checked canonical : Machine.Config (core3 grow) (HostState sig)}
    {checkedResume canonicalResume : Machine.ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {changes : Machine.ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : Machine.HostFrame.Related.Paired changes checked canonical)
    (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    (checkNext : Nat → Except Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkedBody : checkedResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let verdict ← (Record.authority recordClaims Limits.spec (destination.context inst)).prepare plan
      checkNext ptr verdict))
    (canonicalBody : canonicalResume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext))
    {thread checkedFrames canonicalFrames checkedRest canonicalRest}
    (checkedAt : checked.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog checkedResume :: checkedFrames⟩ :: checkedRest)
    (canonicalAt : canonical.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog canonicalResume :: canonicalFrames⟩ :: canonicalRest)
    {bytes : Nat} (sized : (core3 grow).memSize? checked.store.core destination.memory = some bytes)
    (canonicalDispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)) := dispatch) :
    let trapped := fun reason =>
      (∃ steps, Machine.Steps profile ready dispatch checked (List.replicate steps .tau ++ [.trap reason])
        (Machine.StepDefs.trapCfg checked)) ∧
      (∃ steps, Machine.Steps profile ready canonicalDispatch canonical (List.replicate steps .tau ++ [.trap reason])
        (Machine.StepDefs.trapCfg canonical))
    if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      (∃ labels, (∀ label ∈ labels, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready dispatch checked labels
        { checked with ctl := ⟨thread, .prog (checkNext pointer (Record.prepare checked.store checked.host.writer plan)),
          checkedFrames⟩ :: checkedRest }) ∧
      (∃ labels, (∀ label ∈ labels, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready canonicalDispatch canonical labels
        { canonical with ctl := ⟨thread, .prog (canonNext pointer), canonicalFrames⟩ :: canonicalRest })
    else trapped .outOfBounds :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.paired_range_recheck
    paired destination inst area count pointer plan checkNext canonNext checkedBody canonicalBody checkedAt canonicalAt sized canonicalDispatch

/-- A checked return from realloc validates range and the live plan before
entering element traversal. Both branches retain the reached store and
writer up to this point, not the state before the callback. -/
theorem RecordDestination.checked_dynamic_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (pointer : Nat) (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let cx := destination.context inst
      let authority := Record.authority recordClaims Limits.spec cx
      let ptr ← validateListRange cx (layout destination.width element) entries.length pointer
      let verdict ← authority.prepare (Field.listObjects entries)
      let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
        element entries index output ptr verdict
      finish result)) {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (aligned : pointer = alignTo pointer (layout destination.width element).alignment) {bytes : Nat}
    (sized : (core3 grow).memSize? reached.store.core destination.memory = some bytes)
    (bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready dispatch reached labels
        { reached with ctl := ⟨thread, .prog (checkedDynamicContinue Limits.spec Quirks.none cx authority
            destination.width element entries index output pointer
            (Record.prepare reached.store reached.host.writer (Field.listObjects entries)) >>= finish),
          segments⟩ :: rest } :=
  destination.listRange_recheck reached inst (layout destination.width element) entries.length pointer
    (Field.listObjects entries) (fun ptr verdict => checkedDynamicContinue Limits.spec Quirks.none
      (destination.context inst) (Record.authority recordClaims Limits.spec (destination.context inst))
      destination.width element entries index output ptr verdict >>= finish) resume resumes returned aligned sized bounds

/-- After a linked allocator prefix, the same destination address still has
the original width and its already-valid region still fits. The returned
range is checked separately, in the reached store. Invalid returns go to the
canonical trap configuration, not to the typed completion continuation. -/
theorem RecordDestination.linked_range_resume {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig)) {initial reached : Machine.Config (core3 grow) (HostState sig)}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) initial trace reached)
    (growing : initial.CoreGrowing)
    (installs : ∀ {current next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) initial leading current →
      Step profile ready (specDispatch ready (host bindings)) current label next →
      LinkedPayloadInstall bindings current label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) current label)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check initial.store = .ok ())
    (start length initialBytes : Nat) (sized : (core3 grow).memSize? initial.store.core destination.memory = some initialBytes)
    (oldBounds : start + length ≤ initialBytes) (area : Layout) (count pointer : Nat)
    (finish : Nat → Session grow sig (Ret (core3 grow))) (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let trapped := fun reason => ∃ steps, Machine.Steps profile ready dispatch reached
      (List.replicate steps .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg reached)
    ptrTypeIn reached.store (destination.context inst) = destination.width ∧
    ∃ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes ∧
      initialBytes ≤ bytes ∧ start + length ≤ bytes ∧
      if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
      else if pointer + count * area.size ≤ bytes then
        ∃ labels, (∀ label ∈ labels, label = .tau) ∧
          Machine.Steps profile ready dispatch reached labels
            { reached with ctl := ⟨thread, .prog (finish pointer), segments⟩ :: rest }
      else trapped .outOfBounds :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.linked_range_resume
    bindings run growing installs destination inst checked start length initialBytes sized oldBounds area count pointer
    finish resume resumes returned

/-- Cut a returned collection at its live refusal. A bad returned pointer
traps first in the real scheduler. If its range fits, the live plan read
reaches the typed error continuation before any element or descriptor write.
That cut keeps the entire allocator-reached state, including callback writes
and any earlier claim spends. It is not a canonical error or a rollback. -/
theorem RecordDestination.linked_dynamic_refusal {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig)) {initial reached : Machine.Config (core3 grow) (HostState sig)}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) initial trace reached)
    (growing : initial.CoreGrowing)
    (installs : ∀ {current next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) initial leading current →
      Step profile ready (specDispatch ready (host bindings)) current label next →
      LinkedPayloadInstall bindings current label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) current label)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check initial.store = .ok ())
    (start length initialBytes : Nat) (sized : (core3 grow).memSize? initial.store.core destination.memory = some initialBytes)
    (oldBounds : start + length ≤ initialBytes) (element : Stored.TypeOf) (entries : List Field)
    (index pointer : Nat) (output : Stored.Lower.Output)
    (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let cx := destination.context inst
      let authority := Record.authority recordClaims Limits.spec cx
      let ptr ← validateListRange cx (layout destination.width element) entries.length pointer
      let verdict ← authority.prepare (Field.listObjects entries)
      let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
        element entries index output ptr verdict
      finish result)) {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (issue : Endpoints.RecordLower.Issue)
    (refusal : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .error issue) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let trapped := fun reason => ∃ steps, Machine.Steps profile ready dispatch reached
      (List.replicate steps .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg reached)
    let area := layout destination.width element
    let stopped := match issue with
      | .preflight bad => Endpoints.RecordLower.Issue.field index (.afterAllocation bad)
      | other => Endpoints.RecordLower.Issue.nested index other
    ptrTypeIn reached.store (destination.context inst) = destination.width ∧
    ∃ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes ∧
      initialBytes ≤ bytes ∧ start + length ≤ bytes ∧
      if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
      else if pointer + entries.length * area.size ≤ bytes then
        ∃ labels, (∀ label ∈ labels, label = .tau) ∧
          Machine.Steps profile ready dispatch reached labels
            { reached with ctl := ⟨thread, .prog (finish (.error stopped)), segments⟩ :: rest }
      else trapped .outOfBounds :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.linked_dynamic_refusal
    bindings run growing installs destination inst checked start length initialBytes sized oldBounds element entries
    index pointer output finish resume resumes returned issue refusal

/-- A child placed by an aligned record or tuple cursor is in bounds after a
certified prefix. Execute the checked nested aggregate's actual bounds read
and proceed with the same reached state; this does not validate new pointers. -/
theorem RecordDestination.record_field_guard (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (fields : List Layout) (base index offset bytes : Nat) (field : Layout)
    (aligned : (recordAlignment fields).bytes ∣ base)
    (member : fields[index]? = some field) (placed : (fieldOffsets base fields)[index]? = some offset)
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (bounds : base + (recordLayout fields).size ≤ bytes)
    (finish : P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (checkInBounds (destination.context inst) offset field.size >>= fun _ => finish),
      segments⟩ :: rest) :
    offset % field.alignment.bytes = 0 ∧
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog finish, segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection.record_field_guard
    run destination inst checked fields base index offset bytes field aligned member placed sized bounds finish focused

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
