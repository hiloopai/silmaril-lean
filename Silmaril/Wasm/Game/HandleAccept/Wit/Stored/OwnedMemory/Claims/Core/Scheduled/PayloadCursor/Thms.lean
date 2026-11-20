module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open ReturnFrame.Occurrence (RetainsBelowTop)

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

theorem RecordDestination.check_width (destination : RecordDestination) (store : CStore (core3 grow))
    (checked : destination.check store = .ok ()) :
    (core3 grow).memAddrType? store.core destination.memory = some destination.width :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.check_width destination store checked

/-- After a certified prefix, a canonical record or tuple still uses the checked
width for the next field's alignment and cursor increment. This is the actual
read step, not a claim that the child succeeds or that guest bytes are unchanged. -/
theorem RecordDestination.memory_cursor (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (storeField : Nat → Field → Nat → P (core3 grow) Host Unit)
    (field : Field) (fields : List Field) (cursor index : Nat)
    (finish : Unit → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (memorySequence (ptrType (destination.context inst))
      storeField (field :: fields) cursor index >>= finish), segments⟩ :: rest) :
    let area := layout destination.width field.type
    let ptr := alignTo cursor area.alignment
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog (do
          storeField index field ptr
          let result ← memorySequence (ptrType (destination.context inst)) storeField fields
            (ptr + area.size) (index + 1)
          finish result), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.memory_cursor
    run destination inst checked storeField field fields cursor index finish focused

/-- The allocation instruction and continuation precede both range checks. -/
theorem listRange_focus (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) :
    (allocateListRange cx area count >>= finish) =
      .op (.call (.reallocate cx 0 0 area.alignment.bytes (count * area.size))) (listRangeResume cx area count finish) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.list_range_focus cx area count finish

/-- A dynamic collection installs the real allocator and exact saved frame. -/
theorem listRange_install (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (allocateListRange cx area count >>= finish),
      segments⟩ :: rest) :
    let request := Call.reallocate cx 0 0 area.alignment.bytes (count * area.size)
    Step profile ready dispatch after .tau { after with ctl :=
      ⟨thread, .prog (dispatch request), .prog (listRangeResume cx area count finish) :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.list_range_install cx area count finish focused

/-- A dynamic collection dispatches the real allocator before either range check.
The saved continuation does not capture the pre-allocation store. -/
theorem listRange_call (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (allocateListRange cx area count >>= finish),
      segments⟩ :: rest) :
    let request := Call.reallocate cx 0 0 area.alignment.bytes (count * area.size)
    ∃ resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (validateListRange cx area count pointer >>= finish)) ∧
      Step profile ready dispatch after .tau
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } :=
  ⟨listRangeResume cx area count finish, fun _ => rfl, listRange_install cx area count finish focused⟩

/-- Evaluate just the resumed range check, using the reached store. Alignment
traps before a memory read; a bounds trap retains the callback's effects. On
success, post-allocation claim checks and element writes are still ahead. -/
theorem RecordDestination.listRange_body (destination : RecordDestination) (inst : InstId)
    (area : Layout) (count pointer : Nat) (store : CStore (core3 grow)) (host : Host)
    (thread : Option ThreadId) :
    Plain.runBody (validateListRange (destination.context inst) area count pointer) store host (some thread) =
      (store, host, if pointer ≠ alignTo pointer area.alignment then .error (.trapped .unalignedPointer)
        else match (core3 grow).memSize? store.core destination.memory with
        | none => .error (.trapped (.internal "dangling memory address"))
        | some size => if pointer + count * area.size ≤ size then .ok pointer
            else .error (.trapped .outOfBounds)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.list_range_body
    destination inst area count pointer store host thread

/-- From a reached allocator return, the actual scheduler resumes the range
check. It either reaches the continuation with the callback's store and host
still in place or traps from that reached state without running the continuation. -/
theorem RecordDestination.listRange_resume (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (finish : Nat → P (core3 grow) Host (Ret (core3 grow)))
    (resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : after.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let body := validateListRange (destination.context inst) area count pointer
    match (Plain.runBody body after.store after.host (some thread)).2.2 with
    | .ok value => ∃ labels, (∀ label ∈ labels, label = .tau) ∧
        RetainsBelowTop profile ready dispatch after labels
          { after with ctl := ⟨thread, .prog (finish value), segments⟩ :: rest }
    | .error (.trapped reason) => ∃ count, Machine.Steps profile ready dispatch after
        (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg after)
    | .error _ => False :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.list_range_resume
    destination inst area count pointer finish resume resumes returned

/-- A valid allocator return reaches the live checked collection plan. The
check reads the allocator's reached store and writer without updating either.
The continuation receives a fresh result even when the dry run before realloc
succeeded. A refusal branch can therefore stop before any element or descriptor
write without losing an earlier transfer or callback effect. -/
theorem RecordDestination.listRange_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    (finish : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let address ← validateListRange (destination.context inst) area count pointer
      let verdict ← (Record.authority recordClaims Limits.spec (destination.context inst)).prepare plan
      finish address verdict))
    {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (aligned : pointer = alignTo pointer area.alignment) {bytes : Nat}
    (sized : (core3 grow).memSize? reached.store.core destination.memory = some bytes)
    (bounds : pointer + count * area.size ≤ bytes) :
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧
      RetainsBelowTop profile ready dispatch reached labels
        { reached with ctl := ⟨thread, .prog (finish pointer
          (Record.prepare reached.store reached.host.writer plan)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.list_range_recheck
    reached destination inst area count pointer plan finish resume resumes returned aligned sized bounds

/-- Start the shared memory/flat emitter from its successful compilation. The
canonical value, recursive layout, and ordered receipts all refer to the very
field used by the scheduled program. Dry-run rejection reaches the typed
return without changing claims; success reads the checked width before testing
ABI fit. Neither branch has yet canonicalized or written the root. -/
theorem RecordDestination.compiled_payload_start {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (type : Stored.TypeOf) (payload : OwnedMemory.Payload type) (output : Stored.Lower.Output)
    (field : Field) (plan : List Object)
    (finish : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) type payload output = .ok (field, plan))
    (destinationChecked : destination.check reached.store = .ok ()) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Record.lowerValue recordClaims Limits.spec Quirks.none
      (destination.context inst) type payload output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    field.value = payload.val.value ∧ field.LayoutMatches type ∧
    payload.val.owners = field.objects.filterMap Object.ownerReceipt ∧
    match Record.prepare reached.store reached.host.writer field.objects with
    | .error issue => Machine.Steps profile ready dispatch reached [.tau, .tau]
        { reached with ctl := ⟨thread, .prog (finish (.error issue)), segments⟩ :: rest }
    | .ok () => Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (
          if !Stored.Lower.fits Quirks.none destination.encoding destination.width type payload.val.value then
            finish (.error (.preflight (.abi .allocationPrecondition)))
          else Internal.emitValue Limits.spec Quirks.none cx authority destination.width type field output >>= finish),
          segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor.compiled_payload_start
    reached destination inst type payload output field plan finish compiled destinationChecked focused

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
