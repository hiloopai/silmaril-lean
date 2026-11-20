module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Thms
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Tree)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Refusing before payload lift preserves component authorities, even if writing the
error result traps. It does not undo earlier effects or forbid result/subtask updates. -/
theorem refusal_frame (ticket : Nat) (caller : CallerId) (issue : Issue) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True)
      (refuseBeforeLift (grow := grow) (sig := sig) ticket caller issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.refusal_frame
    ticket caller issue before

/-- Given the same guarded caller record, the checked error and reference resolution
have identical continuations after the store read, including the indirect write and traps. -/
theorem resolve_error_agrees (ticket : Nat) (caller : CallerId) (snapshot : CStore (core3 grow))
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (record : ArenaField.callers.get? snapshot caller = some (.lower subtask cx args pos ft limits results))
    (type : ft.result = some resultType) (mode : results ≤ 1) :
    ∃ checked reference : CStore (core3 grow) → Session grow sig (Ret (core3 grow)),
      resolveError ticket caller = .op (S := Eff (core3 grow) (HostState sig)) .get checked ∧
      (do
        lowerOnResolve Limits.spec Quirks.none caller (some [.variant 1 none])
        pure (Ret.cancel (E := core3 grow) .none)) = .op (S := Eff (core3 grow) (HostState sig)) .get reference ∧
      checked snapshot = reference snapshot :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.resolve_error_agrees
    ticket caller snapshot subtask cx args pos ft limits results record type mode

/-- Registration before canonical result lowering is only a preview. At this step,
the reference program receives the candidate handle, and the writer is unchanged. -/
theorem resolve_begin {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket : Nat) (caller : CallerId) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 writer.accepted.length))])
          completeResolvedTree ticket tree writer.accepted.length), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_begin
    ticket caller tree writer registered room pending

/-- Once the canonical result program returns, valid live registration with the checked
handle commits the root. This branch publishes before it records
the reply; completion does not overwrite or roll back the reached reference store. -/
theorem complete_commit {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau]
      { config with
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.complete_commit
    ticket handle tree writer registered expected room pending ⟨0⟩).reaches.1

/-- If live registration instead predicts a different handle, record a typed
diagnostic and lock down the reached store without publishing or replying. -/
theorem complete_stale {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (stale : handle ≠ writer.accepted.length)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg
        { config with host := config.host.record (.bindingTrap ticket .wrongResultType) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.complete_stale
    ticket handle tree writer registered stale pending

/-- The success path reads the reached caller record, using its actual length limit,
context and result cursor. If lowering traps, neither resolution nor publication runs. -/
theorem resolve_caller {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (pos : Nat) (ft : WIT.FuncType Empty RtId) (params results : Nat)
    (callerRecord : ArenaField.callers.get? config.store caller =
      some (.lower subtask cx args pos ft params results))
    (pending : config.ctl = ⟨thread, .prog (do
      lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 handle))])
      completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
        maybeOnProgress subtask
        let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 0 (some (Val.u32 handle))]
          ft.result.toList (some ⟨args, pos⟩)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_caller
    ticket handle caller tree subtask cx args pos ft params results callerRecord pending

/-- The reached caller's `maybeOnProgress` queues or replaces its subtask
event before result lowering if it has a caller index. Unindexed calls
leave the pending slot unchanged. Neither branch resolves or delivers. -/
theorem resolve_progress {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (pos : Nat) (ft : WIT.FuncType Empty RtId) (params results : Nat) (record : Subtask)
    (callerRecord : ArenaField.callers.get? config.store caller = some (.lower subtask cx args pos ft params results))
    (live : config.store.subtask? subtask = some record)
    (focused : config.ctl = ⟨thread, .prog (do
      lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 handle))])
      completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    let queued := if record.index.isSome then config.store.setPendingSt (.subtask subtask) (.subtask subtask)
      else config.store
    let final : Config (core3 grow) (HostState sig) := { config with store := queued, ctl :=
      ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 0 (some (Val.u32 handle))]
          ft.result.toList (some ⟨args, pos⟩)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest }
    Steps prof ready dispatch config (.tau :: .tau :: if record.index.isSome then [.tau] else []) final ∧
      final.store.subtask? subtask = some { record with common := if record.index.isSome then
        { record.common with pending := some (.subtask subtask) } else record.common } :=
  let result := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_progress
    (prof := prof) (ready := ready) (dispatch := dispatch)
    ticket handle caller tree subtask cx args pos ft params results record callerRecord live focused
  ⟨(result.1 ⟨0⟩).reaches.1, result.2⟩

/-- Exact reference program for the indirect acceptor reply, in either memory width.
The typed cursor, alignment and full eight-byte range checks precede any write. The
error writes only its discriminant; success also writes the handle at offset four. -/
theorem lower_result_program (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor)
    (maxResults : Nat) (indirect : maxResults ≤ 1) (reply : Option Nat) :
    (lowerFlatValues Limits.spec Quirks.none cx maxResults
      [reply.elim (.variant 1 none) (fun handle => .variant 0 (some (Val.u32 handle)))]
      [resultType] (some cursor) : Session grow sig (List FlatValue)) =
    (do
      let width ← ptrType cx
      let (pointer, _) ← cursor.next (ABI.pointerType width)
      let out := flatNat pointer
      trapIf (decide (out ≠ ABI.alignTo out .four)) .unalignedPointer
      checkInBounds cx out 8
      let _ ← ptrType cx
      let _ ← ptrType cx
      let field := ABI.alignTo out .four
      let _ ← match reply with
        | none => storeInt cx 1 field 1
        | some handle =>
          storeInt cx 0 field 1
          storeInt cx handle (ABI.alignTo (field + 1) .four) 4
      return []) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.lower_result_program
    cx cursor maxResults indirect reply

theorem result_payload_offset (out : Nat) (aligned : out = ABI.alignTo out .four) :
    ABI.alignTo (ABI.alignTo out .four + 1) .four = out + 4 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.result_payload_offset out aligned

/-- The real indirect success path writes the tag then the handle. Its full range
check guarantees both writes in Core 3.0; neither changes the queued subtask. -/
theorem resolve_indirect_write {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor) (maxResults : Nat)
    (indirect : maxResults ≤ 1) (pointer : FlatValue) (address : Nat)
    (atCursor : cursor.values[cursor.pos]? = some pointer)
    (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) .four)
    (memory : cx.opts.memory = some address) (size : Nat)
    (sized : (core3 grow).memSize? config.store.core address = some size)
    (inBounds : flatNat pointer + 8 ≤ size) (record : Subtask)
    (live : config.store.subtask? subtask = some record)
    (focused : config.ctl = ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx maxResults
          [.variant 0 (some (Val.u32 handle))] [resultType] (some cursor)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    let out := flatNat pointer
    let tagged := writeMemSt address out (intToLE 1 0) config.store
    let final : Config (core3 grow) (HostState sig) := { config with
      store := writeMemSt address (out + 4) (intToLE 4 handle) tagged
      ctl := ⟨thread, .prog (do
        Subtask.resolve subtask .returned []
        completeResolvedTree ticket tree handle), segments⟩ :: rest }
    Steps prof ready dispatch config (List.replicate 8 .tau) final ∧
      final.store.subtask? subtask = some record :=
  let result := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_indirect_write
    (prof := prof) (ready := ready) (dispatch := dispatch)
    ticket handle tree subtask cx cursor maxResults indirect pointer address atCursor aligned
    memory size sized inBounds record live focused
  ⟨(result.1 ⟨0⟩).reaches.1, result.2⟩

/-- With an aligned indirect result pointer but insufficient space, resolution traps
before either result write. The trap uses the store reached after progress queueing. -/
theorem resolve_indirect_range_trap {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor) (maxResults : Nat)
    (indirect : maxResults ≤ 1) (pointer : FlatValue) (address : Nat)
    (atCursor : cursor.values[cursor.pos]? = some pointer)
    (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) .four)
    (memory : cx.opts.memory = some address) (size : Nat)
    (sized : (core3 grow).memSize? config.store.core address = some size)
    (outside : size < flatNat pointer + 8)
    (focused : config.ctl = ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx maxResults
          [.variant 0 (some (Val.u32 handle))] [resultType] (some cursor)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .trap .outOfBounds] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_indirect_range_trap
    ticket handle tree subtask cx cursor maxResults indirect pointer address atCursor aligned memory size sized outside focused

/-- A misaligned indirect result pointer traps before examining the memory range. -/
theorem resolve_indirect_alignment_trap {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor) (maxResults : Nat)
    (indirect : maxResults ≤ 1) (pointer : FlatValue)
    (atCursor : cursor.values[cursor.pos]? = some pointer)
    (misaligned : flatNat pointer ≠ ABI.alignTo (flatNat pointer) .four)
    (focused : config.ctl = ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx maxResults
          [.variant 0 (some (Val.u32 handle))] [resultType] (some cursor)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .unalignedPointer] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_indirect_alignment_trap
    ticket handle tree subtask cx cursor maxResults indirect pointer atCursor misaligned focused

/-- Direct result lowering reaches resolution with two ABI words and no store change. -/
theorem resolve_direct_words {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor) (maxResults : Nat)
    (direct : 2 ≤ maxResults)
    (focused : config.ctl = ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx maxResults
          [.variant 0 (some (Val.u32 handle))] [resultType] (some cursor)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
        Subtask.resolve subtask .returned [i32Flat 0, i32Flat handle]
        completeResolvedTree ticket tree handle), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_direct_words
    ticket handle tree subtask cx cursor maxResults direct focused

/-- From the canonical tail after the result write, resolution and publication retain
the same subtask's index, lends and pending event. This does not deliver the event. -/
theorem resolve_commit {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (subtask : SubtaskId) (flat : List FlatValue) (record : Subtask)
    (live : config.store.subtask? subtask = some record)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (do
      Subtask.resolve subtask .returned flat
      completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    let final : Config (core3 grow) (HostState sig) :=
      { config with
        store := config.store.subtaskResolveSt subtask .returned flat
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest }
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau] final ∧
      final.store.subtask? subtask = some { record with state := .returned, flatResults := flat } :=
  let result := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_commit
    (prof := prof) (ready := ready) (dispatch := dispatch)
    ticket handle tree writer subtask flat record live registered expected room pending
  ⟨(result.1 ⟨0⟩).reaches.1, result.2⟩

/-- A linked caller's actual lowering limits imply an indirect result in either mode.
From the reached resolve entry with a valid out-pointer, queue progress as applicable,
write the result, resolve the same subtask, and publish. Delivery is still separate. -/
theorem resolve_linked_commit {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (callee : Callee sig) (ticket : Nat) (caller : CallerId)
    (tree : Tree sig) (writer : State sig) (subtask : SubtaskId) (record : Subtask)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (callerRecord : ArenaField.callers.get? config.store caller = some
      (.lower subtask cx args pos callee.funcType (lowerLimits callee.async_).1 (lowerLimits callee.async_).2))
    (live : config.store.subtask? subtask = some record) (context : cx.opts = callee.options)
    (pointer : FlatValue) (atCursor : args[pos]? = some pointer)
    (aligned : flatNat pointer = ABI.alignTo (flatNat pointer) .four)
    (size : Nat) (sized : (core3 grow).memSize? config.store.core callee.memory = some size)
    (inBounds : flatNat pointer + 8 ≤ size)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (focused : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    let handle := writer.accepted.length
    let out := flatNat pointer
    let queued := if record.index.isSome then config.store.setPendingSt (.subtask subtask) (.subtask subtask)
      else config.store
    let tagged := writeMemSt callee.memory out (intToLE 1 0) queued
    let written := writeMemSt callee.memory (out + 4) (intToLE 4 handle) tagged
    let final : Config (core3 grow) (HostState sig) := { config with
      store := written.subtaskResolveSt subtask .returned []
      host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
        (.returned ticket handle)
      ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest }
    Steps prof ready dispatch config (List.replicate (16 + record.index.isSome.toNat) .tau) final ∧
      final.store.subtask? subtask = some { record with
        state := .returned
        flatResults := []
        common := if record.index.isSome then { record.common with pending := some (.subtask subtask) }
          else record.common } ∧
      (∀ saved, ParkedPrefix prof ready dispatch saved config (List.replicate (16 + record.index.isSome.toNat) .tau) final) :=
  let result := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.resolve_linked_commit
    (prof := prof) (ready := ready) (dispatch := dispatch)
    callee ticket caller tree writer subtask record cx args pos callerRecord live context pointer
    atCursor aligned size sized inBounds registered room focused
  ⟨(result.1 ⟨0⟩).reaches.1, result.2, result.1⟩

/-- Delivery requires the actual queued event and an executing waitable continuation.
It clears the event, applies the reference lend release, and returns the recorded index. -/
theorem deliver_pending {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask))
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (pending : config.ctl = ⟨thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= resume),
      segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        store := (config.store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
          |>.deliverResolveSt subtask
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.deliver_pending
    subtask record index live returned indexed eventPending resume pending

/-- An actual poll makes the admitted shuffle choice, keeps its order, and
delivers the selected returned subtask. Membership and the pending slot make
the first readiness read true. A later event-buffer write is still separate. -/
theorem poll_delivers_returned {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ws : WsetId) (set : WaitableSet) (perm : List Nat) (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (setLive : config.store.wset? ws = some set) (member : .subtask subtask ∈ set.elems)
    (allowed : Allowed prof (.shuffle set.elems.length) perm)
    (selects : (applyPerm perm set.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask))
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask))
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetPoll ws >>= resume), segments⟩ :: rest) :
    let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    Steps prof ready dispatch config [.tau, .tau, .choice (.shuffle set.elems.length) perm, .tau, .tau, .tau, .tau]
      { config with
        store := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
          |>.deliverResolveSt subtask
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.poll_delivers_returned
    ws set perm subtask record index setLive member allowed selects live returned indexed eventPending resume focused

/-- Consume the selected return event in the shared wait/poll selection body. -/
theorem get_delivers_returned {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ws : WsetId) (set : WaitableSet) (perm : List Nat)
    (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (setLive : config.store.wset? ws = some set)
    (allowed : Allowed prof (.shuffle set.elems.length) perm)
    (selects : (applyPerm perm set.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask))
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask))
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetGetPendingEvent ws >>= resume), segments⟩ :: rest) :
    let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    Steps prof ready dispatch config [.tau, .choice (.shuffle set.elems.length) perm, .tau, .tau, .tau, .tau]
      { config with
        store := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
          |>.deliverResolveSt subtask
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.get_delivers_returned
    ws set perm subtask record index setLive allowed selects live returned indexed eventPending resume focused

/-- Selection on a live but empty set still shuffles before the internal trap. -/
theorem get_shuffles_empty {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ws : WsetId) (record : WaitableSet) (perm : List Nat)
    (setLive : config.store.wset? ws = some record) (empty : config.store.wsetHasEvent ws = false)
    (allowed : Allowed prof (.shuffle record.elems.length) perm)
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetGetPendingEvent ws >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .choice (.shuffle record.elems.length) perm, .tau, .tau,
      .trap (.internal "WaitableSet.get_pending_event: no pending event")]
      (StepDefs.trapCfg { config with store := config.store.wsetSetElemsSt ws (applyPerm perm record.elems) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.get_shuffles_empty ws record perm
    setLive empty allowed resume focused

/-- Execute the canonical event-buffer writes in the reached store. Both
four-byte writes follow the alignment and whole eight-byte range checks. -/
theorem unpack_event_write {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (cx : LiftLowerContext (core3 grow)) (ptr address size : Nat) (event : EventTuple)
    (aligned : ptr % 4 = 0) (memory : cx.opts.memory = some address)
    (sized : (core3 grow).memSize? config.store.core address = some size) (inBounds : ptr + 8 ≤ size)
    (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    let indexed := writeMemSt address ptr (u32Bytes event.index) config.store
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau]
      { config with
        store := writeMemSt address (ptr + 4) (u32Bytes event.payload) indexed
        ctl := ⟨thread, .prog (resume event.code.toNat), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.unpack_event_write
    cx ptr address size event aligned memory sized inBounds resume focused

/-- An unaligned event buffer traps before reading the range or writing bytes. -/
theorem unpack_event_bad_alignment {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (event : EventTuple)
    (misaligned : ptr % 4 ≠ 0) (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.trap .unalignedPointer] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.unpack_event_bad_alignment
    cx ptr event misaligned resume focused

theorem unpack_event_bad_range {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (cx : LiftLowerContext (core3 grow)) (ptr address size : Nat) (event : EventTuple)
    (aligned : ptr % 4 = 0) (memory : cx.opts.memory = some address)
    (sized : (core3 grow).memSize? config.store.core address = some size) (outside : size < ptr + 8)
    (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .outOfBounds] (StepDefs.trapCfg config) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.unpack_event_bad_range
    cx ptr address size event aligned memory sized outside resume focused

/-- A late range trap locks down the store after event consumption and lend
release. Neither event word is written and the already reached host is kept. -/
theorem poll_returned_bad_range {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId} {segments rest}
    (ws : WsetId) (set : WaitableSet) (perm : List Nat) (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (setLive : config.store.wset? ws = some set) (member : .subtask subtask ∈ set.elems)
    (allowed : Allowed prof (.shuffle set.elems.length) perm)
    (selects : (applyPerm perm set.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask))
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask))
    (cx : LiftLowerContext (core3 grow)) (ptr address size : Nat)
    (aligned : ptr % 4 = 0) (memory : cx.opts.memory = some address)
    (sized : (core3 grow).memSize? config.store.core address = some size) (outside : size < ptr + 8)
    (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetPoll ws >>= fun event => unpackEvent cx ptr event >>= resume),
      segments⟩ :: rest) :
    let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    let delivered := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
      |>.deliverResolveSt subtask
    Steps prof ready dispatch config
      [.tau, .tau, .choice (.shuffle set.elems.length) perm, .tau, .tau, .tau, .tau, .tau, .trap .outOfBounds]
      { config with store := StepDefs.lockdownSt delivered, ctl := [] } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.poll_returned_bad_range
    ws set perm subtask record index setLive member allowed selects live returned indexed eventPending cx ptr address size
    aligned memory sized outside resume focused

/-- A parked Core poll resolves the live waitable-set handle and consumes the
selected returned event before validating the output buffer. A valid buffer
receives both words before Core resumes. Alignment and range traps keep event
consumption and lend release but perform neither write nor Core resumption. -/
theorem parked_poll_returned {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {config : Config (core3 grow) (HostState sig)} {segments rest}
    (impl : HostImpl (core3 grow) (HostState sig)) (mem : Nat)
    (slot out : FlatValue) (ws : WsetId) (th : ThreadId) (active : Thread) (task : Task (core3 grow))
    (instance_ : InstState) (core : (core3 grow).Thread (CanonHost (core3 grow)))
    (next : List FlatValue → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨some th, .core core next, segments⟩ :: rest)
    (callout : (core3 grow).status config.store.core core =
      .callout (.builtin (.waitableSetPoll mem) task.inst) [slot, out])
    (liveThread : ArenaField.threads.get? config.store th = some active)
    (liveTask : ArenaField.tasks.get? config.store active.task = some task)
    (liveInst : ArenaField.insts.get? config.store task.inst = some instance_)
    (mayLeave : instance_.mayLeave = true) (handle : instance_.handles.get? (flatNat slot) = some (.wset ws))
    (set : WaitableSet) (perm : List Nat) (subtask : SubtaskId) (record : Subtask) (index : Nat)
    (setLive : config.store.wset? ws = some set) (member : .subtask subtask ∈ set.elems)
    (allowed : Allowed prof (.shuffle set.elems.length) perm)
    (selects : (applyPerm perm set.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm set.elems)).waitableHasEvent = some (.subtask subtask))
    (live : config.store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (eventPending : record.common.pending = some (.subtask subtask)) :
    let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    let delivered := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
      |>.deliverResolveSt subtask
    let written := writeMemSt mem (flatNat out + 4) (u32Bytes SubtaskState.returned.toNat)
      (writeMemSt mem (flatNat out) (u32Bytes index) delivered)
    let deliveredLabels := List.replicate 10 (Label.tau (E := core3 grow) (σ := HostState sig)) ++
      [.choice (.shuffle set.elems.length) perm] ++ List.replicate 4 .tau
    (flatNat out % 4 ≠ 0 → Steps prof ready (specDispatch ready impl) config (deliveredLabels ++ [.trap .unalignedPointer])
      { config with store := StepDefs.lockdownSt delivered, ctl := [] }) ∧
    (∀ size, flatNat out % 4 = 0 → (core3 grow).memSize? config.store.core mem = some size →
      (flatNat out + 8 ≤ size → Steps prof ready (specDispatch ready impl) config (deliveredLabels ++ List.replicate 6 .tau)
        { config with store := written, ctl := ⟨some th,
            .core ((core3 grow).resume written.core core (.values [i32Flat EventCode.subtask.toNat])) next,
            segments⟩ :: rest }) ∧
      (size < flatNat out + 8 → Steps prof ready (specDispatch ready impl) config
        (deliveredLabels ++ [.tau, .trap .outOfBounds]) { config with store := StepDefs.lockdownSt delivered, ctl := [] })) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult.parked_poll_returned
    impl mem slot out ws th active task instance_ core next focused callout liveThread liveTask liveInst mayLeave handle
    set perm subtask record index setLive member allowed selects live returned indexed eventPending

theorem host_checked (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    HostImplSafe CheckedWrite (hostWithComponent (grow := grow) bindings callees) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.hostWithComponent_safe
    bindings callees

/-- The dispatcher conserves published roots, authority, and tickets across arbitrary
machine prefixes with checked initial continuations and checked host-frame programs.
The theorem includes typed refusals and canonical traps, not just successful returns. -/
theorem checked_of_steps (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.Component.checked_of_component_steps
    bindings callees steps safe runSafe

/-- Arbitrary exports and internal scheduling from an ordinary session need no hypotheses
on the guest or its export sequence. Only injected raw programs need a write-policy proof. -/
theorem checked_of_session (bindings : List (Binding sig)) (callees : List (Callee sig))
    {prof : ProfileKind} {ready : HostReady (HostState sig)} (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  checked_of_steps bindings callees steps (Component.Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall
