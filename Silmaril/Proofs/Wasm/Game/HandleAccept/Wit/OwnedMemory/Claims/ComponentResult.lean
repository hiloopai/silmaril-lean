module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory (Tree)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {prof : ProfileKind}
  {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
  {config : Config (core3 grow) (HostState sig)} {thread : Option ThreadId}
  {segments : List (Seg (core3 grow) (HostState sig))} {rest : List (Activation (core3 grow) (HostState sig))}

private theorem parkAppend {start middle final : Config (core3 grow) (HostState sig)} {leading trailing} {saved : ThreadId}
    (prefixRun : ParkedPrefix prof ready dispatch saved start leading middle)
    (tailRun : ParkedPrefix prof ready dispatch saved middle trailing final) :
    ParkedPrefix prof ready dispatch saved start (leading ++ trailing) final := by
  induction prefixRun with
  | done => exact tailRun
  | step run kept _ ih => exact .step run kept (ih tailRun)

theorem resolve_begin (ticket : Nat) (caller : CallerId) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (room : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (resolveTree ticket caller tree), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 writer.accepted.length))])
          completeResolvedTree ticket tree writer.accepted.length), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Nat.not_le.mpr room, ite_false] at step
  exact step

private theorem complete_read (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Machine.Step prof ready dispatch config .tau
      { config with ctl := ⟨thread, .prog (do
          let result ← (do
            if handle != writer.accepted.length then return .error .wrongResultType
            if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
            hostSet (({ config.host with writer } : HostState sig).record (.published ticket writer.accepted.length))
            return .ok writer.accepted.length : Session grow sig (Except Issue Nat))
          match result with
          | .error issue => reject ticket issue
          | .ok published => do
            let _ ← writeCompletion (.returned ticket published, [])
            return .cancel .none), segments⟩ :: rest } := by
  have step := Step.hostGet (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, registered, Option.any] at step
  exact step

theorem complete_commit (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer)
    (expected : handle = writer.accepted.length) (room : handle < 2 ^ 32)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    ∀ saved, ParkedPrefix prof ready dispatch saved config [.tau, .tau, .tau, .tau]
      { config with
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } := by
  subst handle
  intro saved
  refine .step (complete_read ticket writer.accepted.length tree writer registered pending) ?_ ?_
  · rw [transitionEdit, pending]
    rfl
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.not_le.mpr room]
  exact .step (.hostSet rfl) rfl (.step (.hostGet rfl) rfl (.step (.hostSet rfl) rfl (.done _)))

theorem complete_stale (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (stale : handle ≠ writer.accepted.length)
    (pending : config.ctl = ⟨thread, .prog (completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg
        { config with host := config.host.record (.bindingTrap ticket .wrongResultType) }) := by
  refine .cons (complete_read ticket handle tree writer registered pending) ?_
  simp only [bne_iff_ne.mpr stale, ite_true]
  exact .cons (.hostGet rfl) (.cons (.hostSet rfl) (.cons (.trap rfl) (.refl _)))

theorem resolve_caller (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
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
        completeResolvedTree ticket tree handle), segments⟩ :: rest } := by
  have step := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simpa [Prog.bind, callerRecord, Quirks.none, Prog.bind_assoc] using step

private theorem progress_steps (subtask : SubtaskId) (record : Subtask)
    (live : config.store.subtask? subtask = some record) (next : Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (maybeOnProgress subtask >>= fun () => next), segments⟩ :: rest) :
    let queued := if record.index.isSome then config.store.setPendingSt (.subtask subtask) (.subtask subtask)
      else config.store
    ∀ saved, ParkedPrefix prof ready dispatch saved config (.tau :: if record.index.isSome then [.tau] else [])
      { config with store := queued, ctl := ⟨thread, .prog next, segments⟩ :: rest } := by
  dsimp only
  intro saved
  have kept : (transitionEdit config (.tau : Label (core3 grow) (HostState sig))).follow (.saved saved.idx 0) =
      some (.saved saved.idx 0) := by
    rw [transitionEdit, focused]
    rfl
  have read := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) focused
  rw [CStore.subtask?] at live
  cases indexed : record.index with
  | none =>
    simp [Prog.bind, pure, live, indexed] at read ⊢
    exact .step read kept (.done _)
  | some _ =>
    simp [Prog.bind, pure, live, indexed] at read ⊢
    exact .step read kept (.step (.modify rfl) rfl (.done _))

theorem resolve_progress (ticket handle : Nat) (caller : CallerId) (tree : Tree sig)
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
    (∀ saved, ParkedPrefix prof ready dispatch saved config (.tau :: .tau :: if record.index.isSome then [.tau] else []) final) ∧
      final.store.subtask? subtask = some { record with common := if record.index.isSome then
        { record.common with pending := some (.subtask subtask) } else record.common } := by
  constructor
  · intro saved
    let next : Session grow sig (Ret (core3 grow)) := do
      let flat ← lowerFlatValues Limits.spec Quirks.none cx results [.variant 0 (some (Val.u32 handle))]
        ft.result.toList (some ⟨args, pos⟩)
      Subtask.resolve subtask .returned flat
      completeResolvedTree ticket tree handle
    refine .step (resolve_caller ticket handle caller tree subtask cx args pos ft params results callerRecord focused) ?_ ?_
    · rw [transitionEdit, focused]
      rfl
    · exact progress_steps (config := { config with
        ctl := ⟨thread, .prog (maybeOnProgress subtask >>= fun () => next), segments⟩ :: rest })
        subtask record live next rfl saved
  · by_cases indexed : record.index.isSome = true
    · simp only [ite_eq_left indexed, CStore.setPendingSt, CStore.modifyWaitableCommon, CStore.subtask?, ArenaField.get?_modify_self]
      rw [CStore.subtask?] at live
      rw [live]
      rfl
    · simpa only [ite_eq_right indexed] using live

theorem resolve_commit (ticket handle : Nat) (tree : Tree sig) (writer : State sig)
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
    (∀ saved, ParkedPrefix prof ready dispatch saved config [.tau, .tau, .tau, .tau, .tau] final) ∧
      final.store.subtask? subtask = some { record with state := .returned, flatResults := flat } := by
  constructor
  · intro saved
    have step := Step.modify (prof := prof) (hr := ready) (dispatch := dispatch) pending
    simp only [Prog.bind] at step
    refine .step step ?_ ?_
    · rw [transitionEdit, pending]
      rfl
    exact complete_commit (config := { config with
      store := config.store.subtaskResolveSt subtask .returned flat, ctl := _ })
      ticket handle tree writer registered expected room rfl saved
  · change ArenaField.subtasks.get? _ _ = _
    rw [CStore.subtaskResolveSt, ArenaField.get?_modify_self]
    rw [CStore.subtask?] at live
    simp [live]

private theorem take_returned {store : CStore (core3 grow)} (subtask : SubtaskId)
    (record : Subtask) (index : Nat) (live : store.subtask? subtask = some record)
    (returned : record.state = .returned) (indexed : record.index = some index)
    (pending : record.common.pending = some (.subtask subtask)) :
    store.takeWaitableEvent (.subtask subtask) =
      ((store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
        |>.deliverResolveSt subtask, some ⟨.subtask, index, SubtaskState.returned.toNat⟩) := by
  have cleared : (store.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }).subtask? subtask =
      some { record with common := { record.common with pending := none } } := by
    change ArenaField.subtasks.get? _ _ = _
    rw [CStore.modifyWaitableCommon, ArenaField.get?_modify_self]
    rw [CStore.subtask?] at live
    simp [live]
  simp [CStore.takeWaitableEvent, live, pending, CStore.subtaskEvent, cleared, returned, indexed,
    SubtaskState.resolved]

theorem deliver_pending (subtask : SubtaskId) (record : Subtask) (index : Nat)
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
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } := by
  have read := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) pending
  simp only [Prog.bind, take_returned subtask record index live returned indexed eventPending] at read
  refine .cons read (.cons (.modify rfl) ?_)
  simp only [CStore.takeWaitableEventSt, take_returned subtask record index live returned indexed eventPending]
  exact .refl _

theorem get_selects (ws : WsetId) (record : WaitableSet) (perm : List Nat) (selected : Waitable)
    (setLive : config.store.wset? ws = some record)
    (allowed : Allowed prof (.shuffle record.elems.length) perm)
    (selects : (applyPerm perm record.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm record.elems)).waitableHasEvent = some selected)
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetGetPendingEvent ws >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .choice (.shuffle record.elems.length) perm, .tau, .tau]
      { config with
        store := config.store.wsetSetElemsSt ws (applyPerm perm record.elems)
        ctl := ⟨thread, .prog (Waitable.getPendingEvent selected >>= resume), segments⟩ :: rest } := by
  have lookup : ArenaField.wsets.get? config.store ws = some record := setLive
  let pick := fun (elems : List Waitable) (store : CStore (core3 grow)) =>
    (match elems.find? store.waitableHasEvent with
    | some waitable => Waitable.getPendingEvent waitable
    | none => internal "WaitableSet.get_pending_event: no pending event") >>= resume
  let onChoice : List Nat → Session grow sig (Ret (core3 grow)) := fun order =>
    let elems := applyPerm order record.elems
    .op (.modify (CStore.wsetSetElemsSt ws elems)) fun _ => .op .get (pick elems)
  let afterLookup := { config with ctl := ⟨thread,
    .prog (.op (.choose (.shuffle record.elems.length)) onChoice), segments⟩ :: rest }
  have readSet := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) focused
  have reachedChoice : Machine.Step prof ready dispatch config .tau afterLookup := by
    simp only [Prog.bind, lookup] at readSet
    exact readSet
  refine .cons reachedChoice (.cons (Step.choose (m := afterLookup) (ck := .shuffle record.elems.length)
    (k := onChoice) perm rfl allowed) ?_)
  refine .cons (.modify (f := CStore.wsetSetElemsSt ws (applyPerm perm record.elems))
    (k := fun _ => .op .get (pick (applyPerm perm record.elems))) rfl) ?_
  refine .cons (.get (k := pick (applyPerm perm record.elems)) rfl) ?_
  let elems := applyPerm perm record.elems
  let shuffled := config.store.wsetSetElemsSt ws elems
  change Steps prof ready dispatch { config with
    store := shuffled
    ctl := ⟨thread, .prog (pick elems shuffled), segments⟩ :: rest } [] _
  have chosen : pick elems shuffled = (Waitable.getPendingEvent selected >>= resume) := by
    simp only [pick, shuffled, elems, selects]
  rw [chosen]
  exact .refl _

theorem poll_selects (ws : WsetId) (record : WaitableSet) (perm : List Nat) (selected : Waitable)
    (setLive : config.store.wset? ws = some record) (hasEvent : config.store.wsetHasEvent ws = true)
    (allowed : Allowed prof (.shuffle record.elems.length) perm)
    (selects : (applyPerm perm record.elems).find?
      (config.store.wsetSetElemsSt ws (applyPerm perm record.elems)).waitableHasEvent = some selected)
    (resume : EventTuple → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (wsetPoll ws >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .choice (.shuffle record.elems.length) perm, .tau, .tau]
      { config with
        store := config.store.wsetSetElemsSt ws (applyPerm perm record.elems)
        ctl := ⟨thread, .prog (Waitable.getPendingEvent selected >>= resume), segments⟩ :: rest } := by
  have readyRead := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) focused
  simp [Prog.bind, hasEvent, pure] at readyRead
  let entered := { config with ctl := ⟨thread, .prog (wsetGetPendingEvent ws >>= resume), segments⟩ :: rest }
  exact .cons readyRead (get_selects (config := entered) ws record perm selected setLive allowed selects resume rfl)

private theorem resultLayout (width : AddrType) :
    ABI.layout width resultType = ⟨.four, 2⟩ := by
  simp only [resultType, ABI.layout, ABI.layoutOption, ABI.primitiveLayout]
  rfl

private theorem resultTupleLayout (width : AddrType) :
    ABI.layout width (.tuple [resultType]) = ⟨.four, 2⟩ := by
  simp only [ABI.layout, ABI.layoutTypes, resultLayout]
  rfl

private theorem resultPayloadAlignment (width : AddrType) :
    ABI.maxCaseAlignment [ABI.layoutOption width (some (.prim .u32 : WIT.ClosedType RtId)),
      ABI.layoutOption width (none : Option (WIT.ClosedType RtId))] = .four := by
  simp only [ABI.layoutOption, ABI.layout, ABI.primitiveLayout]
  rfl

private theorem resultFlatCount (width : AddrType) :
    (ABI.flattenTypes width [resultType]).length = 2 := by
  simp [resultType, ABI.flattenTypes, ABI.flatten, ABI.flattenOption, ABI.flattenPrimitive]

private theorem store_result (cx : LiftLowerContext (core3 grow)) (out : Nat) (reply : Option Nat) :
    (store Limits.spec Quirks.none cx (.record [reply.elim (.variant 1 none)
      (fun handle => .variant 0 (some (Val.u32 handle)))]) (.tuple [resultType]) out : Session grow sig Unit) =
    (do
      let _ ← ptrType cx
      let _ ← ptrType cx
      let field := ABI.alignTo out .four
      let _ ← match reply with
        | none => storeInt cx 1 field 1
        | some handle =>
          storeInt cx 0 field 1
          storeInt cx handle (ABI.alignTo (field + 1) .four) 4
      pure ()) := by
  cases reply <;> simp only [store, storeTuple, resultLayout] <;>
    simp [resultType, store, resultPayloadAlignment, storeVariantHead, storeOpt, storePrim, Val.u32,
      IntKind.ofPrimitive, IntKind.width, IntKind.signed, discSize, ABI.discriminantAlignment,
      ABI.Alignment.bytes, Prog.bind_assoc]

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
      return []) := by
  simp [lowerFlatValues, resultFlatCount, resultTupleLayout, show maxResults < 2 by omega,
    spillPointer, ABI.Layout.size, ABI.Alignment.bytes, store_result, Prog.bind_assoc]
  cases reply <;> simp [Prog.bind_assoc]

theorem result_payload_offset (out : Nat) (aligned : out = ABI.alignTo out .four) :
    ABI.alignTo (ABI.alignTo out .four + 1) .four = out + 4 := by
  simp only [ABI.alignTo, ABI.Alignment.bytes] at aligned ⊢
  omega

private theorem write_subtask (store : CStore (core3 grow)) (address ptr : Nat)
    (bytes : ByteArray) (subtask : SubtaskId) :
    (writeMemSt address ptr bytes store).subtask? subtask = store.subtask? subtask := by
  unfold writeMemSt
  split <;> rfl

theorem resolve_indirect_write (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
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
    (∀ saved, ParkedPrefix prof ready dispatch saved config (List.replicate 8 .tau) final) ∧
      final.store.subtask? subtask = some record := by
  let out := flatNat pointer
  have payloadOffset : ABI.alignTo (flatNat pointer + 1) .four = flatNat pointer + 4 := by
    simpa only [← aligned] using result_payload_offset (flatNat pointer) aligned
  have tagWrite : ((core3 grow).memWrite? config.store.core address out (intToLE 1 0)).isSome := by
    apply Core3.memWrite?_isSome_iff.2
    exact ⟨size, sized, by change out + 1 ≤ size; omega⟩
  obtain ⟨tagCore, tagged⟩ := Option.isSome_iff_exists.mp tagWrite
  have tagSize : (core3 grow).memSize? (writeMemSt address out (intToLE 1 0) config.store).core address = some size := by
    simp only [writeMemSt, tagged]
    exact (Core3.memWrite?_memSize tagged address).trans sized
  have payloadWrite : ((core3 grow).memWrite? (writeMemSt address out (intToLE 1 0) config.store).core
      address (out + 4) (intToLE 4 handle)).isSome := by
    apply Core3.memWrite?_isSome_iff.2
    exact ⟨size, tagSize, by change out + 4 + 4 ≤ size; omega⟩
  obtain ⟨payloadCore, payload⟩ := Option.isSome_iff_exists.mp payloadWrite
  dsimp only [out] at tagged payload
  refine ⟨?_, ?_⟩
  · intro saved
    have program := lower_result_program (sig := sig) cx cursor maxResults indirect (some handle)
    simp only [Option.elim_some] at program
    rw [program] at focused
    have first := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) focused
    refine .step first ?_ ?_
    · rw [transitionEdit, focused]
      rfl
    simp [Prog.bind, FlatCursor.next, atCursor, pure, trapIf, ← aligned, checkInBounds, memLen,
      memAddr, memory, orTrap]
    refine .step (.get rfl) rfl ?_
    simp [sized, Nat.not_lt.mpr inBounds, Prog.bind]
    refine .step (.get rfl) rfl (.step (.get rfl) rfl ?_)
    simp only [storeInt, writeMem, memAddr, memory, orTrap, Prog.bind, pure]
    refine .step (.get rfl) rfl ?_
    simp only [Prog.bind, tagged, payloadOffset]
    refine .step (.modify rfl) rfl (.step (.get rfl) rfl ?_)
    simp only [Prog.bind, payload]
    exact .step (.modify rfl) rfl (.done _)
  · change (writeMemSt address (out + 4) (intToLE 4 handle)
      (writeMemSt address out (intToLE 1 0) config.store)).subtask? subtask = some record
    simpa only [write_subtask] using live

theorem resolve_indirect_range_trap (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
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
    Steps prof ready dispatch config [.tau, .tau, .trap .outOfBounds] (StepDefs.trapCfg config) := by
  have program := lower_result_program (sig := sig) cx cursor maxResults indirect (some handle)
  simp only [Option.elim_some] at program
  rw [program] at focused
  refine .cons (.get focused) ?_
  simp [Prog.bind, FlatCursor.next, atCursor, pure, trapIf, ← aligned, checkInBounds, memLen,
    memAddr, memory, orTrap]
  refine .cons (.get rfl) ?_
  simp [sized, outside, Prog.bind]
  exact .cons (.trap rfl) (.refl _)

theorem resolve_indirect_alignment_trap (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (cursor : FlatCursor) (maxResults : Nat)
    (indirect : maxResults ≤ 1) (pointer : FlatValue)
    (atCursor : cursor.values[cursor.pos]? = some pointer)
    (misaligned : flatNat pointer ≠ ABI.alignTo (flatNat pointer) .four)
    (focused : config.ctl = ⟨thread, .prog (do
        let flat ← lowerFlatValues Limits.spec Quirks.none cx maxResults
          [.variant 0 (some (Val.u32 handle))] [resultType] (some cursor)
        Subtask.resolve subtask .returned flat
        completeResolvedTree ticket tree handle), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .unalignedPointer] (StepDefs.trapCfg config) := by
  have program := lower_result_program (sig := sig) cx cursor maxResults indirect (some handle)
  simp only [Option.elim_some] at program
  rw [program] at focused
  refine .cons (.get focused) ?_
  simp [Prog.bind, FlatCursor.next, atCursor, pure, trapIf, misaligned]
  exact .cons (.trap rfl) (.refl _)

theorem resolve_direct_words (ticket handle : Nat) (tree : Tree sig) (subtask : SubtaskId)
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
        completeResolvedTree ticket tree handle), segments⟩ :: rest } := by
  have lowered (width : AddrType) :
      (lowerFlatTypes Limits.spec Quirks.none cx width
        [.variant 0 (some (Val.u32 handle))] [resultType] : Session grow sig (List FlatValue)) =
        pure [i32Flat 0, i32Flat handle] := by
    simp [lowerFlatTypes, lowerFlatAt, resultType, lowerFlatVariantWith, resultWants, ABI.flattenOption,
      ABI.flatten, ABI.flattenPrimitive, lowerFlatOpt, lowerFlatPrim, Val.u32,
      IntKind.ofPrimitive, coerceLowerSlots, coerceLower, Prog.bind, pure, lowerFlatInt, intKindCore,
      i32Flat, BitVec.ofInt_natCast]
    rfl
  have step := Step.get (prof := prof) (hr := ready) (dispatch := dispatch) focused
  simpa [Prog.bind, resultFlatCount, Nat.not_lt.mpr direct, lowered, pure] using step

private theorem appendSteps {first middle last : Config (core3 grow) (HostState sig)} {leading trailing}
    (lead : Steps prof ready dispatch first leading middle) (tail : Steps prof ready dispatch middle trailing last) :
    Steps prof ready dispatch first (leading ++ trailing) last := by
  induction lead with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem parked_poll_entry (impl : HostImpl (core3 grow) (HostState sig)) (mem : Nat)
    (slot out : FlatValue) (ws : WsetId) (th : ThreadId) (active : Thread) (task : Task (core3 grow))
    (instance_ : InstState) (core : (core3 grow).Thread (CanonHost (core3 grow)))
    (next : List FlatValue → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨some th, .core core next, segments⟩ :: rest)
    (callout : (core3 grow).status config.store.core core =
      .callout (.builtin (.waitableSetPoll mem) task.inst) [slot, out])
    (liveThread : ArenaField.threads.get? config.store th = some active)
    (liveTask : ArenaField.tasks.get? config.store active.task = some task)
    (liveInst : ArenaField.insts.get? config.store task.inst = some instance_)
    (mayLeave : instance_.mayLeave = true) (handle : instance_.handles.get? (flatNat slot) = some (.wset ws)) :
    Steps prof ready (specDispatch ready impl) config (List.replicate 8 .tau)
      { config with ctl := ⟨some th, .prog (wsetPoll ws >>= fun event =>
          unpackEvent (Builtins.eventCx mem task.inst) (flatNat out) event >>= fun code => pure (.flat [i32Flat code])),
        .core core next :: segments⟩ :: rest } := by
  have admitted : calloutEntry config.store (some th) (.builtin (.waitableSetPoll mem) task.inst) = none := by
    simp [calloutEntry, instOfThread?, liveThread, liveTask]
  refine .cons (.coreCallout focused callout) ?_
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, admitted, calloutBody, builtinProg, withArgs2, Builtins.waitableSetPoll, Builtins.enterWaitableBuiltin]
  refine .cons (.currentThread rfl) (.cons (.get rfl) ?_)
  simp [Prog.bind, getTask, getObj, liveThread, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, liveTask, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, liveInst, mayLeave, trapIf, handlesGet, getInst, getObj, pure]
  refine .cons (.get rfl) ?_
  simp [Prog.bind, liveInst, handle, orTrap, Builtins.expectWset, pure, Prog.bind_assoc]
  exact .refl _

theorem poll_delivers_returned (ws : WsetId) (set : WaitableSet) (perm : List Nat)
    (subtask : SubtaskId) (record : Subtask) (index : Nat)
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
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } := by
  have hasEvent : config.store.wsetHasEvent ws = true := by
    rw [CStore.wsetHasEvent, setLive]
    exact List.any_eq_true.mpr ⟨.subtask subtask, member, by simp [CStore.waitableHasEvent, live, eventPending]⟩
  let shuffled := { config with
    store := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    ctl := ⟨thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= resume), segments⟩ :: rest }
  have selected := poll_selects (prof := prof) (ready := ready) (dispatch := dispatch)
    ws set perm (.subtask subtask) setLive hasEvent allowed selects resume focused
  exact appendSteps selected
    (deliver_pending (config := shuffled) subtask record index live returned indexed eventPending resume rfl)

theorem get_delivers_returned (ws : WsetId) (set : WaitableSet) (perm : List Nat)
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
        ctl := ⟨thread, .prog (resume ⟨.subtask, index, SubtaskState.returned.toNat⟩), segments⟩ :: rest } := by
  let shuffled := { config with
    store := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
    ctl := ⟨thread, .prog (Waitable.getPendingEvent (.subtask subtask) >>= resume), segments⟩ :: rest }
  exact appendSteps (get_selects ws set perm (.subtask subtask) setLive allowed selects resume focused)
    (deliver_pending (config := shuffled) subtask record index live returned indexed eventPending resume rfl)

theorem unpack_event_write (cx : LiftLowerContext (core3 grow)) (ptr address size : Nat) (event : EventTuple)
    (aligned : ptr % 4 = 0) (memory : cx.opts.memory = some address)
    (sized : (core3 grow).memSize? config.store.core address = some size) (inBounds : ptr + 8 ≤ size)
    (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    let indexed := writeMemSt address ptr (u32Bytes event.index) config.store
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau]
      { config with
        store := writeMemSt address (ptr + 4) (u32Bytes event.payload) indexed
        ctl := ⟨thread, .prog (resume event.code.toNat), segments⟩ :: rest } := by
  have indexWrite : ((core3 grow).memWrite? config.store.core address ptr (u32Bytes event.index)).isSome := by
    apply Core3.memWrite?_isSome_iff.2
    exact ⟨size, sized, by change ptr + 4 ≤ size; omega⟩
  obtain ⟨indexCore, wroteIndex⟩ := Option.isSome_iff_exists.mp indexWrite
  have indexSize : (core3 grow).memSize? (writeMemSt address ptr (u32Bytes event.index) config.store).core address = some size := by
    simp only [writeMemSt, wroteIndex]
    exact (Core3.memWrite?_memSize wroteIndex address).trans sized
  have payloadWrite : ((core3 grow).memWrite? (writeMemSt address ptr (u32Bytes event.index) config.store).core
      address (ptr + 4) (u32Bytes event.payload)).isSome := by
    apply Core3.memWrite?_isSome_iff.2
    exact ⟨size, indexSize, by change ptr + 4 + 4 ≤ size; omega⟩
  obtain ⟨payloadCore, wrotePayload⟩ := Option.isSome_iff_exists.mp payloadWrite
  simp [unpackEvent, checkAligned, aligned, Prog.bind, pure, trapIf, checkInBounds, memLen, memAddr, memory, orTrap] at focused
  refine .cons (.get focused) ?_
  simp [sized, Nat.not_lt.mpr inBounds, Prog.bind, writeMem, memAddr, memory, orTrap, pure]
  refine .cons (.get rfl) ?_
  simp only [Prog.bind, wroteIndex]
  refine .cons (.modify rfl) (.cons (.get rfl) ?_)
  simp only [Prog.bind, wrotePayload]
  exact .cons (.modify rfl) (.refl _)

theorem unpack_event_bad_alignment (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (event : EventTuple)
    (misaligned : ptr % 4 ≠ 0) (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.trap .unalignedPointer] (StepDefs.trapCfg config) := by
  simp [unpackEvent, checkAligned, misaligned, trapIf, pure] at focused
  exact .cons (.trap focused) (.refl _)

theorem unpack_event_bad_range (cx : LiftLowerContext (core3 grow)) (ptr address size : Nat) (event : EventTuple)
    (aligned : ptr % 4 = 0) (memory : cx.opts.memory = some address)
    (sized : (core3 grow).memSize? config.store.core address = some size) (outside : size < ptr + 8)
    (resume : Nat → Session grow sig (Ret (core3 grow)))
    (focused : config.ctl = ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .outOfBounds] (StepDefs.trapCfg config) := by
  simp [unpackEvent, checkAligned, aligned, Prog.bind, pure, trapIf, checkInBounds, memLen, memAddr, memory, orTrap] at focused
  refine .cons (.get focused) ?_
  simp [sized, outside, Prog.bind]
  exact .cons (.trap rfl) (.refl _)

private theorem lenders_core (store : CStore (core3 grow)) (lenders : List HandleObjId) :
    (lenders.foldl (fun acc handle => ArenaField.resHandles.modify acc handle fun entry =>
      { entry with numLends := entry.numLends - 1 }) store).core = store.core := by
  induction lenders generalizing store with
  | nil => rfl
  | cons handle lenders ih => exact ih (ArenaField.resHandles.modify store handle _)

private theorem delivered_core (store : CStore (core3 grow)) (subtask : SubtaskId) :
    (store.deliverResolveSt subtask).core = store.core := by
  unfold CStore.deliverResolveSt
  split
  · rfl
  · exact lenders_core store _

theorem poll_returned_bad_range (ws : WsetId) (set : WaitableSet) (perm : List Nat)
    (subtask : SubtaskId) (record : Subtask) (index : Nat)
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
      { config with store := StepDefs.lockdownSt delivered, ctl := [] } := by
  let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
  let delivered := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
    |>.deliverResolveSt subtask
  let event : EventTuple := ⟨.subtask, index, SubtaskState.returned.toNat⟩
  let reached := { config with
    store := delivered
    ctl := ⟨thread, .prog (unpackEvent cx ptr event >>= resume), segments⟩ :: rest }
  have sameCore : reached.store.core = config.store.core :=
    delivered_core (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }) subtask
  have poll := poll_delivers_returned (prof := prof) (ready := ready) (dispatch := dispatch)
    ws set perm subtask record index setLive member allowed selects live returned indexed eventPending _ focused
  exact appendSteps poll (unpack_event_bad_range (config := reached) cx ptr address size event aligned memory
    (by rw [sameCore]; exact sized) outside resume rfl)

theorem resolve_linked_commit (callee : Callee sig) (ticket : Nat) (caller : CallerId)
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
    (∀ saved, ParkedPrefix prof ready dispatch saved config (List.replicate (16 + record.index.isSome.toNat) .tau) final) ∧
      final.store.subtask? subtask = some { record with
        state := .returned
        flatResults := []
        common := if record.index.isSome then { record.common with pending := some (.subtask subtask) }
          else record.common } := by
  let handle := writer.accepted.length
  let queued := if record.index.isSome then config.store.setPendingSt (.subtask subtask) (.subtask subtask)
    else config.store
  let progressed := { record with common := if record.index.isSome then
    { record.common with pending := some (.subtask subtask) } else record.common }
  have memory : cx.opts.memory = some callee.memory := by rw [context]; rfl
  have spill : (lowerLimits callee.async_).2 ≤ 1 := by cases callee.async_ <;> decide
  have queuedSize : (core3 grow).memSize? queued.core callee.memory = some size := by
    unfold queued
    split <;> exact sized
  let callReady : Config (core3 grow) (HostState sig) := { config with ctl := ⟨thread, .prog (do
    lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Val.u32 handle))])
    completeResolvedTree ticket tree handle), segments⟩ :: rest }
  let resultReady : Config (core3 grow) (HostState sig) := { config with
    store := queued
    ctl := ⟨thread, .prog (do
      let flat ← lowerFlatValues Limits.spec Quirks.none cx (lowerLimits callee.async_).2
        [.variant 0 (some (Val.u32 handle))] [resultType] (some ⟨args, pos⟩)
      Subtask.resolve subtask .returned flat
      completeResolvedTree ticket tree handle), segments⟩ :: rest }
  have beginRun : Step prof ready dispatch config .tau callReady := resolve_begin ticket caller tree writer registered room focused
  have progress := resolve_progress (prof := prof) (ready := ready) (dispatch := dispatch) (config := callReady)
    ticket handle caller tree subtask cx args pos callee.funcType _ _ record callerRecord live rfl
  have write := resolve_indirect_write (prof := prof) (ready := ready) (dispatch := dispatch) (config := resultReady)
    ticket handle tree subtask cx ⟨args, pos⟩ _ spill pointer callee.memory atCursor aligned memory size
    queuedSize inBounds progressed progress.2 rfl
  have commit := resolve_commit (prof := prof) (ready := ready) (dispatch := dispatch)
    ticket handle tree writer subtask [] progressed write.2 registered rfl room rfl
  refine ⟨?_, commit.2⟩
  intro saved
  have kept : (transitionEdit config (.tau : Label (core3 grow) (HostState sig))).follow (.saved saved.idx 0) =
      some (.saved saved.idx 0) := by
    rw [transitionEdit, focused]
    rfl
  have run := ParkedPrefix.step beginRun kept (parkAppend (progress.1 saved) (parkAppend (write.1 saved) (commit.1 saved)))
  cases indexed : record.index <;> simpa [resultReady, queued, handle, indexed] using run

theorem parked_poll_returned (impl : HostImpl (core3 grow) (HostState sig)) (mem : Nat)
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
        (deliveredLabels ++ [.tau, .trap .outOfBounds]) { config with store := StepDefs.lockdownSt delivered, ctl := [] })) := by
  let shuffled := config.store.wsetSetElemsSt ws (applyPerm perm set.elems)
  let delivered := (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none })
    |>.deliverResolveSt subtask
  let event : EventTuple := ⟨.subtask, index, SubtaskState.returned.toNat⟩
  let cx : LiftLowerContext (core3 grow) := Builtins.eventCx mem task.inst
  let reply : Nat → Session grow sig (Ret (core3 grow)) := fun code => pure (.flat [i32Flat code])
  let entered := { config with ctl := ⟨some th, .prog (wsetPoll ws >>= fun event => unpackEvent cx (flatNat out) event >>= reply),
    .core core next :: segments⟩ :: rest }
  let reached := { config with
    store := delivered
    ctl := ⟨some th, .prog (unpackEvent cx (flatNat out) event >>= reply), .core core next :: segments⟩ :: rest }
  have enter := parked_poll_entry (prof := prof) (ready := ready) impl mem slot out ws th active task instance_ core next
    focused callout liveThread liveTask liveInst mayLeave handle
  have poll := poll_delivers_returned (prof := prof) (ready := ready) (dispatch := specDispatch ready impl)
    (config := entered) ws set perm subtask record index setLive member allowed selects live returned indexed eventPending
    (fun event => unpackEvent cx (flatNat out) event >>= reply) rfl
  have run := appendSteps enter poll
  have sameCore : reached.store.core = config.store.core :=
    delivered_core (shuffled.modifyWaitableCommon (.subtask subtask) fun common => { common with pending := none }) subtask
  refine ⟨?_, ?_⟩
  · intro misaligned
    exact appendSteps run (unpack_event_bad_alignment (config := reached) cx (flatNat out) event misaligned reply rfl)
  · intro size aligned sized
    have reachedSize : (core3 grow).memSize? reached.store.core mem = some size := by rw [sameCore]; exact sized
    constructor
    · intro inBounds
      have write := unpack_event_write (prof := prof) (ready := ready) (dispatch := specDispatch ready impl)
        (config := reached) cx (flatNat out) mem size event aligned rfl reachedSize inBounds reply rfl
      exact appendSteps run (appendSteps write (.cons (.popCore rfl) (.refl _)))
    · intro outside
      exact appendSteps run (unpack_event_bad_range (config := reached) cx (flatNat out) mem size event
        aligned rfl reachedSize outside reply rfl)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ComponentResult
