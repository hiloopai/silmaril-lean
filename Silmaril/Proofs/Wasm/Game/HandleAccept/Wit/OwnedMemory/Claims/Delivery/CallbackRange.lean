module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}

theorem collectionRange (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {start canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start checkEntry first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
    (core3 grow).memAddrType? start.store.core destination.memory = some destination.width →
    Core3.Grows start.store.core checked.store.core →
    CollectionRangeCut profile ready base bindings older checked canonical cursor destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
      (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) := by
  intro area mode first second marked paired returning present growth
  obtain ⟨place, origin, trail⟩ := marked.canonicalTrail.survives
  cases origin
  have canonicalTop : segmentAt (segmentStorage canonical) (.active 0 0) = some (.prog second) :=
    (prefix_survives trail).2.trans rfl
  obtain ⟨canonCursor, frame, canonicalAt⟩ := LinkedCallback.marked_pop_frame paired marked.outside returning canonicalTop
  have width : (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width := growth.memAddrType present
  have hasSize : ((core3 grow).memSize? checked.store.core destination.memory).isSome := by
    apply Core3.memAddrType?_isSome_iff.mp
    change ((core3 grow).memAddrType? checked.store.core destination.memory).isSome = true
    rw [width]
    rfl
  obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp hasSize
  have returned : canonical.ctl = ⟨cursor.thread, .prog (.pure (.nat pointer)),
      .prog second :: canonCursor.frames⟩ :: canonCursor.rest := by
    simpa only [PayloadPrefix.Cursor.control, ← frame.thread] using canonicalAt
  refine ⟨canonCursor, bytes, width, sized, frame, ?_⟩
  have validated := destination.paired_range_recheck (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    paired inst area entries.length pointer (Field.listObjects entries)
    (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
    (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext)
    rfl rfl returning returned sized (specDispatch ready (LiveDispatch.host bindings base))
  simpa only [PayloadPrefix.Cursor.control, ← frame.thread] using validated

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
