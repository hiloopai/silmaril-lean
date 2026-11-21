module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
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
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open ComponentCall.Delivery.FiniteSession

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

private theorem silent {labels : Trace grow sig} (tau : ∀ label ∈ labels, label = .tau) : visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    have head := tau label (by simp)
    have tail := ih (fun other member => tau other (List.mem_cons_of_mem _ member))
    subst label
    exact tail

private theorem appendRun {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch start leading middle) (back : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

theorem localData (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (matched : Field.EntriesMatch entries element) (data : LocalDataType element)
    (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)} :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr >>= canonNext
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionReturn profile ready base bindings older checked canonical check checkNext canonNext (rhs pointer) := by
  intro area lhs rhs cut
  obtain ⟨canon, bytes, width, sized, frame, range⟩ := cut
  have trapped (reason : TrapReason)
      (checkRun : ∃ steps, Steps profile ready (specDispatch ready base) checked
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked))
      (canonRun : ∃ steps, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical)) :
      CollectionReturn profile ready base bindings older checked canonical check checkNext canonNext (rhs pointer) := by
    obtain ⟨leftCount, left⟩ := checkRun
    obtain ⟨rightCount, right⟩ := canonRun
    have seen (count : Nat) : visible (List.replicate count (.tau : Label (core3 grow) (HostState sig)) ++ [.trap reason]) =
        [.trap reason] := by
      rw [show visible (List.replicate count .tau ++ [.trap reason] : Trace grow sig) =
        visible (List.replicate count .tau) ++ visible [.trap reason] from List.filter_append ..,
        silent (labels := List.replicate count .tau)
        (fun _ member => List.eq_of_mem_replicate member)]
      rfl
    exact ⟨canon, .trapped reason, _, _, _, _, left, right,
      congrArg StepDefs.lockdownSt frame.store, (seen leftCount).trans (seen rightCount).symm, rfl, rfl, [], seen rightCount⟩
  by_cases aligned : pointer = alignTo pointer area.alignment
  · simp only [ite_eq_right (not_not_intro aligned)] at range
    by_cases bounds : pointer + entries.length * area.size ≤ bytes
    · simp only [ite_eq_left bounds] at range
      obtain ⟨⟨leading, checkTau, checkRun⟩, ⟨referenceLabels, canonTau, canonRun⟩⟩ := range
      let other := { canonical with ctl := canon.control (rhs pointer) }
      have prefixSeen : visible leading = visible referenceLabels := (silent checkTau).trans (silent canonTau).symm
      cases prepared : Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) with
      | error issue =>
        rw [prepared] at checkRun
        let refused := LinkedCallback.CollectionVisit.afterAllocation index issue
        have stop : lhs pointer (.error issue) = checkNext (.error refused) := by cases issue <;> rfl
        rw [stop] at checkRun
        exact ⟨canon, .refused refused, _, _, _, other, (prefix_survives (checkRun 0)).1,
          (prefix_survives (canonRun 0)).1, frame.store, prefixSeen, rfl, rfl, checkRun, canonRun⟩
      | ok result =>
        cases result
        rw [prepared] at checkRun
        let entered := { checked with ctl := check.control (lhs pointer (.ok ())) }
        obtain ⟨store, outcome, checkedTail, canonTail, checkedRun, canonicalRun, seen, result⟩ :=
          local_data_collection_tail (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
            (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst element data entries matched
            pointer bytes index output entered other width sized aligned bounds frame.store check canon frame.thread
            checkNext canonNext rfl rfl
        have left := appendRun (prefix_survives (checkRun 0)).1 checkedRun
        have right := appendRun (prefix_survives (canonRun 0)).1 canonicalRun.steps
        have labels : visible (leading ++ checkedTail) = visible (referenceLabels ++ canonTail) := by
          simp only [visible, List.filter_append] at prefixSeen seen ⊢
          rw [prefixSeen, seen]
        cases outcome with
        | ok value =>
          exact ⟨canon, .returned value, _, _, _, _, left, right, rfl, labels,
            ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩,
            rfl, rfl, fun depth => (checkRun depth).append (result.2.1 depth),
            fun depth => (canonRun depth).append (result.2.2 depth)⟩
        | error reason =>
          obtain ⟨before, tail⟩ := result
          exact ⟨canon, .trapped reason, _, _, _, _, left, right, rfl, labels, rfl, rfl, visible referenceLabels ++ before,
            by simp only [visible, List.filter_append] at tail ⊢; rw [tail, List.append_assoc]⟩
    · simp only [ite_eq_right bounds] at range
      exact trapped .outOfBounds range.1 range.2
  · simp only [ite_eq_left aligned] at range
    exact trapped .unalignedPointer range.1 range.2

theorem replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {callerLabels childEntry}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) callerLabels checked (.active 0 1))
    (cut : CollectionReturn profile ready base bindings older checked canonical check site.reply site.referenceReply childEntry) :
    CollectionReplies profile ready base bindings older site checked canonical childEntry := by
  obtain ⟨canon, outcome, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩ := cut
  have silentTail (trace suffix : Trace grow sig) (tau : visible suffix = []) : visible (trace ++ suffix) = visible trace := by
    change List.filter _ (trace ++ suffix) = _
    rw [List.filter_append]
    change visible trace ++ visible suffix = _
    rw [tau, List.append_nil]
  cases outcome with
  | trapped reason => exact ⟨.trapped reason, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩
  | returned value =>
    obtain ⟨frame, checkAt, canonAt, tracks, _⟩ := result
    obtain ⟨checkEnd, canonEnd, checkReply, canonReply, stores, checkHost, canonHost, paired⟩ :=
      LinkedCallback.MemorySequence.resume_returned_give site value frame (caller.append (tracks 0)) checkAt canonAt
    exact ⟨.returned value, _, _, checkEnd, canonEnd, appendRun checkedRun (checkReply _), appendRun canonRun (canonReply _),
      stores, by rw [silentTail _ _ rfl, silentTail _ _ rfl, seen], left, right, checkReply, canonReply, checkHost, canonHost, paired⟩
  | refused issue =>
    obtain ⟨checkAt, canonAt, tracks, _⟩ := result
    obtain ⟨segments, callerAt⟩ := site.reached_caller checkAt (caller.append (tracks 0))
    let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
    have atReply : left.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
      simpa only [Cursor.control, callerAt, PayloadRoot.Site.reply, reply] using checkAt
    let finished := { left with
      host := left.host.record reply.1
      ctl := ⟨check.thread, .core ((core3 grow).resume left.store.core site.core (.values reply.2)) site.resume, segments⟩ :: check.rest }
    have resumes (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
        Steps profile ready dispatch left [.tau, .tau, .tau] finished := Plain.give_completion_steps reply atReply
    exact ⟨.refused issue, _, rhs, finished, right, appendRun checkedRun (resumes _), canonRun, same,
      by rw [silentTail _ _ rfl, seen], left, canon, rfl, resumes, canonAt⟩

private theorem listEntries {entries : List Field} {element schema : Stored.TypeOf}
    (matched : Field.LayoutMatches (.dynamic (.list element) element entries) schema) : Field.EntriesMatch entries element := by
  cases matched with
  | list children => exact children

theorem refusalReply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (index pointer bytes : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {leading issue} :
    let area := layout site.destination.width element
    let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer
      (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply
    let reply := route.reply site.destination site.start.host.nextTicket
      (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
    CollectionRangeCut profile ready base bindings older checked canonical check site.destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr live => checkedCollectionTail site.destination site.inst entries area index route.output addr live >>= site.reply)
      (fun addr => canonicalCollectionTail site.destination site.inst entries area route.output addr
        (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply) →
    Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1) →
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
    ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (checkedLabels canonLabels : Trace grow sig)
      (segments : List (Seg (core3 grow) (HostState sig))),
      (∀ label ∈ checkedLabels, label = .tau) ∧ (∀ label ∈ canonLabels, label = .tau) ∧
      Steps profile ready (specDispatch ready base) checked (checkedLabels ++ [.tau, .tau, .tau])
        { checked with
          host := checked.host.record reply.1
          ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
            segments⟩ :: check.rest } ∧
      RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels
        { canonical with ctl := canon.control child } := by
  intro area child reply cut caller sized aligned bounds refused
  obtain ⟨canon, capacity, _, atCapacity, _, reached⟩ := cut
  have sameCapacity := Option.some.inj (atCapacity.symm.trans sized)
  subst capacity
  simp only [ite_eq_right (not_not_intro aligned), ite_eq_left bounds] at reached
  obtain ⟨⟨lhs, checkTau, checkedRun⟩, ⟨rhs, canonTau, canonRun⟩⟩ := reached
  rw [refused] at checkedRun
  let stopped := site.reply (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
  have stop : (checkedCollectionTail site.destination site.inst entries area index route.output pointer (.error issue) >>= site.reply) =
      stopped := by cases issue <;> rfl
  rw [stop] at checkedRun
  let reached := { checked with ctl := check.control stopped }
  obtain ⟨segments, atCaller⟩ := site.reached_caller (reached := reached) (body := stopped) rfl (caller.append (checkedRun 0))
  have atReply : reached.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
    simp only [reached, Cursor.control, atCaller, stopped, PayloadRoot.Site.reply, reply]
  exact ⟨canon, lhs, rhs, segments, checkTau, canonTau,
    appendRun (prefix_survives (checkedRun 0)).1 (Plain.give_completion_steps reply atReply), canonRun⟩

theorem localListReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (data : LocalDataType element)
    (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (canonicalCollectionTail site.destination site.inst entries area route.output pointer >>= site.referenceReply) := by
  intro area first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Stored.OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ objects compiled
  rw [field] at matched
  have children := listEntries matched
  have width := site.destination.check_width site.start.store linked.destination
  have prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer
      (Field.listObjects entries) = .ok () := by rw [local_data_objects data children]; rfl
  have checkAt : site.checked.ctl = site.cursor.control (Stored.OwnedMemory.Claims.Record.Effects.field
      recordClaims Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
      (.dynamic (.list element) element entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have canonAt := site.reference_at linked site.referenceReply
  rw [field] at canonAt
  have entered := (collection_install_tracks (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    site.destination site.inst (.list element) element entries route.output 0 site.checked (site.reference site.referenceReply)
    site.cursor site.cursor site.reply site.referenceReply width prepared checkAt canonAt 0).1
  obtain ⟨place, initial, track⟩ := mark.checkedTrail.survives
  cases initial
  have below := track.under 1
  have caller := entered.append below
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.list element) element
    entries route.output 0 pointer site.reply site.referenceReply mark paired returned width growth
  exact replies site caller (localData site.destination site.inst element entries children data route.output 0 pointer
    site.reply site.referenceReply cut)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
