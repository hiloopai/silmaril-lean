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
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
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

private theorem appendVisible (first second : Trace grow sig) :
    visible (first ++ second) = visible first ++ visible second := List.filter_append ..

private theorem leafSilent {Result : Type} {value : Result} {labels : Trace grow sig}
    (quiet : LocalLeafLabels (.ok value) labels) : visible labels = [] := by
  apply silent
  intro label member
  have tau := List.all_eq_true.mp quiet label member
  cases label <;> simp_all

private theorem leafTrap {Result : Type} {reason : TrapReason} {labels : Trace grow sig}
    (traps : LocalLeafLabels (Result := Result) (.error reason) labels) : visible labels = [.trap reason] := by
  obtain ⟨count, rfl⟩ := traps
  rw [appendVisible, silent (fun _ member => List.eq_of_mem_replicate member)]
  rfl

private theorem nominalElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (nominal : ∀ item ∈ entries, CanonicalHandle item) (stride ptr index : Nat)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (checkAt : left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries stride ptr index >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries .value stride ptr >>= canonNext)) :
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (ElementStop destination inst entries stride ptr canonNext) := by
  induction entries generalizing ptr index left right check canon with
  | nil =>
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨canon, .returned (), [], [], left, right, .refl _, .refl _, frame.store, rfl,
      frame, checkAt, canonAt, fun depth => .done _ _, fun depth => .done _ _, trivial⟩
  | cons item rest ih =>
    let checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
      (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width rest stride (ptr + stride) (index + 1)) >>= checkNext
    let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ =>
      CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width rest .value stride (ptr + stride) >>= canonNext
    have atHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width item index (.memory ptr) >>= checkTail) := by
      rw [checkAt, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checkTail]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok value => cases value; rfl
    have atCanonHead : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item (.memory ptr) >>= canonTail) := by
      rw [canonAt, CanonicalTree.elements]
      congr 1
      change Prog.bind (Prog.bind _ (fun _ => _)) canonNext = Prog.bind _ canonTail
      exact Prog.bind_assoc _ _ _
    have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
      (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst item (nominal item (by simp))
      index (.memory ptr) checkTail canonTail frame (Core3.Grows.refl _) atHead atCanonHead
      (next := fun _ lhs rhs check canon => CollectionSegment profile ready base bindings older lhs rhs check checkNext canonNext 0
        (ElementStop destination inst rest stride (ptr + stride) canonNext))
      (fun _ reached reference _ _ related _ lhs rhs => ih (fun child member => nominal child (List.mem_cons_of_mem _ member))
        (ptr + stride) (index + 1) related (by exact lhs) (by exact rhs))
    unfold LinkedCallback.HandleFieldThenBetween at leaf
    cases live : liveLeafPlan left.store left.host.writer index item with
    | error issue =>
      rw [live] at leaf
      obtain ⟨labels, tau, tracks⟩ := leaf
      exact ⟨canon, .refused issue, labels, [], _, right, (prefix_survives (tracks 0)).1, .refl _,
        frame.store, silent tau, _, ⟨[], item :: rest, rfl, by simp, by simp⟩, rfl, canonAt, tracks, fun depth => .done _ _⟩
    | ok plan =>
      rw [live] at leaf
      obtain ⟨store, result, initial, leftLabels, rightLabels, quiet, seenLeft, seenRight, runLeft, runRight, success⟩ := leaf
      cases result with
      | error reason =>
        have seen := leafTrap seenRight
        exact ⟨canon, .trapped reason, _, _, _, _, runLeft, runRight, rfl,
          by rw [appendVisible, silent quiet, List.nil_append, leafTrap seenLeft, seen], rfl, rfl, [], seen⟩
      | ok value =>
        cases value
        obtain ⟨leftTracks, rightTracks, next⟩ := success () rfl
        obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, tailLeft, tailRight, same, seen, status⟩ := next
        have leftRun := appendRun runLeft tailLeft
        have rightRun := appendRun runRight tailRight
        have observed : visible ((initial ++ leftLabels) ++ lhs) = visible (rightLabels ++ rhs) := by
          rw [appendVisible, appendVisible, appendVisible, silent quiet, leafSilent seenLeft, leafSilent seenRight,
            List.nil_append, List.nil_append, List.nil_append, seen]
        refine ⟨reached, outcome, _, _, finalLeft, finalRight, leftRun, rightRun, same, observed, ?_⟩
        cases outcome with
        | returned value =>
          obtain ⟨paired, leftAt, rightAt, leftTail, rightTail, kept⟩ := status
          exact ⟨paired, leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth),
            fun depth => (rightTracks depth).append (rightTail depth), kept⟩
        | refused issue =>
          obtain ⟨stop, ⟨leading, remaining, split, nonempty, stopAt⟩, leftAt, rightAt, leftTail, rightTail⟩ := status
          refine ⟨stop, ⟨item :: leading, remaining, congrArg (item :: ·) split, nonempty, ?_⟩, leftAt, rightAt,
            fun depth => (leftTracks depth).append (leftTail depth), fun depth => (rightTracks depth).append (rightTail depth)⟩
          simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm stride] using stopAt
        | trapped reason =>
          obtain ⟨leftEmpty, rightEmpty, before, trapped⟩ := status
          exact ⟨leftEmpty, rightEmpty, before, by rw [appendVisible, leafSilent seenRight, List.nil_append, trapped]⟩

private theorem finishElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (mode : CanonicalTree.EntryMode) (output : Stored.Lower.Output) (index ptr : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkAt : left.ctl = check.control (checkedCollectionTail destination inst entries area index output ptr (.ok ()) >>= checkNext))
    (canonAt : right.ctl = canon.control (canonicalCollectionTail destination inst entries area output ptr mode >>= canonNext))
    (stopsAt : (Unit → Session grow sig (Ret (core3 grow))) → Session grow sig (Ret (core3 grow)) → Prop)
    (visit : ∀ (checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
        (canonTail : Unit → Session grow sig (Ret (core3 grow))),
      left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width entries area.size ptr 0 >>= checkTail) →
      right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
        (destination.context inst) destination.width entries mode area.size ptr >>= canonTail) →
      CollectionSegment profile ready base bindings older left right check checkTail canonTail 0 (stopsAt canonTail)) :
    let publish := (ListLower.publish (destination.context inst) destination.width ptr entries.length output : Session grow sig output.Result)
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (stopsAt (fun _ => publish >>= canonNext)) := by
  intro publish
  let onChecked : output.Result → Session grow sig (Ret (core3 grow)) := fun result => checkNext (.ok result)
  let checkTail := checkedSequenceNext (.nested index) (fun (_ : Unit) => publish >>= fun result => pure (.ok result)) checkNext
  let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ => publish >>= canonNext
  have checkElements : left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries area.size ptr 0 >>= checkTail) := by
    rw [checkAt]
    congr 1
    simp only [checkedCollectionTail, Prog.bind_eq, Prog.bind_assoc, checkTail, publish]
    congr 1
    funext verdict
    cases verdict with
    | error _ => rfl
    | ok value => cases value; rfl
  have canonElements : right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries mode area.size ptr >>= canonTail) := by
    rw [canonAt]
    congr 1
    change Prog.bind (Prog.bind _ (fun _ => publish)) canonNext = Prog.bind _ canonTail
    exact Prog.bind_assoc _ _ _
  obtain ⟨reached, outcome, lhs, rhs, middleLeft, middleRight, runLeft, runRight, same, seen, status⟩ :=
    visit checkTail canonTail checkElements canonElements
  cases outcome with
  | trapped reason => exact ⟨reached, .trapped reason, lhs, rhs, _, _, runLeft, runRight, same, seen, status⟩
  | refused issue =>
    obtain ⟨stop, witness, leftAt, rightAt, tracksLeft, tracksRight⟩ := status
    exact ⟨reached, .refused (.nested index issue), lhs, rhs, _, _, runLeft, runRight, same, seen,
      stop, witness, leftAt, rightAt, tracksLeft, tracksRight⟩
  | returned value =>
    cases value
    obtain ⟨paired, leftAt, rightAt, tracksLeft, tracksRight, _⟩ := status
    have leftPublish : middleLeft.ctl = check.control (publish >>= onChecked) := by
      rw [leftAt]
      simp only [checkTail, checkedSequenceNext, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', onChecked]
    obtain ⟨store, result, labels, observed, leftWrites, rightWrites, tracks⟩ :=
      collection_descriptor_cut_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
        (reference := specDispatch ready (LiveDispatch.host bindings base)) (destination.context inst) destination.width
        output ptr entries.length middleLeft middleRight check reached onChecked canonNext same leftPublish rightAt
    have labelMatch : visible (lhs ++ labels) = visible (rhs ++ labels) := by rw [appendVisible, appendVisible, seen]
    have leftRun := appendRun runLeft leftWrites.steps
    have rightRun := appendRun runRight rightWrites.steps
    cases result with
    | error reason =>
      exact ⟨reached, .trapped reason, _, _, _, _, leftRun, rightRun, rfl, labelMatch, rfl, rfl, visible rhs,
        by rw [appendVisible, leafTrap observed]⟩
    | ok descriptor =>
      exact ⟨reached, .returned descriptor, _, _, _, _, leftRun, rightRun, rfl, labelMatch,
        ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩,
        rfl, rfl, fun depth => (tracksLeft depth).append (tracks descriptor rfl depth).1,
        fun depth => (tracksRight depth).append (tracks descriptor rfl depth).2, trivial⟩

private theorem rangeThen (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (mode : CanonicalTree.EntryMode)
    (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext
    stopsAt (rhs pointer) →
    (∀ bytes (left right : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig)),
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
      LinkedCallback.ChildFrameOver older left right check canon →
      left.ctl = check.control (lhs pointer (.ok ())) → right.ctl = canon.control (rhs pointer) →
      CollectionSegment profile ready base bindings older left right check checkNext canonNext 0 stopsAt) →
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 stopsAt := by
  intro area lhs rhs acceptsInitial visit cut
  obtain ⟨canon, bytes, width, sized, frame, range⟩ := cut
  have trapped (reason : TrapReason)
      (checkRun : ∃ steps, Steps profile ready (specDispatch ready base) checked
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked))
      (canonRun : ∃ steps, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical)) :
      CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 stopsAt := by
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
          (prefix_survives (canonRun 0)).1, frame.store, prefixSeen, rhs pointer, acceptsInitial, rfl, rfl, checkRun, canonRun⟩
      | ok result =>
        cases result
        rw [prepared] at checkRun
        let entered := { checked with ctl := check.control (lhs pointer (.ok ())) }
        have child : LinkedCallback.ChildFrameOver older entered other check canon :=
          ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        obtain ⟨reached, outcome, checkedTail, canonTail, leftEnd, rightEnd, checkedRun, canonicalRun, same, seen, result⟩ :=
          visit bytes entered other canon width sized aligned bounds child rfl rfl
        have left := appendRun (prefix_survives (checkRun 0)).1 checkedRun
        have right := appendRun (prefix_survives (canonRun 0)).1 canonicalRun
        have labels : visible (leading ++ checkedTail) = visible (referenceLabels ++ canonTail) := by
          simp only [visible, List.filter_append] at prefixSeen seen ⊢
          rw [prefixSeen, seen]
        refine ⟨reached, outcome, _, _, leftEnd, rightEnd, left, right, same, labels, ?_⟩
        cases outcome with
        | returned value =>
          obtain ⟨paired, leftAt, rightAt, leftTail, rightTail, kept⟩ := result
          exact ⟨paired, leftAt, rightAt, fun depth => (checkRun depth).append (leftTail depth),
            fun depth => (canonRun depth).append (rightTail depth), kept⟩
        | refused issue =>
          obtain ⟨stop, accepted, leftAt, rightAt, leftTail, rightTail⟩ := result
          exact ⟨stop, accepted, leftAt, rightAt, fun depth => (checkRun depth).append (leftTail depth),
            fun depth => (canonRun depth).append (rightTail depth)⟩
        | trapped reason =>
          obtain ⟨leftDone, rightDone, before, tail⟩ := result
          exact ⟨leftDone, rightDone, visible referenceLabels ++ before,
            by simp only [visible, List.filter_append] at tail ⊢; rw [tail, List.append_assoc]⟩
    · simp only [ite_eq_right bounds] at range
      exact trapped .outOfBounds range.1 range.2
  · simp only [ite_eq_left aligned] at range
    exact trapped .unalignedPointer range.1 range.2

private theorem localTail (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (mode : CanonicalTree.EntryMode) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)} :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext
    (∀ bytes (left right : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig)),
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
      left.store = right.store → check.thread = canon.thread → left.ctl = check.control (lhs pointer (.ok ())) →
      right.ctl = canon.control (rhs pointer) →
      LocalCutKeepingBetween profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
        (fun store => Core3.Grows left.store.core store.core) left right check canon (fun value => checkNext (.ok value)) canonNext) →
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionReturn profile ready base bindings older checked canonical check checkNext canonNext (rhs pointer) := by
  intro area lhs rhs visit cut
  refine rangeThen destination inst element entries mode output index pointer checkNext canonNext _ rfl ?_ cut
  intro bytes left right canon width sized aligned bounds frame checkAt canonAt
  obtain ⟨store, outcome, checkedTail, canonTail, checkedRun, canonicalRun, seen, result⟩ :=
    visit bytes left right canon width sized aligned bounds frame.store frame.thread checkAt canonAt
  cases outcome with
  | ok value =>
    exact ⟨canon, .returned value, _, _, _, _, checkedRun, canonicalRun.steps, rfl, seen,
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩,
      rfl, rfl, result.2.1, result.2.2, trivial⟩
  | error reason =>
    exact ⟨canon, .trapped reason, _, _, _, _, checkedRun, canonicalRun.steps, rfl, seen, rfl, rfl, result⟩

theorem replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {callerLabels stopsAt}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) callerLabels checked (.active 0 1))
    (cut : CollectionSegment profile ready base bindings older checked canonical check site.reply site.referenceReply 1 stopsAt) :
    CollectionSegmentReplies profile ready base bindings older site checked canonical stopsAt := by
  obtain ⟨canon, outcome, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩ := cut
  have silentTail (trace suffix : Trace grow sig) (tau : visible suffix = []) : visible (trace ++ suffix) = visible trace := by
    change List.filter _ (trace ++ suffix) = _
    rw [List.filter_append]
    change visible trace ++ visible suffix = _
    rw [tau, List.append_nil]
  cases outcome with
  | trapped reason => exact ⟨.trapped reason, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩
  | returned value =>
    obtain ⟨frame, checkAt, canonAt, tracks, _, _⟩ := result
    obtain ⟨checkEnd, canonEnd, checkReply, canonReply, stores, checkHost, canonHost, paired⟩ :=
      LinkedCallback.MemorySequence.resume_returned_give site value frame (caller.append (tracks 0)) checkAt canonAt
    exact ⟨.returned value, _, _, checkEnd, canonEnd, appendRun checkedRun (checkReply _), appendRun canonRun (canonReply _),
      stores, by rw [silentTail _ _ rfl, silentTail _ _ rfl, seen], left, right, lhs, rhs, rfl, rfl,
      checkedRun, canonRun, checkReply, canonReply, checkHost, canonHost, paired⟩
  | refused issue =>
    obtain ⟨stop, stopped, checkAt, canonAt, tracks, canonTracks⟩ := result
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
      by rw [silentTail _ _ rfl, seen], left, lhs, canon, stop, stopped, rfl, checkedRun, canonTracks, rfl, resumes, canonAt⟩

private theorem listEntries {entries : List Field} {element schema : Stored.TypeOf}
    (matched : Field.LayoutMatches (.dynamic (.list element) element entries) schema) : Field.EntriesMatch entries element := by
  cases matched with
  | list children => exact children

private theorem nominalEntry {item : Field} {element : Stored.TypeOf}
    (nominal : NominalElement element) (shape : item.LayoutMatches element) (emitted : item.Emitted) : CanonicalHandle item := by
  cases item with
  | owner | endpoint | context => trivial
  | data => cases nominal <;> cases shape <;> cases emitted
  | aggregate | fixed | dynamic | sum => cases nominal <;> cases shape

private theorem mapPlacement (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (before : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig))
    (next : AddrType → Session grow sig (Ret (core3 grow)))
    (width : (core3 grow).memAddrType? before.store.core destination.memory = some destination.width)
    (atPlacement : before.ctl = canon.control (mapFieldPlacement (destination.context inst)
      (CanonicalTree.EntryMode.forOutput destination.width (.map key element) output) next)) :
    ∃ labels, visible labels = [] ∧ ReturnFrame.Occurrence.RetainsActiveSlots profile ready
      (specDispatch ready (LiveDispatch.host bindings base)) before labels
      { before with ctl := canon.control (next destination.width) } := by
  cases output with
  | memory address =>
    have same : before = { before with ctl := canon.control (next destination.width) } := by
      cases before
      simp_all [mapFieldPlacement, CanonicalTree.EntryMode.forOutput]
    exact ⟨[], rfl, fun depth => same ▸ .done before (.active 0 depth)⟩
  | flat =>
    have reached : ptrTypeIn before.store (destination.context inst) = destination.width := by
      simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, width]
    refine ⟨[.tau], rfl, fun depth => ?_⟩
    change before.ctl = canon.control (.op .get (fun store => next (ptrTypeIn store (destination.context inst)))) at atPlacement
    simpa only [reached, Cursor.control] using (ReturnFrame.Occurrence.Prefix.read (profile := profile)
      (ready := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base)) depth atPlacement)

theorem stringMapKey (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value root : Field) {schema : Stored.TypeOf}
    (layoutRoot : root.LayoutMatches schema)
    (fitRoot : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocator : Field.AllocatorFor destination.realloc root)
    (path : Field.Descendant root (.aggregate (.record (mapEntryFields .string element)) [key.field, value]))
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex issueIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (entry : entryIndex < count)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields .string element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keySlot := fun reached => alignTo ptr (layout reached key.field.type).alignment
    let valueSlot := fun keyWidth reached => alignTo
      (keySlot keyWidth + (layout keyWidth key.field.type).size) (layout reached value.type).alignment
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let afterKey := fun keyWidth (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory (valueSlot keyWidth reached)) >>= canonNext
    let following := fun verdict : Except RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1
          (.memory (valueSlot destination.width destination.width))) >>= fun result => checkNext (result.mapError (.nested issueIndex))
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [key.field, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width key.field (.memory (keySlot reached)) >>= afterKey reached) →
    StringKeyFront profile ready base bindings older destination inst key (keySlot destination.width) left right check canon
      following (afterKey destination.width) := by
  intro cx type ptr keySlot valueSlot mode afterKey following checkAt canonAt
  let keyPayload : Stored.Payload (.prim .string) := ⟨.string key.value, .string key.valid⟩
  let keyOutput := Stored.Lower.Output.memory (keySlot destination.width)
  have keyPath : Field.Descendant root key.field := path.trans (.aggregate (by simp) (.self _))
  have fit := Field.Descendant.string_pre keyPayload rfl keyPath layoutRoot Quirks.none destination.encoding destination.width fitRoot
  obtain ⟨address, realloc⟩ := allocator key.field keyPath rfl
  have currentWidth := growth.memAddrType width
  obtain ⟨placed, checkTracks⟩ := map_key_placement (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    destination inst .string element keyPayload value origin basePtr bytes count entryIndex width sized aligned bounds entry issueIndex
    left (frame.store ▸ growth) check checkNext checkAt
  obtain ⟨canonLabels, canonQuiet, canonTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
    (bindings := bindings) destination inst .string element output right canon _ currentWidth canonAt
  let checkKey := { left with ctl := check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
    key.field 0 keyOutput >>= following) }
  let canonKey := { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width
    key.field keyOutput >>= afterKey destination.width) }
  obtain ⟨reads, keyLeft, keyRight⟩ := string_plan_entry_between (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst
    key.value key.valid 0 keyOutput checkKey canonKey check canon following (afterKey destination.width) frame.store currentWidth
    realloc fit placed rfl rfl
  unfold StringKeyFront
  refine ⟨[.tau] ++ List.replicate reads .tau, canonLabels ++ [.tau], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [appendVisible, silent (fun _ member => List.eq_of_mem_replicate member)]
    rfl
  · rw [appendVisible, canonQuiet]
    rfl
  · exact fun depth => (checkTracks depth).append (keyLeft depth)
  · exact fun depth => (canonTracks depth).append (keyRight depth)
  · exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
  · exact string_front_cut_between _ _ _ _ _ _ _ _ _ frame.store rfl rfl

private theorem nominalMapEntry (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output)
    (keyData : LocalDataType (.prim key.toPrimitive)) (keyPayload : Stored.Payload (.prim key.toPrimitive))
    (value : Field) (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : entryIndex < count) (issueIndex : Nat)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    let afterKey := fun (keyWidth : AddrType) (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      let area := layout keyWidth keyField.type
      let address := alignTo (alignTo ptr area.alignment + area.size) (layout reached value.type).alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory address) >>= canonNext
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [keyField, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField
        (.memory (alignTo ptr (layout reached keyField.type).alignment)) >>= afterKey reached) →
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (· = afterKey destination.width ()) (fun reached => Core3.Grows origin.core reached.core) := by
  intro cx type ptr keyField mode afterKey checkAt canonAt
  let keyArea := layout destination.width keyField.type
  let keyPtr := alignTo ptr keyArea.alignment
  let valPtr := alignTo (keyPtr + keyArea.size) (layout destination.width value.type).alignment
  let onChecked := fun verdict : Except RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
  let checkValue : Session grow sig (Except RecordLower.Issue Unit) :=
    Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valPtr)
  let canonKeyStart := { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width
    keyField (.memory keyPtr) >>= afterKey destination.width) }
  obtain ⟨headLabels, headQuiet, headTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
    (bindings := bindings) destination inst key element output right canon _ (growth.memAddrType width) canonAt
  obtain ⟨store, result, checkKey, canonKey, runCheckKey, runCanonKey, keyLabels, keyStatus⟩ :=
    local_map_key_then_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst key element keyData keyPayload value
      origin basePtr bytes count entryIndex width sized aligned bounds entry issueIndex left canonKeyStart growth frame.store
      check canon frame.thread checkNext (afterKey destination.width) checkAt rfl
  have keyRun := appendRun (prefix_survives (headTracks 0)).1 runCanonKey.steps
  have keySeen : visible checkKey = visible (headLabels ++ canonKey) := by
    rw [appendVisible, headQuiet, List.nil_append, keyLabels]
  cases result with
  | error reason =>
    obtain ⟨prior, stopped⟩ := keyStatus
    exact ⟨canon, .trapped reason, _, _, _, _, runCheckKey, keyRun, rfl, keySeen, rfl, rfl, prior,
      by rw [appendVisible, headQuiet, List.nil_append, stopped]⟩
  | ok result =>
    cases result
    obtain ⟨grown, trackedLeft, trackedRight⟩ := keyStatus
    let checked := { left with store, ctl := check.control (checkValue >>= onChecked) }
    let valueStart := { right with store, ctl := canon.control (afterKey destination.width ()) }
    let canonValue : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory valPtr)
    let canonical := { right with store, ctl := canon.control (canonValue >>= canonNext) }
    obtain ⟨valueLabels, valueQuiet, valueTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
      (bindings := bindings) destination inst key element output valueStart canon (fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory (alignTo (keyPtr + keyArea.size) (layout reached value.type).alignment)) >>= canonNext)
      (grown.memAddrType width) rfl
    have reached : LinkedCallback.ChildFrameOver older checked canonical check canon :=
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
      (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst value (nominalEntry nominal matched emitted)
      1 (.memory valPtr) onChecked canonNext reached grown rfl rfl
      (next := fun _ lhs rhs check canon => LinkedCallback.ChildFrameOver older lhs rhs check canon ∧ Core3.Grows origin.core lhs.store.core)
      (fun _ _ _ _ _ related grown _ _ => ⟨related, grown⟩)
    unfold LinkedCallback.HandleFieldThenBetween at leaf
    cases live : liveLeafPlan checked.store checked.host.writer 1 value with
    | error issue =>
      rw [live] at leaf
      obtain ⟨labels, quiet, tracks⟩ := leaf
      exact ⟨canon, .refused (.nested issueIndex issue), _, _, _, valueStart,
        appendRun runCheckKey (prefix_survives (tracks 0)).1, keyRun, rfl,
        by rw [appendVisible, silent quiet, List.append_nil, keySeen],
        _, rfl, rfl, rfl, fun depth => (trackedLeft depth).append (tracks depth),
        fun depth => (headTracks depth).append (trackedRight depth)⟩
    | ok plan =>
      rw [live] at leaf
      obtain ⟨reachedStore, outcome, guard, checkLabels, canonLabels, quiet, seenLeft, seenRight, runLeft, runRight, success⟩ := leaf
      have leftRun := appendRun runCheckKey runLeft
      have rightRun := appendRun keyRun (appendRun (prefix_survives (valueTracks 0)).1 runRight)
      cases outcome with
      | error reason =>
        refine ⟨canon, .trapped reason, _, _, _, _, leftRun, rightRun, rfl, ?_, rfl, rfl, visible (headLabels ++ canonKey), ?_⟩
        · simp only [appendVisible, silent quiet, headQuiet, valueQuiet, List.nil_append,
            leafTrap seenLeft, leafTrap seenRight, keyLabels]
        · simp only [appendVisible, valueQuiet, List.nil_append, leafTrap seenRight]
      | ok result =>
        cases result
        obtain ⟨leftTracks, rightTracks, paired, kept⟩ := success () rfl
        refine ⟨canon, .returned (), _, _, _, _, leftRun, rightRun, rfl, ?_, paired, rfl, rfl, ?_, ?_, kept⟩
        · simp only [appendVisible, silent quiet, headQuiet, valueQuiet, leafSilent seenLeft,
            leafSilent seenRight, List.nil_append, keyLabels]
        · exact fun depth => (trackedLeft depth).append (leftTracks depth)
        · exact fun depth => ((headTracks depth).append (trackedRight depth)).append ((valueTracks depth).append (rightTracks depth))

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

private theorem collectionCaller {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (type element : Stored.TypeOf) (entries : List Field)
    (field : site.field = .dynamic type element entries)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer (Field.listObjects entries) = .ok ())
    {checked : Config (core3 grow) (HostState sig)} {checkTrace} :
    let area := layout site.destination.width element
    let resume := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    Trail profile ready (specDispatch ready base)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor resume)
      (some (.active 0 0)) checkTrace checked (some (.active 0 0)) →
    ∃ trace, Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) trace checked (.active 0 1) := by
  intro area resume trail
  have width := site.destination.check_width site.start.store linked.destination
  have checkAt : site.checked.ctl = site.cursor.control (Stored.OwnedMemory.Claims.Record.Effects.field
      recordClaims Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
      (.dynamic type element entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have canonAt := site.reference_at linked site.referenceReply
  rw [field] at canonAt
  have entered := (collection_install_tracks (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    site.destination site.inst type element entries route.output 0 site.checked (site.reference site.referenceReply)
    site.cursor site.cursor site.reply site.referenceReply width prepared checkAt canonAt 0).1
  obtain ⟨place, initial, track⟩ := trail.survives
  cases initial
  exact ⟨_, entered.append (track.under 1)⟩

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
  obtain ⟨_, caller⟩ := collectionCaller site linked (.list element) element entries field prepared mark.checkedTrail
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.list element) element
    entries route.output 0 pointer site.reply site.referenceReply mark paired returned width growth
  exact replies site caller (localTail site.destination site.inst element entries .value route.output 0 pointer
    site.reply site.referenceReply (fun bytes left right canon reachedWidth sized aligned bounds same thread checkAt rightAt =>
      local_data_collection_tail site.destination site.inst element data entries children pointer bytes 0 route.output left right
        reachedWidth sized aligned bounds same check canon thread site.reply site.referenceReply checkAt rightAt) cut)

theorem nominalListReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    (admitted : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
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
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply) := by
  intro area first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted admitted
  have entriesMatch := listEntries matched
  cases emitted with
  | list children =>
    have handles : ∀ item ∈ entries, CanonicalHandle item := fun item member =>
      nominalEntry nominal (entries_match_of_mem entriesMatch member) (children item member)
    obtain ⟨_, caller⟩ := collectionCaller site linked (.list element) element entries field admitted mark.checkedTrail
    have width := site.destination.check_width site.start.store linked.destination
    have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.list element) element
      entries route.output 0 pointer site.reply site.referenceReply mark paired returned width growth
    refine replies site caller (rangeThen site.destination site.inst element entries .value route.output 0 pointer
      site.reply site.referenceReply (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply)
      (.inl rfl) ?_ cut)
    intro _ left right canon _ _ _ _ frame checkAt canonAt
    obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, status⟩ :=
      finishElements site.destination site.inst entries area .value route.output 0 pointer site.reply site.referenceReply checkAt canonAt
        (ElementStop site.destination site.inst entries area.size pointer)
        (fun checkTail canonTail lhs rhs => nominalElements site.destination site.inst entries handles area.size pointer 0
          checkTail canonTail frame lhs rhs)
    refine ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, ?_⟩
    cases outcome with
    | returned _ | trapped _ => exact status
    | refused _ =>
      obtain ⟨stop, witness, rest⟩ := status
      exact ⟨stop, .inr witness, rest⟩

private theorem nominalMapElements (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output)
    (keyData : LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (origin : CStore (core3 grow)) (basePtr bytes count : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entries : List Field) (index : Nat) (room : index + entries.length ≤ count)
    (shape : ∀ item ∈ entries, ∃ (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) keyPayload, value] ∧
        value.LayoutMatches element ∧ value.Emitted)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core) :
    let stride := (layout destination.width (.record (mapEntryFields key element))).size
    let ptr := basePtr + index * stride
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride ptr index >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries
      mode stride ptr >>= canonNext) →
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (MapValueStop destination inst key element mode entries stride ptr canonNext) := by
  induction entries generalizing index left right check canon with
  | nil =>
    intro _ _ _ _ checkAt canonAt
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨canon, .returned (), [], [], left, right, .refl _, .refl _, frame.store, rfl,
      frame, checkAt, canonAt, fun depth => .done _ _, fun depth => .done _ _, trivial⟩
  | cons item rest ih =>
    intro stride ptr cx mode checkAt canonAt
    have valid : index < count := by simp only [List.length_cons] at room; omega
    have nextRoom : index + 1 + rest.length ≤ count := by simp only [List.length_cons] at room; omega
    have nextPtr : basePtr + (index + 1) * stride = ptr + stride := by
      simp only [ptr, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    obtain ⟨keyPayload, value, shapeHead, matched, emitted⟩ := shape item (by simp)
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
      (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width rest stride (ptr + stride) (index + 1))
        >>= checkNext
    let canonRest : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (ptr + stride)
    let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ => canonRest >>= canonNext
    let afterKey := fun (keyWidth : AddrType) (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      let area := layout keyWidth keyField.type
      let address := alignTo (alignTo ptr area.alignment + area.size) (layout reached value.type).alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory address) >>= canonTail
    have atHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
        (.aggregate type [keyField, value]) index (.memory ptr) >>= checkTail) := by
      rw [checkAt, shapeHead, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checkTail]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok result => cases result; rfl
    have atCanonHead : right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField
          (.memory (alignTo ptr (layout reached keyField.type).alignment)) >>= afterKey reached) := by
      rw [canonAt, shapeHead]
      apply congrArg canon.control
      let readWidth : Session grow sig AddrType := ptrType cx
      let keySlot := fun reached => alignTo ptr (layout reached keyField.type).alignment
      let keyBody : AddrType → Session grow sig Unit := fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory (keySlot reached))
      let valBody : AddrType → AddrType → Session grow sig Unit := fun keyWidth reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory (alignTo (keySlot keyWidth + (layout keyWidth keyField.type).size) (layout reached value.type).alignment))
      cases output with
      | memory address =>
        let reached := destination.width
        change ((keyBody reached).bind (fun _ => (valBody reached reached).bind (fun _ => canonRest))).bind canonNext =
          (keyBody reached).bind (fun _ => (valBody reached reached).bind (fun _ => canonRest.bind canonNext))
        simp only [Prog.bind_assoc]
      | flat =>
        change ((readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
          readWidth.bind fun reached => (valBody keyWidth reached).bind fun _ => .pure ())).bind (fun _ => canonRest)).bind canonNext =
          readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
            readWidth.bind fun reached => (valBody keyWidth reached).bind fun _ => canonRest.bind canonNext)
        simp only [Prog.bind_assoc, Prog.pure_bind']
    obtain ⟨reached, outcome, headLeft, headRight, middleLeft, middleRight, runHeadLeft, runHeadRight, same, seen, status⟩ :=
      nominalMapEntry (profile := profile) (ready := ready) (base := base) (bindings := bindings)
        destination inst key element output keyData keyPayload value nominal matched emitted origin basePtr bytes count index width sized aligned bounds
        valid index checkTail canonTail frame growth atHead atCanonHead
    cases outcome with
    | trapped reason => exact ⟨reached, .trapped reason, _, _, _, _, runHeadLeft, runHeadRight, same, seen, status⟩
    | refused issue =>
      obtain ⟨stop, stopped, leftAt, rightAt, leftTracks, rightTracks⟩ := status
      refine ⟨reached, .refused issue, _, _, _, _, runHeadLeft, runHeadRight, same, seen, stop,
        ⟨[], rest, keyField, value, congrArg (· :: rest) shapeHead, ?_⟩, leftAt, rightAt, leftTracks, rightTracks⟩
      change stop = mapValueSuffix destination inst mode keyField value rest stride (ptr + 0 * stride) canonNext
      rw [Nat.zero_mul, Nat.add_zero]
      exact stopped
    | returned result =>
      cases result
      obtain ⟨paired, reachedLeft, reachedRight, leftTracks, rightTracks, grown⟩ := status
      have next := ih (index + 1) nextRoom (fun child member => shape child (List.mem_cons_of_mem _ member))
        paired (paired.store ▸ grown)
      dsimp only at next
      have advance : basePtr + (index + 1) * (layout destination.width (.record (mapEntryFields key element))).size = ptr + stride := nextPtr
      rw [advance] at next
      obtain ⟨last, outcome, tailLeft, tailRight, finalLeft, finalRight, runTailLeft, runTailRight, sameFinal, seenTail, finish⟩ :=
        next reachedLeft reachedRight
      refine ⟨last, outcome, _, _, finalLeft, finalRight, appendRun runHeadLeft runTailLeft, appendRun runHeadRight runTailRight,
        sameFinal, by rw [appendVisible, appendVisible, seen, seenTail], ?_⟩
      cases outcome with
      | returned result =>
        obtain ⟨finalPair, leftAt, rightAt, leftTail, rightTail, kept⟩ := finish
        exact ⟨finalPair, leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth),
          fun depth => (rightTracks depth).append (rightTail depth), kept⟩
      | refused issue =>
        obtain ⟨stop, ⟨leading, suffix, keySlot, valueSlot, split, stopped⟩, leftAt, rightAt, leftTail, rightTail⟩ := finish
        refine ⟨stop, ⟨item :: leading, suffix, keySlot, valueSlot, congrArg (item :: ·) split, ?_⟩,
          leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth), fun depth => (rightTracks depth).append (rightTail depth)⟩
        have address : ptr + (item :: leading).length * stride = (ptr + stride) + leading.length * stride := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        change stop = mapValueSuffix destination inst mode keySlot valueSlot suffix stride
          (ptr + (item :: leading).length * stride) canonNext
        rw [address]
        exact stopped
      | trapped reason =>
        obtain ⟨leftDone, rightDone, leading, stopped⟩ := finish
        exact ⟨leftDone, rightDone, visible headRight ++ leading, by rw [appendVisible, stopped, List.append_assoc]⟩

private theorem mapEntries {entries : List Field} {key : WIT.KeyType} {element schema : Stored.TypeOf}
    (matched : Field.LayoutMatches (.dynamic (.map key element) (.record (mapEntryFields key element)) entries) schema) :
    Field.EntriesMatch entries (.record (mapEntryFields key element)) := by
  cases matched with
  | map children => exact children

private theorem mapValueLayout {key : WIT.KeyType} {element : Stored.TypeOf} {keyField value : Field}
    (matched : Field.LayoutMatches (.aggregate (.record (mapEntryFields key element)) [keyField, value])
      (.record (mapEntryFields key element))) : value.LayoutMatches element := by
  cases matched with
  | record fields =>
    cases fields with
    | cons _ tail =>
      cases tail with
      | cons shape _ => exact shape

theorem nominalMapReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    (admitted : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map key element) output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (MapReturnStop site.destination site.inst key element entries output pointer site.referenceReply) := by
  intro entryType area output mode first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted admitted
  have children := mapEntries matched
  cases emitted with
  | map shapes emitted =>
    have shape : ∀ item ∈ entries, ∃ (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
        item = .aggregate entryType [.data (.prim key.toPrimitive) keyPayload, value] ∧
          value.LayoutMatches element ∧ value.Emitted := by
      intro item member
      have layout := entries_match_of_mem children member
      obtain ⟨keyPayload, value, rfl⟩ := shapes item member
      exact ⟨keyPayload, value, rfl, mapValueLayout layout, emitted keyPayload value member⟩
    obtain ⟨_, caller⟩ := collectionCaller site linked (.map key element) entryType entries field admitted mark.checkedTrail
    have width := site.destination.check_width site.start.store linked.destination
    have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.map key element) entryType
      entries output 0 pointer site.reply site.referenceReply mark paired returned width growth
    refine replies site caller (rangeThen site.destination site.inst entryType entries mode output 0 pointer
      site.reply site.referenceReply (MapReturnStop site.destination site.inst key element entries output pointer
        site.referenceReply) (.inl rfl) ?_ cut)
    intro bytes left right canon reachedWidth sized aligned bounds frame checkAt canonAt
    obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, status⟩ :=
      finishElements site.destination site.inst entries area mode output 0 pointer site.reply site.referenceReply checkAt canonAt
        (MapValueStop site.destination site.inst key element mode entries area.size pointer)
        (fun checkTail canonTail lhs rhs => by
          have visit := nominalMapElements (profile := profile) (ready := ready) (base := base) (bindings := bindings)
            site.destination site.inst key element output keyData nominal left.store pointer bytes entries.length reachedWidth sized aligned bounds
            entries 0 (by simp) shape checkTail canonTail frame (frame.store ▸ Core3.Grows.refl _)
          simp only [Nat.zero_mul, Nat.add_zero] at visit
          exact visit lhs rhs)
    refine ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, ?_⟩
    cases outcome with
    | returned _ | trapped _ => exact status
    | refused _ =>
      obtain ⟨stop, witness, tail⟩ := status
      exact ⟨stop, .inr witness, tail⟩

theorem localMapReplies {outputPointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory outputPointer))
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : LocalDataType (.prim key.toPrimitive)) (valueData : LocalDataType element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let mode := CanonicalTree.EntryMode.memoryMap site.destination.width key element
    let output := (GiveEffectRoute.memory outputPointer).output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (canonicalCollectionTail site.destination site.inst entries area output pointer mode >>= site.referenceReply) := by
  intro entryType area mode output first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Stored.OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Stored.OwnedMemory.Claims.Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted
  have children := mapEntries matched
  have prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer
      (Field.listObjects entries) = .ok () := by rw [local_data_map_objects valueData children emitted]; rfl
  obtain ⟨_, caller⟩ := collectionCaller site linked (.map key element) entryType entries field prepared mark.checkedTrail
  have width := site.destination.check_width site.start.store linked.destination
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.map key element) entryType
    entries output 0 pointer site.reply site.referenceReply mark paired returned width growth
  exact replies site caller (localTail site.destination site.inst entryType entries mode output 0 pointer site.reply site.referenceReply
    (fun bytes left right canon reachedWidth sized aligned bounds same thread checkAt rightAt =>
      local_map_collection_tail site.destination site.inst key element keyData valueData entries children emitted pointer bytes 0
        (flatNat outputPointer) left right reachedWidth sized aligned bounds same check canon thread site.reply site.referenceReply
        checkAt rightAt) cut)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
