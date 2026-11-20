module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

theorem slotsMap (mode : Track) (width : AddrType) {premise target : Field → Nat → Prop}
    (convert : ∀ item address, premise item address → target item address) (items : List Field) (cursor : Nat)
    (slots : mode.Slots width premise items cursor) : mode.Slots width target items cursor := by
  induction items generalizing cursor with
  | nil => exact trivial
  | cons item rest ih => exact ⟨convert item _ slots.1, ih _ slots.2⟩

private theorem fieldSlots (width : AddrType) (rule : Field → Nat → Prop) (items : List Field) (base : Nat)
    (placed : ∀ (index : Nat) item address, items[index]? = some item →
      (fieldOffsets base (items.map fun field => layout width field.type))[index]? = some address → rule item address) :
    Track.fields.Slots width rule items base := by
  induction items generalizing base with
  | nil => exact trivial
  | cons item rest ih =>
    refine ⟨placed 0 item _ rfl rfl, ih _ ?_⟩
    intro index child address found offset
    exact placed (index + 1) child address found offset

theorem aggregateSlots (width : AddrType) {type : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.LayoutMatches (.aggregate type items) type)
    (aligned : base % (layout width type).alignment.bytes = 0) (bounds : base + (layout width type).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    Track.fields.Slots width rule items base := by
  have compiled := compiled_aggregate_layout width matched
  rw [compiled] at aligned bounds
  apply fieldSlots
  intro index item address found offset
  have shape : (items.map fun field => layout width field.type)[index]? = some (layout width item.type) := by
    simp only [List.getElem?_map, found, Option.map_some]
  obtain ⟨_, modulo, fits⟩ := recordLayout_field_fits _ base index address _ (Nat.dvd_of_mod_eq_zero aligned) shape offset
  exact child item (List.mem_of_getElem? found) address ⟨modulo, fits.trans bounds⟩

theorem elementSlots (width : AddrType) {element : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.EntriesMatch items element) (aligned : base = alignTo base (layout width element).alignment)
    (bounds : base + items.length * (layout width element).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    (Track.elements (layout width element).size).Slots width rule items base := by
  let area := layout width element
  have baseDiv : area.alignment.bytes ∣ base :=
    ⟨(base + area.alignment.bytes - 1) / area.alignment.bytes, aligned.trans (Nat.mul_comm ..)⟩
  have strideDiv : area.alignment.bytes ∣ area.size := ⟨area.units, Nat.mul_comm ..⟩
  clear aligned
  induction items generalizing base with
  | nil => exact trivial
  | cons item rest ih =>
    cases matched with
    | cons head tail =>
      have layoutEq : layout width item.type = area := congrArg (layout width) head.type_eq
      have positioned : SlotFits width bytes item base := by
        unfold SlotFits
        rw [layoutEq]
        refine ⟨Nat.mod_eq_zero_of_dvd baseDiv, ?_⟩
        simpa only [List.length_cons, Nat.succ_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (Nat.add_le_add_left (Nat.mul_le_mul_right area.size (Nat.succ_le_succ (Nat.zero_le rest.length))) base).trans bounds
      refine ⟨child item (List.mem_cons_self ..) base positioned, ih tail ?_ ?_ (Nat.dvd_add baseDiv strideDiv)⟩
      · simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounds
      · exact fun entry member => child entry (List.mem_cons_of_mem _ member)

private theorem focusStep (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (rest : List Field)
    (cursor : Nat) (canonNext : CanonNext grow sig) (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig))
    (width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (atProgram : right.ctl = canon.control (mode.canonical destination inst (item :: rest) cursor >>= canonNext)) :
    Steps profile ready (specDispatch ready (host bindings)) right mode.readLabels
      (focus mode destination inst item cursor right canon
        (canonTail mode destination inst rest (mode.slot destination.width item cursor).2 canonNext)) := by
  cases mode with
  | placedFields =>
    let position := Track.placedFields.slot destination.width item cursor
    let entered := focus .placedFields destination inst item cursor right canon
      (canonTail .placedFields destination inst rest position.2 canonNext)
    have control : right.ctl = entered.ctl := by
      rw [atProgram]
      change canon.control (((CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        item (.memory position.1)).bind (fun () => canonicalPlacedFields destination inst rest position.2)).bind canonNext) = _
      rw [Prog.bind_assoc]
      rfl
    have same : entered = right :=
      (congrArg (fun ctl => { right with ctl }) control.symm).trans (by cases right; rfl)
    change Steps profile ready (specDispatch ready (host bindings)) right [] entered
    rw [same]
    exact .refl right
  | elements stride =>
    let entered := focus (.elements stride) destination inst item cursor right canon
      (canonTail (.elements stride) destination inst rest (cursor + stride) canonNext)
    have control : right.ctl = entered.ctl := by
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
        destination.width item (.memory cursor)
      let tail : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
        destination.width rest .value stride (cursor + stride)
      rw [atProgram]
      change canon.control ((head.bind (fun () => tail)).bind canonNext) =
        canon.control (head.bind (fun () => tail.bind canonNext))
      rw [Prog.bind_assoc]
    have same : entered = right :=
      (congrArg (fun ctl => { right with ctl }) control.symm).trans (by cases right; rfl)
    change Steps profile ready (specDispatch ready (host bindings)) right [] entered
    rw [same]
    exact .refl right
  | fields =>
    let cx := destination.context (grow := grow) inst
    let body := fun current =>
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address) >>= fun () =>
        CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size) >>= canonNext
    have atRead : right.ctl = canon.control (ptrType cx >>= body) := by
      rw [atProgram]
      congr 1
      simp only [Track.canonical, CanonicalTree.memory, Prog.bind_eq, Prog.bind_assoc, body, cx]
      congr 1
      funext current
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address)
      let tail : Session grow sig Unit := CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size)
      change (head.bind (fun () => tail)).bind canonNext = head.bind (fun () => tail.bind canonNext)
      rw [Prog.bind_assoc]
    have step := (CoreGrowthSteps.refl (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings)) right).read_width
      cx rfl width body atRead
    exact step.steps

theorem replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (slots : mode.Slots destination.width (FieldRule compare older origin destination inst) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon := by
  induction items generalizing index cursor left right check canon with
  | nil =>
    change finish left right check canon
    apply ends left right check canon frame growth
    · cases mode <;> simpa only [Track.checked, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using checkAt
    · cases mode <;> simpa only [Track.canonical, canonicalPlacedFields, CanonicalTree.memory, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using canonAt
  | cons item rest ih =>
    rw [Replay]
    change FieldRule compare older origin destination inst item (mode.slot destination.width item cursor).1 ∧
      mode.Slots destination.width (FieldRule compare older origin destination inst) rest (mode.slot destination.width item cursor).2 at slots
    have width := frame.store ▸ growth.memAddrType present
    refine ⟨focusStep mode destination inst item rest cursor canonNext right canon width canonAt, ?_⟩
    let nextAddress := (mode.slot destination.width item cursor).2
    let nextCheck := checkTail mode destination inst rest (index + 1) nextAddress checkNext
    let nextCanon := canonTail mode destination inst rest nextAddress canonNext
    let focused := focus mode destination inst item cursor right canon nextCanon
    have paired : ChildFrameOver older left focused check canon :=
      ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    refine slots.1 index nextCheck nextCanon left focused check canon paired growth ?_ rfl _ ?_
    · rw [checkAt]
      congr 1
      cases mode <;> simp only [Track.checked, Track.slot, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.bind_assoc]
      all_goals
        congr 1
        funext verdict
        cases verdict with
        | error issue => rfl
        | ok result => cases result; rfl
    · intro reached reference pushedCheck pushedCanon paired grown checked canonical
      exact ih (index + 1) (mode.slot destination.width item cursor).2 paired grown slots.2 checked canonical

theorem mixedRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (allocator : Validation.containsPtr item.type = true → ∃ addr, destination.realloc = some addr)
    (slot : MixedSlot destination bytes item address) :
    FieldRule (mixed profile ready bindings older destination inst) older origin destination inst item address := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  rcases slot with handle | ⟨⟨str, rfl, fit⟩, aligned, bounds⟩
  · exact .inl ⟨handle, frame.handle_field_then destination inst item handle index (.memory address) checkNext canonNext
      growth checkAt canonAt (fun () => ends)⟩
  · obtain ⟨reachedBytes, sizeAt, widened⟩ := growth.memSize sized
    obtain ⟨_, realloc⟩ := allocator rfl
    change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at sizeAt
    change address % (layout destination.width (.prim .string : TypeOf)).alignment.bytes = 0 at aligned
    change address + (layout destination.width (.prim .string : TypeOf)).size ≤ bytes at bounds
    have placed : rootPlacement destination left.store (.prim .string) (.memory address) = .ok () := by
      simp [rootPlacement, placement, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
      rfl
    exact .inr ⟨str, rfl, frame.string_field_then destination inst str (.memory address) index checkNext canonNext
      growth present realloc fit placed checkAt canonAt (fun () => ends)⟩

private theorem aggregateEntry {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (items : List Field) (index address : Nat)
    (left : State grow sig) (check : Cursor (E := core3 grow) (HostState sig)) (checkNext : CheckNext grow sig)
    (growth : Core3.Grows origin.core left.store.core)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : address % (layout destination.width type).alignment.bytes = 0)
    (bounds : address + (layout destination.width type).size ≤ bytes)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width (.aggregate type items) index (.memory address) >>= checkNext)) :
    Steps profile ready (specDispatch ready (host bindings)) left [.tau] (enterAggregate destination inst items index address left check checkNext) := by
  let area := layout destination.width type
  let body := Track.fields.checked (grow := grow) (sig := sig) destination inst items 0 address >>= aggregateNext index checkNext
  obtain ⟨reachedBytes, sizeAt, widened⟩ := growth.memSize sized
  change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at sizeAt
  have placementAt : placement destination left.store area address = .ok () := by
    simp [placement, area, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
    rfl
  have guardAt : left.ctl = check.control (do
      checkAligned address area.alignment.bytes
      checkInBounds (destination.context inst) address area.size
      body) := by
    rw [Record.Effects.field] at checkAt
    let children := Track.fields.checked (grow := grow) (sig := sig) destination inst items 0 address
    let range : Session grow sig Unit := checkInBounds (destination.context inst) address area.size
    change left.ctl = check.control ((range.bind fun () => children.bind fun verdict =>
      Prog.pure (verdict.mapError (.nested index))).bind checkNext) at checkAt
    rw [Prog.bind_assoc] at checkAt
    have focused : left.ctl = check.control (range.bind fun () => body) := by
      rw [checkAt]
      congr 2
      funext result
      cases result
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    simpa [checkAligned, trapIf, area, aligned, Prog.bind_eq, Prog.pure_bind', range] using focused
  have guard := check_placement_steps (profile := profile) (placementReady := ready) (placementDispatch := specDispatch ready (host bindings))
    destination inst left area address check body guardAt
  rw [placementAt] at guard
  exact guard

theorem aggregateReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (items : List Field) (index address : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (matched : Field.LayoutMatches (.aggregate type items) type)
    (aligned : address % (layout destination.width type).alignment.bytes = 0)
    (bounds : address + (layout destination.width type).size ≤ bytes)
    (child : ∀ item ∈ items, ∀ slot, SlotFits destination.width bytes item slot → FieldRule compare older origin destination inst item slot)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width (.aggregate type items) index (.memory address) >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width (.aggregate type items) (.memory address) >>= canonNext)) :
    Steps profile ready (specDispatch ready (host bindings)) left [.tau] (enterAggregate destination inst items index address left check checkNext) ∧
      Replay profile ready bindings .fields destination inst compare (aggregateNext index checkNext) canonNext finish
        items 0 address (enterAggregate destination inst items index address left check checkNext) right check canon := by
  have guard := aggregateEntry (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type items index address left check checkNext growth sized aligned bounds checkAt
  rw [CanonicalTree.field] at canonAt
  refine ⟨guard, replay .fields destination inst items 0 address compare (aggregateNext index checkNext) canonNext finish ?_
    growth present (aggregateSlots destination.width matched aligned bounds _ child) ends rfl canonAt⟩
  exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩

private theorem matchedField {items : List Field} {types : List TypeOf} {item : Field}
    (matched : Field.FieldsMatch items types) (member : item ∈ items) : item.LayoutMatches item.type := by
  induction items generalizing types with
  | nil => simp at member
  | cons first rest ih =>
    cases matched with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | inside
      · rw [head.type_eq]; exact head
      · exact ih tail inside

private theorem matchedAggregateChild {children : List Field} {type : TypeOf} {child : Field}
    (matched : Field.LayoutMatches (.aggregate type children) type) (member : child ∈ children) : child.LayoutMatches child.type := by
  cases matched with
  | record childMatches => exact matchedField childMatches member
  | tuple childMatches => exact matchedField childMatches member

theorem nestedRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (shape : AggregateShape (StringField.Fits destination) depth item) (matched : item.LayoutMatches item.type)
    (placement : SlotFits destination.width bytes item address) :
    FieldRule (nested profile ready bindings older destination inst depth) older origin destination inst item address := by
  induction depth generalizing item address with
  | zero =>
    cases shape with
    | handle handle => exact mixedRule destination inst item address present sized (fun _ => ⟨_, realloc⟩) (.inl handle)
    | string fit => exact mixedRule destination inst item address present sized (fun _ => ⟨_, realloc⟩) (.inr ⟨fit, placement⟩)
  | succ depth ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
    cases shape with
    | handle handle => exact .inl (mixedRule destination inst item address present sized (fun _ => ⟨_, realloc⟩) (.inl handle)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | string fit => exact .inl (mixedRule destination inst item address present sized (fun _ => ⟨_, realloc⟩) (.inr ⟨fit, placement⟩)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | @aggregate _ type children child =>
      refine .inr ⟨type, children, rfl, aggregateReplay destination inst type children index address _
        checkNext canonNext finish frame growth present sized matched placement.1 placement.2 ?_ ends checkAt canonAt⟩
      exact fun entry member slot fits => ih entry slot (child entry member) (matchedAggregateChild matched member) fits

theorem valueTailWith {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (element : TypeOf) (entries : List Field) (index pointer : Nat)
    (compare : FieldComparison grow sig)
    (output : Lower.Output) (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (next : ValueFinish grow sig output) {initial checked canonical : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {bytes : Nat}
    (region : CollectionVisit.Admitted older destination (layout destination.width element) entries pointer bytes
      initial checked canonical check canon)
    (matched : Field.EntriesMatch entries element)
    (children : ∀ item ∈ entries, ∀ address, SlotFits destination.width bytes item address →
      FieldRule compare older checked.store destination inst item address)
    (ends : ∀ value reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows initial.store.core reached.store.core → reached.ctl = check.control (checkNext (.ok value)) →
      reference.ctl = canon.control (canonNext value) → next value reached reference check canon) :
    let area := layout destination.width element
    ValueEntriesReplay profile ready bindings destination inst compare element entries index pointer output checkNext canonNext next
      { checked with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
      { canonical with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer .value >>= canonNext) }
      check canon := by
  intro area
  let lhs := { checked with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
  let rhs := { canonical with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer .value >>= canonNext) }
  let checkPublish := publishChecked destination inst pointer entries.length index output checkNext
  let canonPublish := publishCanonical destination inst pointer entries.length output canonNext
  have frame : ChildFrameOver older lhs rhs check canon :=
    ⟨region.frame.store, region.frame.pending, region.frame.results, region.frame.cancels, region.frame.blocked,
      region.frame.thread, region.frame.frames, region.frame.rest⟩
  unfold ValueEntriesReplay
  refine replay (origin := checked.store) (.elements area.size) destination inst entries 0 pointer _ checkPublish canonPublish _
    frame (Core3.Grows.refl _) region.width (elementSlots destination.width matched region.aligned region.bounds _ children) ?_ ?_ ?_
  · intro reached reference check canon paired grown checkAt canonAt
    obtain ⟨store, result, labels, observed, lhsRun, rhsRun, tracked⟩ :=
      collection_descriptor_cut (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
        (destination.context inst) destination.width output pointer entries.length reached reference check canon
        (fun value => checkNext (.ok value)) canonNext paired.store checkAt canonAt
    refine ⟨store, result, labels, observed, lhsRun, rhsRun, ?_⟩
    intro value returned
    subst result
    refine ⟨fun depth => (tracked value rfl depth).1, fun depth => (tracked value rfl depth).2, ?_⟩
    exact ends value _ _ _ _
      ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩
      (region.growth.trans (grown.trans lhsRun.grows)) rfl rfl
  · change check.control ((checkedCollectionTail destination inst entries area index output pointer (.ok ())).bind checkNext) = _
    congr 1
    simp only [checkedCollectionTail, Track.checked, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext verdict
    cases verdict with
    | error issue => rfl
    | ok value => cases value; simp only [Prog.bind_assoc]; rfl
  · change canon.control ((canonicalCollectionTail destination inst entries area output pointer .value).bind canonNext) = _
    simp only [canonicalCollectionTail, Track.canonical, Prog.bind_eq, Prog.bind_assoc]
    rfl

theorem valueCollectionReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (depth index : Nat) (output : Lower.Output) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (valueMode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (matched : Field.EntriesMatch entries element)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (shape : ∀ item ∈ entries, AggregateShape (StringField.Fits destination) depth item)
    (replay : CollectionReplay profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext
      (ValueListReturn profile ready bindings older destination inst type element entries depth index output checkNext canonNext) := by
  obtain ⟨checkInstall, canonInstall, continueRun⟩ := replay
  refine ⟨checkInstall, canonInstall, ?_⟩
  intro last seen protectedReturn path covers
  obtain ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, cut⟩ :=
    continueRun path covers
  refine ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, ?_⟩
  intro pointer cursor reached atReturn
  unfold ValueListReturn
  refine (cut pointer cursor reached atReturn).visit_collection destination inst type (layout destination.width element) entries
    index pointer output checkNext canonNext _ ?_
  intro bytes reference canon region
  rw [valueMode]
  refine valueTailWith destination inst element entries index pointer _ output checkNext canonNext _ region matched ?_
    (fun _ _ _ _ _ frame growth checked canonical => ⟨frame, growth, checked, canonical⟩)
  intro item member address fits
  have found := entries_match_of_mem matched member
  exact nestedRule destination inst depth item address region.width region.sized realloc (shape item member)
    (found.type_eq.symm ▸ found) fits

theorem recursiveValueReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (index : Nat) (output : Lower.Output) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (compare : FieldComparison grow sig) (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output) (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (matched : Field.EntriesMatch entries element)
    (children : ∀ (atStore : CStore (core3 grow)) bytes,
      (core3 grow).memAddrType? atStore.core destination.memory = some destination.width →
      (core3 grow).memSize? atStore.core destination.memory = some bytes →
      ∀ item ∈ entries, ∀ address, SlotFits destination.width bytes item address →
        FieldRule compare older atStore destination inst item address)
    (ends : ∀ value reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows left.store.core reached.store.core → reached.ctl = check.control (checkNext (.ok value)) →
      reference.ctl = canon.control (canonNext value) → finish value reached reference check canon)
    (replay : CollectionReplay profile ready bindings older destination inst type element entries index output
      left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst type element entries index output
      left right check canon checkNext canonNext
      (RecursiveValueReturn profile ready bindings older destination inst compare type element entries index output checkNext canonNext finish) := by
  obtain ⟨checkInstall, canonInstall, continueRun⟩ := replay
  refine ⟨checkInstall, canonInstall, ?_⟩
  intro last seen protectedReturn path covers
  obtain ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, cut⟩ :=
    continueRun path covers
  refine ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, ?_⟩
  intro pointer cursor reached atReturn
  unfold RecursiveValueReturn
  refine (cut pointer cursor reached atReturn).visit_collection destination inst type (layout destination.width element)
    entries index pointer output checkNext canonNext _ ?_
  intro bytes reference canon region
  rw [mode]
  exact valueTailWith destination inst element entries index pointer compare output checkNext canonNext finish region matched
    (children _ _ region.width region.sized) ends

private theorem mapEntriesReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (entries : List Field) (index cursor : Nat) (compare : FieldComparison grow sig)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (slots : let stride := (layout destination.width (.record (mapEntryFields key element))).size
      (Track.elements stride).Slots destination.width (SlotFits destination.width bytes) entries cursor)
    (children : ∀ entry ∈ entries, ∃ keyField valueField, entry = .aggregate (.record (mapEntryFields key element)) [keyField, valueField] ∧
      ∀ item ∈ [keyField, valueField], ∀ address, SlotFits destination.width bytes item address →
        FieldRule compare older origin destination inst item address)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (Track.checked (.elements (layout destination.width (.record (mapEntryFields key element))).size)
      destination inst entries index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mapTail destination inst key element entries cursor >>= canonNext)) :
    MapEntriesReplay profile ready bindings destination inst compare key element checkNext canonNext finish entries index cursor left right check canon := by
  induction entries generalizing index cursor left right check canon with
  | nil =>
    apply ends left right check canon frame growth
    · simpa only [Track.checked, Record.Effects.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using checkAt
    · simpa only [mapTail, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using canonAt
  | cons entry rest ih =>
    cases matched with
    | cons entryLayout restLayout =>
      obtain ⟨keyField, valueField, equal, pairRules⟩ := children entry (List.mem_cons_self ..)
      subst entry
      let type : TypeOf := .record (mapEntryFields key element)
      let stride := (layout destination.width type).size
      let fields := [keyField, valueField]
      let nextCheck := checkTail (.elements stride) destination inst rest (index + 1) (cursor + stride) checkNext
      let nextCanon : CanonNext grow sig := fun () => mapTail destination inst key element rest (cursor + stride) >>= canonNext
      let entered := enterAggregate destination inst fields index cursor left check nextCheck
      change SlotFits destination.width bytes (.aggregate type fields) cursor ∧
        (Track.elements stride).Slots destination.width (SlotFits destination.width bytes) rest (cursor + stride) at slots
      have guardAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width (.aggregate type fields) index (.memory cursor) >>= nextCheck) := by
        rw [checkAt]
        congr 1
        simp only [Track.checked, Record.Effects.elements, Prog.bind_eq, Prog.bind_assoc]
        congr 1
        funext verdict
        cases verdict with
        | error issue => rfl
        | ok value => cases value; rfl
      have guard := aggregateEntry (profile := profile) (ready := ready) (bindings := bindings)
        destination inst type fields index cursor left check nextCheck growth sized slots.1.1 slots.1.2 guardAt
      have refAt : right.ctl = canon.control (Track.canonical .placedFields destination inst fields cursor >>= nextCanon) := by
        rw [canonAt]
        simp only [Track.canonical, mapTail, fields, canonicalPlacedFields, Track.slot, nextCanon,
          CanonicalTree.elements, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
        let cx := destination.context (grow := grow) inst
        let keySlot := Track.placedFields.slot destination.width keyField cursor
        let valueSlot := Track.placedFields.slot destination.width valueField keySlot.2
        let keyWrite : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory keySlot.1)
        let valueWrite : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width valueField (.memory valueSlot.1)
        let tail : Session grow sig Unit := mapTail destination inst key element rest (cursor + stride)
        change canon.control ((keyWrite.bind fun () => valueWrite.bind fun () => tail).bind canonNext) =
          canon.control (keyWrite.bind fun () => valueWrite.bind fun () => tail.bind canonNext)
        simp only [Prog.bind_assoc]
      refine ⟨keyField, valueField, rfl, guard, replay (older := older) .placedFields destination inst fields 0 cursor compare
        (aggregateNext index nextCheck) nextCanon _ ?_ growth present ?_ ?_ rfl refAt⟩
      · exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      · exact aggregateSlots destination.width entryLayout slots.1.1 slots.1.2 _ pairRules
      · intro reached reference check canon frame grown checkCont canonCont
        exact ih (index + 1) (cursor + stride) frame grown restLayout slots.2
          (fun item member => children item (List.mem_cons_of_mem _ member)) checkCont canonCont

private theorem mapReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entries : List Field)
    (index address : Nat) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig)
    (finish : Finish grow sig) (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (children : ∀ (atStore : CStore (core3 grow)) bytes,
      (core3 grow).memAddrType? atStore.core destination.memory = some destination.width →
      (core3 grow).memSize? atStore.core destination.memory = some bytes →
      ∀ entry ∈ entries, ∃ keyField valueField, entry = .aggregate (.record (mapEntryFields key element)) [keyField, valueField] ∧
        ∀ item ∈ [keyField, valueField], ∀ address, SlotFits destination.width bytes item address →
          FieldRule compare older atStore destination inst item address)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows left.store.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (replay : CollectionReplay profile ready bindings older destination inst (.map key element)
      (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst (.map key element) (.record (mapEntryFields key element))
      entries index (.memory address) left right check canon checkNext canonNext
      (MapReturn profile ready bindings older destination inst compare key element entries index address checkNext canonNext finish) := by
  obtain ⟨checkInstall, canonInstall, continueRun⟩ := replay
  refine ⟨checkInstall, canonInstall, ?_⟩
  intro last seen protectedReturn path covers
  obtain ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, cut⟩ :=
    continueRun path covers
  refine ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, checkTrail, canonTrail, ?_⟩
  intro pointer cursor reached atReturn
  unfold MapReturn
  let output := Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Output.memory address
  let area := layout destination.width (.record (mapEntryFields key element))
  refine (cut pointer cursor reached atReturn).visit_collection destination inst (.map key element) area entries
    index pointer output checkNext canonNext _ ?_
  intro bytes reference canon region
  let lhs := { last with ctl := cursor.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
  let rhs := { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
    (.memoryMap destination.width key element) >>= canonNext) }
  let checkPublish := publishChecked destination inst pointer entries.length index output checkNext
  let canonPublish := publishCanonical destination inst pointer entries.length output canonNext
  have frame : ChildFrameOver older lhs rhs cursor canon :=
    ⟨region.frame.store, region.frame.pending, region.frame.results, region.frame.cancels, region.frame.blocked,
      region.frame.thread, region.frame.frames, region.frame.rest⟩
  refine mapEntriesReplay destination inst key element entries 0 pointer compare checkPublish canonPublish _ frame
    (Core3.Grows.refl _) region.width region.sized matched
    (elementSlots destination.width matched region.aligned region.bounds _ (fun _ _ _ fit => fit))
    (children _ _ region.width region.sized) ?_ ?_ ?_
  · intro reached reference check canon paired grown checkAt canonAt
    obtain ⟨store, result, labels, observed, lhsRun, rhsRun, tracked⟩ :=
      collection_descriptor_cut (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
        (destination.context inst) destination.width output pointer entries.length reached reference check canon
        (fun value => checkNext (.ok value)) canonNext paired.store checkAt canonAt
    refine ⟨store, result, labels, observed, lhsRun, rhsRun, ?_⟩
    intro value returned
    subst result
    refine ⟨fun depth => (tracked value rfl depth).1, fun depth => (tracked value rfl depth).2, ?_⟩
    cases value
    exact ends _ _ _ _
      ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩
      (region.growth.trans (grown.trans lhsRun.grows)) rfl rfl
  · let body : Session grow sig (Except RecordLower.Issue Unit) := Track.checked (.elements area.size) destination inst entries 0 pointer
    let desc : Session grow sig Unit := ListLower.publish (destination.context (grow := grow) inst) destination.width pointer entries.length output
    change cursor.control ((body.bind fun result => match result with
      | .error issue => Prog.pure (.error (.nested index issue))
      | .ok () => desc.bind fun value => Prog.pure (.ok value)).bind checkNext) =
      cursor.control (body.bind checkPublish)
    rw [Prog.bind_assoc]
    apply congrArg cursor.control
    congr 1
    funext verdict
    cases verdict with
    | error issue => rfl
    | ok value => cases value; simp only [Prog.bind_assoc]; rfl
  · let body := mapTail (grow := grow) (sig := sig) destination inst key element entries pointer
    let desc : Session grow sig Unit := ListLower.publish (destination.context (grow := grow) inst) destination.width pointer entries.length output
    change canon.control ((body.bind fun () => desc).bind canonNext) = canon.control (body.bind canonPublish)
    rw [Prog.bind_assoc]
    rfl

private theorem scalarRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload type)
    (data : LocalDataType type) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (placementFits : SlotFits destination.width bytes (.data type payload) address) :
    FieldRule (memoryLeaf profile ready bindings older destination inst) older origin destination inst (.data type payload) address := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  obtain ⟨reachedBytes, reachedSize, widened⟩ := growth.memSize sized
  change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at reachedSize
  have aligned : address % (layout destination.width type).alignment.bytes = 0 := placementFits.1
  have bounds : address + (layout destination.width type).size ≤ reachedBytes := placementFits.2.trans widened
  have placed : rootPlacement destination left.store type (.memory address) = .ok () := by
    simp [rootPlacement, placement, aligned, reachedSize, Nat.not_lt.mpr bounds]
    rfl
  have reachedWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width := growth.memAddrType present
  have width : ptrTypeIn left.store (destination.context inst) = destination.width := by
    simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth]
  have cut := local_data_leaf_frame (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
    destination inst type data payload index (.memory address) origin left right (frame.store ▸ growth) width placed
    frame.store check canon frame.thread checkNext canonNext checkAt canonAt
  obtain ⟨store, result, chk, ref, checkRun, canonRun, labels, status⟩ := cut
  refine .inr ⟨⟨type, payload, rfl, data⟩, store, result, chk, ref, checkRun, canonRun, labels, ?_⟩
  cases result with
  | ok value =>
    exact ⟨status.2.1, status.2.2,
      ends _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ status.1 rfl rfl⟩
  | error _ => exact status

private theorem layoutCaseMap (width : AddrType) (cases : List (String × Option TypeOf)) :
    layoutCases width cases = (cases.map Prod.snd).map (layoutOption width) := by
  induction cases with
  | nil => rw [layoutCases]; rfl
  | cons head rest ih => cases head; rw [layoutCases, List.map_cons, List.map_cons, ih]

private theorem selectedLayout (width : AddrType) {type : TypeOf} {arms : List (Option TypeOf)} {tag : Nat} {item : Field}
    (matched : Field.LayoutMatches (.sum type arms tag (some item)) type) :
    layout width type = variantLayout (arms.map (layoutOption width)) ∧
      some (layout width item.type) ∈ arms.map (layoutOption width) ∧ item.LayoutMatches item.type := by
  cases matched with
  | variant atTag arm =>
    cases arm with
    | some matchArm =>
      refine ⟨by rw [layout, layoutCaseMap], ?_, matchArm.type_eq.symm ▸ matchArm⟩
      exact List.mem_map.mpr ⟨_, List.mem_of_getElem? atTag, by rw [matchArm.type_eq, layoutOption]⟩
  | optionSome matchArm =>
    refine ⟨by simp only [layout, List.map_cons, List.map_nil, layoutOption], ?_, matchArm.type_eq.symm ▸ matchArm⟩
    rw [matchArm.type_eq]
    simp [layoutOption]
  | resultOk arm =>
    cases arm with
    | some matchArm =>
      refine ⟨by simp only [layout, List.map_cons, List.map_nil], ?_, matchArm.type_eq.symm ▸ matchArm⟩
      rw [matchArm.type_eq]
      simp [layoutOption]
  | resultError arm =>
    cases arm with
    | some matchArm =>
      refine ⟨by simp only [layout, List.map_cons, List.map_nil], ?_, matchArm.type_eq.symm ▸ matchArm⟩
      rw [matchArm.type_eq]
      simp [layoutOption]

theorem listTreeRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field) (address : Nat)
    {origin : CStore (core3 grow)}
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (allocator : Field.AllocatorFor destination.realloc item)
    (shape : ListTreeShape (StringField.Fits destination) depth item)
    (matched : item.LayoutMatches item.type) (placement : SlotFits destination.width bytes item address) :
    FieldRule (listTree profile ready bindings older destination inst depth) older origin destination inst item address := by
  induction depth generalizing item origin bytes address with
  | zero =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
    cases shape with
    | handle handle =>
      exact .inl (mixedRule destination inst item address present sized (allocator item (.self item)) (.inl handle)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | string fit =>
      exact .inl (mixedRule destination inst item address present sized (allocator item (.self item)) (.inr ⟨fit, placement⟩)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | scalar payload nonString =>
      exact scalarRule destination inst _ payload nonString address present sized placement
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  | succ depth ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
    cases shape with
    | handle handle =>
      exact .inl (.inl (mixedRule destination inst item address present sized (allocator item (.self item)) (.inl handle)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends))
    | string fit =>
      exact .inl (.inl (mixedRule destination inst item address present sized (allocator item (.self item)) (.inr ⟨fit, placement⟩)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends))
    | scalar payload nonString =>
      exact .inl (scalarRule destination inst _ payload nonString address present sized placement
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | @aggregate _ type children child =>
      refine .inr (.inl ⟨type, children, rfl, aggregateReplay destination inst type children index address _
        checkNext canonNext finish frame growth present sized matched placement.1 placement.2 ?_ ends checkAt canonAt⟩)
      exact fun entry member slot fits => ih entry slot present sized
        (fun leaf path => allocator leaf (.aggregate member path)) (child entry member) (matchedAggregateChild matched member) fits
    | @list _ element entries child =>
      have matching : Field.EntriesMatch entries element := by cases matched with | list matchEntries => exact matchEntries
      refine .inr (.inr (.inl ⟨element, entries, rfl, ?_⟩))
      cases prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) with
      | error issue =>
        exact dynamic_refused_before_allocation destination inst (.list element) element entries (.memory address) index
          left right check canon checkNext canonNext frame.store issue prepared checkAt
      | ok result =>
        cases result
        obtain ⟨reachedBytes, reachedSize, _⟩ := growth.memSize sized
        refine recursiveValueReplay destination inst (.list element) element entries index (.memory address) _
          checkNext canonNext _ rfl matching ?_ ?_
          (frame.collection_replay destination inst (.list element) element entries index (.memory address) checkNext canonNext
            (growth.memAddrType present) reachedSize prepared checkAt canonAt)
        · intro reached bytes reachedWidth reachedSize entry member slot fits
          have layoutAt := entries_match_of_mem matching member
          exact ih entry slot reachedWidth reachedSize (fun leaf path => allocator leaf (.dynamic member path))
            (child entry member) (layoutAt.type_eq.symm ▸ layoutAt) fits
        · intro value reached reference check canon paired grown atCheck atCanon
          cases value
          exact ends _ _ _ _ paired (growth.trans grown) atCheck atCanon
    | @map _ key element entries records child =>
      let type : TypeOf := .record (mapEntryFields key element)
      have matching : Field.EntriesMatch entries type := by cases matched with | map matchEntries => exact matchEntries
      refine .inr (.inr (.inr (.inl ⟨key, element, entries, rfl, ?_⟩)))
      cases prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) with
      | error issue =>
        exact dynamic_refused_before_allocation destination inst (.map key element) type entries (.memory address) index
          left right check canon checkNext canonNext frame.store issue prepared checkAt
      | ok result =>
        cases result
        obtain ⟨reachedBytes, reachedSize, _⟩ := growth.memSize sized
        refine mapReplay destination inst key element entries index address _ checkNext canonNext finish matching ?_ ?_
          (frame.collection_replay destination inst (.map key element) type entries index (.memory address) checkNext canonNext
            (growth.memAddrType present) reachedSize prepared checkAt canonAt)
        · intro reached bytes reachedWidth reachedSize entry member
          obtain ⟨fields, rfl⟩ := records entry member
          have shapeAt := child _ member fields rfl
          have layoutAt := entries_match_of_mem matching member
          rcases map_entry_layout (key := key) (element := element) layoutAt with ⟨keyField, valueField, equal, _, _⟩ | ⟨_, equal⟩
          · cases equal
            refine ⟨keyField, valueField, rfl, ?_⟩
            intro item inPair address fits
            exact ih item address reachedWidth reachedSize (fun leaf path => allocator leaf (.dynamic member (.aggregate inPair path)))
              (shapeAt item inPair) (matchedAggregateChild layoutAt inPair) fits
          · cases equal
        · exact fun _ _ _ _ paired grown atCheck atCanon => ends _ _ _ _ paired (growth.trans grown) atCheck atCanon
    | @sum _ type arms tag selected child =>
      refine .inr (.inr (.inr (.inr (.inl ⟨type, arms, tag, selected, rfl, ?_⟩))))
      have reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width :=
        frame.store ▸ growth.memAddrType present
      have width : ptrTypeIn right.store (destination.context inst) = destination.width := by
        simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth]
      obtain ⟨store, result, chk, ref, runChk, runRef, labels, status⟩ :=
        memory_sum_tag (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
          destination inst type arms tag index address selected origin left right check canon checkNext canonNext
          frame.store frame.thread width (frame.store ▸ growth) checkAt canonAt
      refine ⟨store, result, chk, ref, runChk, runRef, labels, ?_⟩
      cases result with
      | error _ => exact status
      | ok value =>
        cases value
        refine ⟨status.2.1, status.2.2, ?_⟩
        cases selected with
        | none =>
          exact ends _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ status.1 rfl rfl
        | some item =>
          let addressAt := sumPayloadAddress destination.width arms address
          obtain ⟨area, member, matchChild⟩ := selectedLayout destination.width matched
          have aligned : (variantLayout (arms.map (layoutOption destination.width))).alignment.bytes ∣ address := by
            rw [← area]
            exact Nat.dvd_of_mod_eq_zero placement.1
          obtain ⟨alignedAt, boundsAt⟩ := variantLayout_payload_fits _ address (layout destination.width item.type) aligned member
          have bounds : address + (variantLayout (arms.map (layoutOption destination.width))).size ≤ bytes := by
            rw [← area]
            exact placement.2
          have fits : SlotFits destination.width bytes item addressAt := by
            rw [List.length_map] at alignedAt boundsAt
            exact ⟨alignedAt, boundsAt.trans bounds⟩
          let entered := localLeafEnd left left.host store check.thread check.frames check.rest
            (sumCheckedNext destination inst (some item) index addressAt checkNext) (.ok ())
          let reference := localLeafEnd right right.host store canon.thread canon.frames canon.rest
            (sumCanonicalNext destination inst (some item) addressAt canonNext) (.ok ())
          exact ih item addressAt present sized (fun leaf path => allocator leaf (.sum path))
            (child item rfl) matchChild fits 0 (aggregateNext index checkNext) canonNext
            entered reference check canon ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
            status.1 rfl rfl finish (fun _ _ _ _ frame grew checkAt canonAt => ends _ _ _ _ frame grew checkAt canonAt)
    | @fixed _ element length entries child =>
      obtain ⟨count, entriesMatch⟩ : entries.length = length ∧ Field.EntriesMatch entries element := by
        cases matched with | fixed count matchItems => exact ⟨count, matchItems⟩
      let area := layout destination.width element
      let mode := Track.elements area.size
      let cx := destination.context (grow := grow) inst
      let canonBody := fun reached => CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries .value
        (layout reached element).size address >>= canonNext
      have canonRead : right.ctl = canon.control (ptrType cx >>= canonBody) := by
        rw [canonAt, CanonicalTree.field]
        let body : AddrType → Session grow sig Unit := fun reached => CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries .value
          (layout reached element).size address
        change canon.control (((ptrType cx).bind body).bind canonNext) = _
        rw [Prog.bind_assoc]
        rfl
      have width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width :=
        frame.store ▸ growth.memAddrType present
      have read := (CoreGrowthSteps.refl (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings)) right).read_width
        cx rfl width canonBody canonRead
      refine .inr (.inr (.inr (.inr (.inr ⟨element, length, entries, rfl, read.steps, ?_⟩))))
      have alignMod := placement.1
      change address % (layout destination.width (.fixedList element length)).alignment.bytes = 0 at alignMod
      rw [layout] at alignMod
      have aligned : address = alignTo address area.alignment := by
        change address % area.alignment.bytes = 0 at alignMod
        cases reached : area.alignment <;> simp only [alignTo, reached, Alignment.bytes] at alignMod ⊢ <;> omega
      have bounds := placement.2
      change address + (layout destination.width (.fixedList element length)).size ≤ bytes at bounds
      rw [layout, ← count] at bounds
      have placed : address + entries.length * area.size ≤ bytes := by
        simpa only [area, Layout.size, Nat.mul_assoc] using bounds
      refine replay (older := older) mode destination inst entries 0 address _ (aggregateNext index checkNext) canonNext finish
        ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        growth present (elementSlots destination.width entriesMatch aligned placed _ ?_) ends ?_ rfl
      · intro item member slot fits
        have layoutAt := entries_match_of_mem entriesMatch member
        exact ih item slot present sized (fun leaf path => allocator leaf (.fixed member path))
          (child item member) (layoutAt.type_eq.symm ▸ layoutAt) fits
      · rw [checkAt, Record.Effects.field]
        let body : Session grow sig (Except RecordLower.Issue Unit) :=
          mode.checked destination inst entries 0 address
        change check.control ((body.bind fun verdict => Prog.pure (verdict.mapError (.nested index))).bind checkNext) = _
        rw [Prog.bind_assoc]
        rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence
