module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Derive the canonical field addresses from the compiled record or tuple
layout, not from assumptions about the bytes that a callback can change. -/
theorem Track.fields_slots (width : AddrType) {type : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.LayoutMatches (.aggregate type items) type)
    (aligned : base % (layout width type).alignment.bytes = 0) (bounds : base + (layout width type).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    Track.fields.Slots width rule items base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.aggregateSlots width matched aligned bounds rule child

/-- Derive all strided entry slots from the actual validated array range and
the compiler's entry layouts, including empty arrays and zero-sized slots. -/
theorem Track.elements_slots (width : AddrType) {element : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.EntriesMatch items element) (aligned : base = alignTo base (layout width element).alignment)
    (bounds : base + items.length * (layout width element).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    (Track.elements (layout width element).size).Slots width rule items base :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.elementSlots width matched aligned bounds rule child

/-- Traverse both actual memory sequences. Record/tuple reads are taken in
the reached store and element slots keep their validated stride. The rule
for the next sibling applies only on the preceding child's common return. -/
theorem sequence_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
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
    Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.replay
    mode destination inst items index cursor compare checkNext canonNext finish frame growth present slots ends checkAt canonAt

/-- Instantiate the traversal with actual allocating strings and live handles
in placed slots. Bounds transfer by reached Core growth, not byte stability. -/
theorem mixed_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (slots : mode.Slots destination.width (MixedSlot destination bytes) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst (mixed profile ready bindings older destination inst)
      checkNext canonNext finish items index cursor left right check canon :=
  sequence_replay mode destination inst items index cursor _ checkNext canonNext finish frame growth present
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.slotsMap mode destination.width
      (fun item address slot => Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.mixedRule
        destination inst item address present sized (fun _ => ⟨_, realloc⟩) slot) items cursor slots) ends checkAt canonAt

/-- Execute the checked aggregate guard at the reached memory size, then
compare the actual record or tuple child programs under the same saved frames.
Only successful child traversal reaches the aggregate's outer continuation. -/
theorem aggregate_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
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
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left [.tau]
      (enterAggregate destination inst items index address left check checkNext) ∧
      Replay profile ready bindings .fields destination inst compare (aggregateNext index checkNext) canonNext finish
        items 0 address (enterAggregate destination inst items index address left check checkNext) right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.aggregateReplay
    destination inst type items index address compare checkNext canonNext finish frame growth present sized matched aligned bounds child ends checkAt canonAt

/-- Structural comparison for nested memory records and tuples with string
and handle leaves. Derives every child rule from placement and the shape
certificate; it does not take child equivalence or allocator liveness as a
premise. Pending allocator occurrences keep the actual nested continuations. -/
theorem nested_rule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (shape : AggregateShape (StringField.Fits destination) depth item) (matched : item.LayoutMatches item.type)
    (placement : SlotFits destination.width bytes item address) :
    FieldRule (nested profile ready bindings older destination inst depth) older origin destination inst item address :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.nestedRule
    destination inst depth item address present sized realloc shape matched placement

/-- Replay the marked allocator's return into all value-mode entries, with
allocating string/handle aggregates at any entry, then compare the actual
pointer/count descriptor. A stopped or trapped prefix runs no unvisited
entries. This applies to lists and value-mode maps, not indirect maps. -/
theorem value_entries_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (depth index : Nat) (output : Lower.Output) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (valueMode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (matched : Field.EntriesMatch entries element)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (shape : ∀ item ∈ entries, AggregateShape (StringField.Fits destination) depth item)
    (replay : CollectionReplay profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext
      (ValueListReturn profile ready bindings older destination inst type element entries depth index output checkNext canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.valueCollectionReplay
    destination inst type element entries depth index output checkNext canonNext valueMode matched realloc shape replay

theorem recursive_value_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
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
      (RecursiveValueReturn profile ready bindings older destination inst compare type element entries index output checkNext canonNext finish) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.recursiveValueReplay
    destination inst type element entries index output compare checkNext canonNext finish mode matched children ends replay

theorem list_tree_rule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field) (address : Nat)
    {origin : CStore (core3 grow)}
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (allocator : Field.AllocatorFor destination.realloc item)
    (shape : ListTreeShape (StringField.Fits destination) depth item)
    (matched : item.LayoutMatches item.type) (placement : SlotFits destination.width bytes item address) :
    FieldRule (listTree profile ready bindings older destination inst depth) older origin destination inst item address :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.listTreeRule
    destination inst depth item address present sized allocator shape matched placement

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
