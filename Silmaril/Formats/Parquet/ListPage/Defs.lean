module

public import Silmaril.Formats.Parquet.FlatPage.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.Plain.Defs

/-! One complete V1 page for the canonical nullable LIST of nullable INT32. -/

public section

namespace Silmaril.Formats.Parquet.ListPage

abbrev Row := Option (List (Option Int32))

inductive Event where
  | nullList
  | emptyList
  | first (item : Option Int32)
  | next (item : Option Int32)
  deriving DecidableEq, Repr

@[expose] def Event.wire : Event → Nat × Nat × Option Int32
  | .nullList => (0, 0, none)
  | .emptyList => (0, 1, none)
  | .first item => (0, if item.isSome then 3 else 2, item)
  | .next item => (1, if item.isSome then 3 else 2, item)

inductive Error where
  | codec (actual : Int)
  | pageKind
  | crc
  | encoding
  | bodySize
  | bodyLimit
  | rowLimit
  | repetitionSection (cause : FlatPage.Error)
  | definitionSection (cause : FlatPage.Error)
  | repetition (cause : Hybrid.Error)
  | definition (cause : Hybrid.Error)
  | plain (cause : Plain.Error)
  | reconstruct (cause : FlatPage.Error)
  | levelPair
  | continuationWithoutList
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

private def eventFor (entry : Nat × Nat × Option Int32) : Event :=
  let (rep, defn, item) := entry
  if rep = 0 then
    if defn = 0 then Event.nullList else if defn = 1 then .emptyList else .first item
  else .next item

def readEvent (entry : Nat × Nat × Option Int32) : Except Error Event :=
  let event := eventFor entry
  if event.wire = entry then .ok event else .error .levelPair

@[expose] def rowEvents : Row → List Event
  | none => [.nullList]
  | some [] => [.emptyList]
  | some (item :: rest) => .first item :: rest.map Event.next

/-- Group reconstruction state. An open list has a first element, which
may be null. Both accumulators are reversed for constant-time appends. -/
structure State where
  active : Option (Option Int32 × List (Option Int32))
  closed : List Row

@[expose] def State.empty : State := ⟨none, []⟩

private def State.flush (state : State) : List Row :=
  match state.active with
  | none => state.closed
  | some (item, reverseTail) => some (item :: reverseTail.reverse) :: state.closed

/-- Finish at the group boundary, closing the final open list. -/
def State.finish (state : State) : List Row := state.flush.reverse

private def State.step (state : State) : Event → Except Error State
  | .nullList => .ok ⟨none, none :: state.flush⟩
  | .emptyList => .ok ⟨none, some [] :: state.flush⟩
  | .first item => .ok ⟨some (item, []), state.flush⟩
  | .next item =>
    match state.active with
    | none => .error .continuationWithoutList
    | some (head, reverseTail) => .ok { state with active := some (head, item :: reverseTail) }

/-- Feed a page's ordered events without closing the last list. A continuation
requires a nonempty list still open in this page or the preceding page. -/
def State.feed (state : State) (events : List Event) : Except Error State :=
  events.foldlM State.step state

/-- Whole-page reconstruction starts at a row boundary and closes its final row. -/
def reconstruct (events : List Event) : Except Error (List Row) :=
  (State.empty.feed events).map State.finish

structure Limits where
  maxBodyBytes : Nat := 16 * 1024 * 1024
  maxRows : Nat := 1024 * 1024
  levels : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩

@[expose] def valueMask (definitions : List Nat) : List Bool :=
  definitions.map (· == 3)

/-- Decode the exact level streams, then use the selected scalar reader for
precisely the present INT32 values. -/
def decodeSectionsUsing {ε : Type} (wrap : Error → ε) (readValues : Nat → Bytes → Except ε (List Int32))
    (limits : Limits) (slots : Nat) (repetition definition scalars : Bytes) : Except ε (List Event) := do
  let reps ← (Hybrid.decode 1 slots limits.levels repetition).mapError (wrap ∘ .repetition)
  let defs ← (Hybrid.decode 2 slots limits.levels definition).mapError (wrap ∘ .definition)
  let mask := valueMask defs
  let values ← readValues (mask.count true) scalars
  let entries ← (FlatPage.reconstruct mask values).mapError (wrap ∘ .reconstruct)
  ((reps.zip (defs.zip entries)).mapM readEvent).mapError wrap

def readPlain (count : Nat) (source : Bytes) : Except Error (List Int32) :=
  (Plain.decodeInt32 count source).mapError .plain

/-- Decode separately bounded level streams and the exact PLAIN value suffix. -/
def decodeSections (limits : Limits) (slots : Nat) (repetition definition scalars : Bytes) :
    Except Error (List Event) :=
  decodeSectionsUsing id readPlain limits slots repetition definition scalars

/-- Read the two exact V1 level extents and give the selected reader their
untouched value suffix. -/
def decodeEventsUsing {ε : Type} (wrap : Error → ε) (readValues : Nat → Bytes → Except ε (List Int32))
    (limits : Limits) (slots : Nat) (body : Bytes) : Except ε (List Event) := do
  if limits.maxBodyBytes < body.length then return ← throw (wrap .bodyLimit)
  let first ← (FlatPage.splitV1Optional limits.levels.bytes body).mapError (wrap ∘ .repetitionSection)
  let second ← (FlatPage.splitV1Optional limits.levels.bytes first.scalars).mapError (wrap ∘ .definitionSection)
  decodeSectionsUsing wrap readValues limits slots first.definitions second.definitions second.scalars

/-- Read the exact V1 level streams and PLAIN values at this page's slot count. -/
def decodeEvents (limits : Limits) (slots : Nat) (body : Bytes) : Except Error (List Event) :=
  decodeEventsUsing id readPlain limits slots body

/-- Standalone page profile, with the original body-limit and row-limit precedence. -/
def decodeBody (limits : Limits) (expectedRows slots : Nat) (body : Bytes) :
    Except Error (List Row) := do
  if limits.maxBodyBytes < body.length then return ← throw .bodyLimit
  if limits.maxRows < expectedRows then return ← throw .rowLimit
  let events ← decodeEvents limits slots body
  let rows ← reconstruct events
  if rows.length ≠ expectedRows then return ← throw (.rowCount expectedRows rows.length)
  pure rows

/-- Check the header shared by the standalone and continued V1 profiles. -/
def checkV1 (codec : Int) (header : Page.Header) (body : Bytes) : Except Error Page.DataV1 := do
  if codec ≠ 0 then return ← throw (.codec codec)
  let .dataV1 info := header.kind | throw .pageKind
  if header.crc.isSome then return ← throw .crc
  if ¬ (info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3) then
    return ← throw .encoding
  if ¬ (header.compressedSize = body.length ∧ header.uncompressedSize = body.length) then
    return ← throw .bodySize
  pure info

/-- Decode the exact V1 bytes of one frame without assuming a row boundary. -/
def decodeV1Events (limits : Limits) (codec : Int) (header : Page.Header)
    (body : Bytes) : Except Error (List Event) := do
  let info ← checkV1 codec header body
  decodeEvents limits info.numValues body

/-- The caller supplies a matching header and body, a checked canonical LIST
schema and the expected number of complete rows. No partial row is supported. -/
def decodeV1 (limits : Limits) (codec : Int) (header : Page.Header) (expectedRows : Nat)
    (body : Bytes) : Except Error (List Row) := do
  let info ← checkV1 codec header body
  decodeBody limits expectedRows info.numValues body

structure SectionsWireUsing {ε : Type} (readValues : Nat → Bytes → Except ε (List Int32))
    (slots : Nat) (repetition definition scalars : Bytes) (events : List Event) : Prop where
  slotCount : events.length = slots
  data : ∃ (reps defs : List Nat) (values : List Int32) (entries : List (Option Int32)),
    Hybrid.Wire 1 slots repetition.toList reps ∧ Hybrid.Wire 2 slots definition.toList defs ∧
    reps.length = slots ∧ defs.length = slots ∧ entries.length = slots ∧
    readValues ((valueMask defs).count true) scalars = .ok values ∧
    entries.map Option.isSome = valueMask defs ∧ entries.filterMap id = values ∧
    events.map Event.wire = reps.zip (defs.zip entries)

structure EventsWireUsing {ε : Type} (readValues : Nat → Bytes → Except ε (List Int32))
    (limits : Limits) (slots : Nat) (body : Bytes) (events : List Event) : Prop where
  cap : body.length ≤ limits.maxBodyBytes
  data : ∃ (repLength defLength : List UInt8) (reps defs scalars : Bytes),
    repLength.length = 4 ∧ defLength.length = 4 ∧
    KBytes.leVal repLength = reps.length ∧ KBytes.leVal defLength = defs.length ∧
    body.toList = repLength ++ reps.toList ++ defLength ++ defs.toList ++ scalars.toList ∧
    SectionsWireUsing readValues slots reps defs scalars events

/-- Exact ordered slot triples for already separated level and value streams. -/
structure SectionsWire (slots : Nat) (repetition definition scalars : Bytes) (events : List Event) : Prop where
  slotCount : events.length = slots
  data : ∃ (reps defs : List Nat) (values : List Int32) (entries : List (Option Int32)),
    Hybrid.Wire 1 slots repetition.toList reps ∧ Hybrid.Wire 2 slots definition.toList defs ∧
    reps.length = slots ∧ defs.length = slots ∧ entries.length = slots ∧
    Plain.decodeInt32 ((valueMask defs).count true) scalars = .ok values ∧
    entries.map Option.isSome = valueMask defs ∧ entries.filterMap id = values ∧
    events.map Event.wire = reps.zip (defs.zip entries)

/-- Exact original bytes and ordered slot triples for the two level streams
and the PLAIN values. -/
@[expose] def SlotsWire (slots : Nat) (body : Bytes)
    (entriesInOrder : List (Nat × Nat × Option Int32)) : Prop :=
  ∃ (repLength defLength : List UInt8) (repBytes defBytes scalarBytes : Bytes)
      (reps defs : List Nat) (values : List Int32) (entries : List (Option Int32)),
    repLength.length = 4 ∧ defLength.length = 4 ∧
    KBytes.leVal repLength = repBytes.length ∧ KBytes.leVal defLength = defBytes.length ∧
    body.toList = repLength ++ repBytes.toList ++ defLength ++ defBytes.toList ++ scalarBytes.toList ∧
    Hybrid.Wire 1 slots repBytes.toList reps ∧ Hybrid.Wire 2 slots defBytes.toList defs ∧
    reps.length = slots ∧ defs.length = slots ∧ entries.length = slots ∧
    Plain.decodeInt32 ((valueMask defs).count true) scalarBytes = .ok values ∧
    entries.map Option.isSome = valueMask defs ∧ entries.filterMap id = values ∧
    entriesInOrder = reps.zip (defs.zip entries)

structure EventsWire (limits : Limits) (slots : Nat) (body : Bytes) (events : List Event) : Prop where
  cap : body.length ≤ limits.maxBodyBytes
  slotCount : events.length = slots
  data : SlotsWire slots body (events.map Event.wire)

structure V1Wire (codec : Int) (header : Page.Header) (body : Bytes) (info : Page.DataV1) : Prop where
  codec : codec = 0
  crc : header.crc = none
  compressedSize : header.compressedSize = body.length
  uncompressedSize : header.uncompressedSize = body.length
  kind : header.kind = .dataV1 info
  encoding : info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3

/-- A data stream witnesses all slots and a canonical event sequence for
exactly the returned complete rows. -/
structure Wire (limits : Limits) (expectedRows slots : Nat) (body : Bytes) (rows : List Row) : Prop where
  rowCount : rows.length = expectedRows
  caps : body.length ≤ limits.maxBodyBytes ∧ expectedRows ≤ limits.maxRows
  data : SlotsWire slots body ((rows.flatMap rowEvents).map Event.wire)

structure PageWire (limits : Limits) (codec : Int) (header : Page.Header) (expectedRows : Nat)
    (body : Bytes) (rows : List Row) : Prop where
  codec : codec = 0
  crc : header.crc = none
  compressedSize : header.compressedSize = body.length
  uncompressedSize : header.uncompressedSize = body.length
  page : ∃ info, header.kind = .dataV1 info ∧ info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧
    info.definitionLevelEncoding = 3 ∧ Wire limits expectedRows info.numValues body rows

end Silmaril.Formats.Parquet.ListPage
