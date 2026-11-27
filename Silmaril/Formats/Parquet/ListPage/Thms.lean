module

public import Silmaril.Formats.Parquet.ListPage.Defs
import Silmaril.Proofs.Formats.Parquet.ListPage.Correctness

public section

namespace Silmaril.Formats.Parquet.ListPage

theorem readEvent_wire {entry : Nat × Nat × Option Int32} {event : Event}
    (h : readEvent entry = .ok event) : event.wire = entry :=
  Proofs.Formats.Parquet.ListPage.readEvent_wire h

/-- The rows re-emit exactly the original sequence of starts, nulls, and elements. -/
theorem reconstruct_wire {events : List Event} {rows : List Row}
    (h : reconstruct events = .ok rows) : rows.flatMap rowEvents = events :=
  Proofs.Formats.Parquet.ListPage.reconstruct_wire h

theorem reconstruct_continuation (item : Option Int32) (rest : List Event) :
    reconstruct (.next item :: rest) = .error .continuationWithoutList :=
  Proofs.Formats.Parquet.ListPage.reconstruct_continuation item rest

theorem decodeBody_wire {limits : Limits} {expectedRows slots : Nat} {body : Bytes}
    {rows : List Row} (h : decodeBody limits expectedRows slots body = .ok rows) :
    Wire limits expectedRows slots body rows :=
  Proofs.Formats.Parquet.ListPage.decodeBody_wire h

/-- The complete checked page has the declared level slot count, original row
count and exact byte consumption, including both level lengths and PLAIN values. -/
theorem decodeV1_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {expectedRows : Nat} {body : Bytes} {rows : List Row}
    (h : decodeV1 limits codec header expectedRows body = .ok rows) :
    PageWire limits codec header expectedRows body rows :=
  Proofs.Formats.Parquet.ListPage.decodeV1_wire h

theorem finish_empty : State.empty.finish = [] := Proofs.Formats.Parquet.ListPage.finish_empty

/-- Feeding a page appends precisely its ordered events to the group state. -/
theorem feed_wire {state next : State} {events : List Event}
    (h : state.feed events = .ok next) :
    next.finish.flatMap rowEvents = state.finish.flatMap rowEvents ++ events :=
  Proofs.Formats.Parquet.ListPage.feed_wire h

theorem feed_nil (state : State) : state.feed [] = .ok state :=
  Proofs.Formats.Parquet.ListPage.feed_nil state

theorem reconstruct_of_feed {events : List Event} {state : State}
    (h : State.empty.feed events = .ok state) :
    reconstruct events = .ok state.finish :=
  Proofs.Formats.Parquet.ListPage.reconstruct_of_feed h

/-- The reconstruction result and typed failure are invariant under event cuts. -/
theorem feed_append (state : State) (left right : List Event) :
    state.feed (left ++ right) = (state.feed left).bind (·.feed right) :=
  Proofs.Formats.Parquet.ListPage.feed_append state left right

/-- A leading continuation requires a previously opened nonempty list. -/
theorem feed_next {state : State} (item : Option Int32) (rest : List Event) :
    state.feed (.next item :: rest) =
      match state.active with
      | none => .error .continuationWithoutList
      | some (head, tail) => ({ state with active := some (head, item :: tail) } : State).feed rest :=
  Proofs.Formats.Parquet.ListPage.feed_next item rest

/-- A selected value reader receives the exact suffix and its decoded present count. -/
theorem decodeSectionsUsing_wire {ε : Type} {wrap : Error → ε}
    {readValues : Nat → Bytes → Except ε (List Int32)} {limits : Limits} {slots : Nat}
    {repetition definition scalars : Bytes} {events : List Event}
    (h : decodeSectionsUsing wrap readValues limits slots repetition definition scalars = .ok events) :
    SectionsWireUsing readValues slots repetition definition scalars events :=
  Proofs.Formats.Parquet.ListPage.decodeSectionsUsing_wire h

/-- A selected V1 value reader receives the exact original suffix and present count. -/
theorem decodeEventsUsing_wire {ε : Type} {wrap : Error → ε}
    {readValues : Nat → Bytes → Except ε (List Int32)} {limits : Limits} {slots : Nat}
    {body : Bytes} {events : List Event}
    (h : decodeEventsUsing wrap readValues limits slots body = .ok events) :
    EventsWireUsing readValues limits slots body events :=
  Proofs.Formats.Parquet.ListPage.decodeEventsUsing_wire h

/-- The already separated level and value slices determine all ordered event slots. -/
theorem decodeSections_wire {limits : Limits} {slots : Nat} {repetition definition scalars : Bytes}
    {events : List Event} (h : decodeSections limits slots repetition definition scalars = .ok events) :
    SectionsWire slots repetition definition scalars events :=
  Proofs.Formats.Parquet.ListPage.decodeSections_wire h

/-- A page-local body decode consumes all bytes at the exact slot count. -/
theorem decodeEvents_wire {limits : Limits} {slots : Nat} {body : Bytes}
    {events : List Event} (h : decodeEvents limits slots body = .ok events) :
    EventsWire limits slots body events :=
  Proofs.Formats.Parquet.ListPage.decodeEvents_wire h

/-- The V1 guard retains the exact header tags and body sizes. -/
theorem checkV1_wire {codec : Int} {header : Page.Header} {body : Bytes} {info : Page.DataV1}
    (h : checkV1 codec header body = .ok info) : V1Wire codec header body info :=
  Proofs.Formats.Parquet.ListPage.checkV1_wire h

/-- A V1 frame gives the exact ordered wire events, including a possible leading continuation. -/
theorem decodeV1Events_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {body : Bytes} {events : List Event} (h : decodeV1Events limits codec header body = .ok events) :
    ∃ info, V1Wire codec header body info ∧ EventsWire limits info.numValues body events :=
  Proofs.Formats.Parquet.ListPage.decodeV1Events_wire h

end Silmaril.Formats.Parquet.ListPage
