module

public import Silmaril.Formats.Parquet.ListPage.Defs
import all Silmaril.Formats.Parquet.ListPage.Defs
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms

namespace Silmaril.Proofs.Formats.Parquet.ListPage

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListPage

public theorem readEvent_wire {entry : Nat × Nat × Option Int32} {event : Event}
    (h : readEvent entry = .ok event) : event.wire = entry := by
  unfold readEvent at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    assumption
  · cases h

private theorem readEvents_wire {entries : List (Nat × Nat × Option Int32)} {events : List Event}
    (h : entries.mapM readEvent = .ok events) : events.map Event.wire = entries := by
  induction entries generalizing events with
  | nil => cases h; rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at h
    cases first : readEvent entry with
    | error => simp [first, bind, Except.bind] at h
    | ok event =>
      simp only [first, bind, Except.bind] at h
      cases tail : rest.mapM readEvent with
      | error => rw [tail] at h; cases h
      | ok out =>
        rw [tail] at h
        obtain rfl := Except.ok.inj h
        simp [readEvent_wire first, ih tail]

@[simp] private theorem finish_flush (state : State) : state.flush.reverse = state.finish := rfl

private theorem step_wire {state next : State} {event : Event}
    (h : State.step state event = .ok next) :
    next.finish.flatMap rowEvents = state.finish.flatMap rowEvents ++ [event] := by
  cases event with
  | nullList =>
    cases h
    simp [State.finish, State.flush, rowEvents]
  | emptyList =>
    cases h
    simp [State.finish, State.flush, rowEvents]
  | first item =>
    cases h
    simp [State.finish, State.flush, rowEvents]
  | next item =>
    rw [State.step] at h
    split at h
    · cases h
    · rename_i head tail active
      obtain rfl := Except.ok.inj h
      simp [State.finish, State.flush, active, rowEvents, List.map_append, List.append_assoc]

public theorem finish_empty : State.empty.finish = [] := by simp [State.finish, State.flush, State.empty]

public theorem feed_wire {state next : State} {events : List Event}
    (h : state.feed events = .ok next) :
    next.finish.flatMap rowEvents = state.finish.flatMap rowEvents ++ events := by
  induction events generalizing state with
  | nil => cases h; simp
  | cons event rest ih =>
    unfold State.feed at h
    rw [List.foldlM_cons] at h
    cases step : State.step state event with
    | error e => simp [step, bind, Except.bind] at h
    | ok more =>
      simp only [step, bind, Except.bind] at h
      rw [ih h, step_wire step, List.append_assoc]
      rfl

public theorem feed_nil (state : State) : state.feed [] = .ok state := by
  unfold State.feed
  rfl

public theorem reconstruct_of_feed {events : List Event} {state : State}
    (h : State.empty.feed events = .ok state) :
    reconstruct events = .ok state.finish := by
  simp [reconstruct, h, Except.map]

public theorem feed_append (state : State) (left right : List Event) :
    state.feed (left ++ right) = (state.feed left).bind (·.feed right) := by
  simp [State.feed, List.foldlM_append, bind, Except.bind]

public theorem feed_next {state : State} (item : Option Int32) (rest : List Event) :
    state.feed (.next item :: rest) =
      match state.active with
      | none => .error .continuationWithoutList
      | some (head, tail) => ({ state with active := some (head, item :: tail) } : State).feed rest := by
  unfold State.feed
  rw [List.foldlM_cons]
  cases active : state.active <;> simp [State.step, active, bind, Except.bind]

public theorem reconstruct_wire {events : List Event} {rows : List Row}
    (h : reconstruct events = .ok rows) : rows.flatMap rowEvents = events := by
  unfold reconstruct at h
  cases read : State.empty.feed events with
  | error e => simp [read, Except.map] at h
  | ok state =>
    have same : state.finish = rows := by simpa [read, Except.map] using h
    rw [← same, feed_wire read]
    rfl

public theorem reconstruct_continuation (item : Option Int32) (rest : List Event) :
    reconstruct (.next item :: rest) = .error .continuationWithoutList := by
  rw [reconstruct, feed_next]
  rfl

public theorem decodeEvents_wire {limits : Limits} {slots : Nat} {body : Bytes}
    {events : List Event} (h : decodeEvents limits slots body = .ok events) :
    EventsWire limits slots body events := by
  unfold decodeEvents at h
  split at h
  · cases h
  rename_i bodyCap
  cases repSplit : FlatPage.splitV1Optional limits.levels.bytes body with
  | error => simp [repSplit, Except.mapError, bind, Except.bind] at h
  | ok first =>
    simp only [repSplit, Except.mapError, bind, Except.bind] at h
    cases defSplit : FlatPage.splitV1Optional limits.levels.bytes first.scalars with
    | error => simp [defSplit] at h
    | ok second =>
      simp only [defSplit] at h
      cases repRead : Hybrid.decode 1 slots limits.levels first.definitions with
      | error => simp [repRead] at h
      | ok reps =>
        simp only [repRead] at h
        cases defRead : Hybrid.decode 2 slots limits.levels second.definitions with
        | error => simp [defRead] at h
        | ok defs =>
          simp only [defRead] at h
          cases plain : Plain.decodeInt32 ((valueMask defs).count true) second.scalars with
          | error => simp [plain] at h
          | ok values =>
            simp only [plain] at h
            cases filled : FlatPage.reconstruct (valueMask defs) values with
            | error => simp [filled] at h
            | ok entries =>
              simp only [filled] at h
              cases eventRead : (reps.zip (defs.zip entries)).mapM readEvent with
              | error => rw [eventRead] at h; cases h
              | ok decoded =>
                rw [eventRead] at h
                obtain rfl := Except.ok.inj h
                obtain ⟨repLength, repWidth, repBytes, _, fromBody⟩ :=
                  FlatPage.splitV1Optional_ok_iff.mp repSplit
                obtain ⟨defLength, defWidth, defBytes, _, fromRest⟩ :=
                  FlatPage.splitV1Optional_ok_iff.mp defSplit
                obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp filled
                have repCount := Hybrid.decode_length repRead
                have defCount := Hybrid.decode_length defRead
                have entryCount : entries.length = slots := by
                  simpa [valueMask, defCount] using congrArg List.length mask
                have exactEvents := readEvents_wire eventRead
                have slotsExact : decoded.length = slots := by
                  simpa [repCount, defCount, entryCount] using congrArg List.length exactEvents
                refine ⟨Nat.le_of_not_gt bodyCap, slotsExact,
                  repLength, defLength, first.definitions, second.definitions, second.scalars,
                  reps, defs, values, entries, repWidth, defWidth, repBytes, defBytes, ?_,
                  (Hybrid.decode_ok_iff.mp repRead).2.2.2.2, (Hybrid.decode_ok_iff.mp defRead).2.2.2.2,
                  repCount, defCount, entryCount, plain, mask, ordered, exactEvents⟩
                simpa [fromRest, List.append_assoc] using fromBody

public theorem decodeBody_wire {limits : Limits} {expectedRows slots : Nat} {body : Bytes}
    {rows : List Row} (h : decodeBody limits expectedRows slots body = .ok rows) :
    Wire limits expectedRows slots body rows := by
  unfold decodeBody at h
  split at h
  · cases h
  rename_i bodyCap
  split at h
  · cases h
  rename_i rowCap
  cases decoded : decodeEvents limits slots body with
  | error e => simp [decoded, bind, Except.bind] at h
  | ok events =>
    simp only [decoded, bind, Except.bind] at h
    cases assembled : reconstruct events with
    | error e => simp [assembled] at h
    | ok output =>
      simp only [assembled] at h
      split at h
      · cases h
      rename_i count
      obtain rfl := Except.ok.inj h
      refine ⟨not_not.mp count, ⟨Nat.le_of_not_gt bodyCap, Nat.le_of_not_gt rowCap⟩, ?_⟩
      rw [reconstruct_wire assembled]
      exact (decodeEvents_wire decoded).data

public theorem checkV1_wire {codec : Int} {header : Page.Header} {body : Bytes} {info : Page.DataV1}
    (h : checkV1 codec header body = .ok info) : V1Wire codec header body info := by
  unfold checkV1 at h
  split at h
  · cases h
  rename_i compression
  split at h
  · rename_i actual page
    split at h
    · cases h
    rename_i crc
    split at h
    · cases h
    rename_i encoding
    split at h
    · cases h
    rename_i sizes
    obtain rfl := Except.ok.inj h
    have extent := not_not.mp sizes
    exact ⟨not_not.mp compression, by cases eq : header.crc <;> simp_all,
      extent.1, extent.2, page, not_not.mp encoding⟩
  · cases h

public theorem decodeV1Events_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {body : Bytes} {events : List Event} (h : decodeV1Events limits codec header body = .ok events) :
    ∃ info, V1Wire codec header body info ∧ EventsWire limits info.numValues body events := by
  unfold decodeV1Events at h
  cases check : checkV1 codec header body with
  | error e => simp [check, bind, Except.bind] at h
  | ok info => exact ⟨info, checkV1_wire check, decodeEvents_wire (by simpa [check, bind, Except.bind] using h)⟩

public theorem decodeV1_wire {limits : Limits} {codec : Int} {header : Page.Header}
    {expectedRows : Nat} {body : Bytes} {rows : List Row}
    (h : decodeV1 limits codec header expectedRows body = .ok rows) :
    PageWire limits codec header expectedRows body rows := by
  unfold decodeV1 at h
  cases check : checkV1 codec header body with
  | error e => simp [check, bind, Except.bind] at h
  | ok info =>
    simp only [check, bind, Except.bind] at h
    have wire := checkV1_wire check
    exact ⟨wire.codec, wire.crc, wire.compressedSize, wire.uncompressedSize,
      info, wire.kind, wire.encoding.1, wire.encoding.2.1, wire.encoding.2.2, decodeBody_wire h⟩

end Silmaril.Proofs.Formats.Parquet.ListPage
