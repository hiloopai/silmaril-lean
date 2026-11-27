module

public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.Timestamp.Defs

/-! # Logical timestamp metadata and signed payloads for Arrow and Parquet -/

@[expose] public section

namespace Silmaril.Formats.ColumnarTimestamp

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Gregorian (CivilDate)

def epochKind (adjustedToUTC : Bool) : Kind :=
  if adjustedToUTC then .utcInstant else .localReading

namespace Arrow

/-- The timestamp fields a schema adapter supplies after reading Arrow metadata. -/
structure Metadata where
  unit : TickUnit
  timezone : Option String
  deriving DecidableEq

/-- An opaque display annotation. Unset and empty strings both give local semantics. -/
def Metadata.timezoneAnnotation (metadata : Metadata) : Option String :=
  metadata.timezone.filter (· != "")

def Metadata.kind (metadata : Metadata) : Kind :=
  epochKind metadata.timezoneAnnotation.isSome

/-- Interpret a signed payload under the metadata's epoch and unit. -/
def Metadata.decode (metadata : Metadata) (payload : Int64) : Ticks metadata.kind metadata.unit :=
  Ticks.ofInt64 metadata.kind metadata.unit payload

/-- Encode same-kind ticks exactly in the metadata's unit and signed payload range. -/
def Metadata.encode (metadata : Metadata) {source : TickUnit} (value : Ticks metadata.kind source) :
    Except ConversionError Int64 :=
  value.toInt64 metadata.unit

end Arrow

namespace Parquet

/-- The supported units of the modern INT64 `TIMESTAMP` logical type. -/
inductive TimeUnit where
  | millis | micros | nanos
  deriving DecidableEq, Repr

def TimeUnit.tickUnit : TimeUnit → TickUnit
  | .millis => .millisecond
  | .micros => .microsecond
  | .nanos => .nanosecond

/-- A logical annotation after an adapter has checked the INT64 physical type. -/
structure Metadata where
  unit : TimeUnit
  isAdjustedToUTC : Bool

def Metadata.kind (metadata : Metadata) : Kind :=
  epochKind metadata.isAdjustedToUTC

/-- Interpret a signed payload under the metadata's epoch and unit. -/
def Metadata.decode (metadata : Metadata) (payload : Int64) :
    Ticks metadata.kind metadata.unit.tickUnit :=
  Ticks.ofInt64 metadata.kind metadata.unit.tickUnit payload

/-- Encode same-kind ticks exactly in the metadata's unit and signed payload range. -/
def Metadata.encode (metadata : Metadata) {source : TickUnit} (value : Ticks metadata.kind source) :
    Except ConversionError Int64 :=
  value.toInt64 metadata.unit.tickUnit

end Parquet

/-- Preserve the interpretation when projecting Arrow metadata onto Parquet.
    The timezone annotation has no field in the destination. -/
def Arrow.Metadata.parquet (metadata : Arrow.Metadata) (target : Parquet.TimeUnit) : Parquet.Metadata :=
  ⟨target, metadata.timezoneAnnotation.isSome⟩

/-- Convert the payload for the Parquet metadata returned by `parquet`. -/
def Arrow.Metadata.toParquet (metadata : Arrow.Metadata) (target : Parquet.TimeUnit) (payload : Int64) :
    Except ConversionError Int64 :=
  (metadata.parquet target).encode (metadata.decode payload)

/-- Use `UTC` as the canonical Arrow annotation for a Parquet instant. -/
def Parquet.Metadata.arrow (metadata : Parquet.Metadata) (target : TickUnit) : Arrow.Metadata :=
  ⟨target, if metadata.isAdjustedToUTC then some "UTC" else none⟩

/-- Convert the payload for the Arrow metadata returned by `arrow`. -/
def Parquet.Metadata.toArrow (metadata : Parquet.Metadata) (target : TickUnit) (payload : Int64) :
    Except ConversionError Int64 :=
  (metadata.decode payload).toInt64 target

/-- The length of a local timestamp day on the uniform scale. -/
def nanosecondsPerDay : Nat := 86400000000000

/-- A local wall-clock date candidate and its bounded nanosecond-of-day field. -/
structure LocalDateTime where
  date : CivilDate
  nanosecondOfDay : Fin nanosecondsPerDay
  deriving DecidableEq, Repr

/-- Split the local offset by Euclidean division, including before day zero. -/
def LocalDateTime.ofTicks {unit : TickUnit} (value : Ticks .localReading unit) : LocalDateTime :=
  let nanos := value.denote.ticks
  ⟨CivilDate.ofEpochDay (nanos / nanosecondsPerDay), ⟨(nanos % nanosecondsPerDay).toNat, by
    exact (Int.toNat_lt' (by decide : 0 < nanosecondsPerDay)).mpr
      (Int.emod_lt_of_pos nanos (by decide))⟩⟩

/-- Combine a valid civil date and a nanosecond of day on the local scale. -/
def LocalDateTime.toTicks? (value : LocalDateTime) : Option (Ticks .localReading .nanosecond) := do
  let day ← value.date.toEpochDay?
  return ⟨day * nanosecondsPerDay + value.nanosecondOfDay.val⟩

end Silmaril.Formats.ColumnarTimestamp
