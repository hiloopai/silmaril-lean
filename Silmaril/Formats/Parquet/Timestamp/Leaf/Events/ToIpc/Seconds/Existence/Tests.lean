module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Thms
meta import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence

private def field : Arrow.TimestampBatch.Binding := ⟨"time", true, ⟨.second, none⟩⟩

private def emptyBatches : List (Arrow.TimestampBatch.Column field) := [[], []]

private def zeroLimits (batches : Nat) : Arrow.ObservationLimits :=
  { ipc := { batches := batches, rows := 0, bodyBytes := 0 }
    totalRows := 0
    totalCells := 0 }

#guard (Arrow.TimestampStream.Writer.emit (zeroLimits 1) field emptyBatches)
  matches .error (.writer (.limit .batches))
#guard (Arrow.TimestampStream.Writer.emit (zeroLimits 2) field emptyBatches).isOk
#guard (Arrow.TimestampStream.Writer.emit (zeroLimits 0) field []).isOk
