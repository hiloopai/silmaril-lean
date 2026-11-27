module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs

open Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds (recover)

private def millis (n : Int) : Ticks .utcInstant .millisecond := ⟨n⟩

#guard (millis (-1001)).rescale .second = none
#guard (millis 1001).rescale .second = none
#guard (millis (-9223372036854775000)).rescale .second = some ⟨-9223372036854775⟩
#guard (millis 9223372036854775000).rescale .second = some ⟨9223372036854775⟩
#guard recover .utcInstant [[none, some 0], [], [some (-1000)]] =
  some [[none, some 0], [], [some (-1)]]
#guard (convert {maxFileBytes := 1} {} (.ofList [0, 1])) matches .error (.source (.fileByteLimit 1 2))
