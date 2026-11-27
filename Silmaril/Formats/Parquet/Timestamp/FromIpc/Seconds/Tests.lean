module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Thms
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs

open Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds

private def seconds (n : Int) : Ticks .localReading .second := ⟨n⟩

#guard (seconds (-9223372036854775)).toInt64 .millisecond = .ok (-9223372036854775000)
#guard (seconds 9223372036854775).toInt64 .millisecond = .ok 9223372036854775000
#guard (seconds (-9223372036854776)).toInt64 .millisecond = .error .outOfRange
#guard (seconds 9223372036854776).toInt64 .millisecond = .error .outOfRange
#guard recover .localReading [[some (-1000), none, some 0], [], [some 1000]] =
  some [[some (-1), none, some 0], [], [some 1]]
#guard recover .utcInstant [[some (-1001)]] = none
#guard recover .utcInstant [] = some []
#guard recover .utcInstant [[], []] = some [[], []]
#guard (convert {} {maxInputBytes := 0} (.ofChunks 1 1 [0])) matches .error .inputByteLimit
