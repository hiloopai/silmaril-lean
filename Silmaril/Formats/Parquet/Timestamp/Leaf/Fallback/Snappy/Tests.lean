module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf

#guard (Fallback.Snappy.convert .modernOnly {} {maxFileBytes := 1} {} (.ofList [0, 1]) 1)
  matches .error (.fileByteLimit 1 2)
#guard Fallback.admits 0 && Fallback.admits 8 && !Fallback.admits 2
