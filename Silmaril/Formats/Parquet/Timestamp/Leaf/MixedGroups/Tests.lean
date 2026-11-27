module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf

private def dataPage (tag : Int) (offset : Nat) : Dictionary.DataPage :=
  ⟨⟨⟨0, 0, none, .dataV1 ⟨0, tag, 3, 3⟩⟩, ⟨offset, offset + 1⟩, ⟨offset + 1, offset + 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 1⟩, 0, 0, tag, .v1 3 3⟩⟩

#guard MixedGroups.checkSequence [] = .error .dictionaryMissingData
#guard MixedGroups.checkSequence [dataPage 8 12] = .ok ()
#guard MixedGroups.dictionaryLayout [dataPage 8 12] = .references
#guard MixedGroups.checkSequence [dataPage 8 12, dataPage 0 13] = .ok ()
#guard MixedGroups.dictionaryLayout [dataPage 8 12, dataPage 0 13] = .fallback
#guard MixedGroups.checkSequence [dataPage 0 12, dataPage 8 13] = .error (.dictionaryPage 1 12 (.encoding 0))
#guard MixedGroups.checkSequence [dataPage 8 12, dataPage 0 13, dataPage 8 14] =
  .error (.dictionaryPage 3 14 .dictionaryAfterFallback)
#guard (MixedGroups.convert .modernOnly {} {maxFileBytes := 1} {} (.ofList [0, 1]) 1)
  matches .error (.fileByteLimit 1 2)
