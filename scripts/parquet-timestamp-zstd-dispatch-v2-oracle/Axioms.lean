module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Zstd.Dispatch.V2.dictionaryProfile_fallback_iff
#print axioms Zstd.Dispatch.V2.planDictionary_wire
#print axioms Zstd.Dispatch.V2.readDictionary_matches
#print axioms Zstd.Dispatch.V2.dictionary_framing_error
#print axioms Zstd.Dispatch.V2.readDictionary_wire
#print axioms Zstd.Dispatch.V2.hasDictionary_selected
#print axioms Zstd.Dispatch.V2.readGroup_route_error
#print axioms Zstd.Dispatch.V2.readGroup_plain_matches
#print axioms Zstd.Dispatch.V2.readGroup_dictionary_matches
#print axioms Zstd.Dispatch.V2.readGroup_dictionary_framing_error
#print axioms Zstd.Dispatch.V2.readGroup_wire
#print axioms Zstd.Dispatch.V2.readBound_first_error
#print axioms Zstd.Dispatch.V2.convert_first_error
#print axioms Zstd.Dispatch.V2.convert_readback
#print axioms Zstd.V2.checkGroup_wire
#print axioms Zstd.V2.decodePage_wire
#print axioms Dictionary.Zstd.V2.readEntries_wire
#print axioms Dictionary.Zstd.V2.decodePage_wireWith
#print axioms Fallback.Zstd.V2.checkGroup_no_reentry
#print axioms Fallback.Zstd.V2.decodePage_wire
#print axioms Events.ToIpc.selectedBinding_exact
