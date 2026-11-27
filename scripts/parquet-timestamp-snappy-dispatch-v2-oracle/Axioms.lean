module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Snappy.Dispatch.V2.dictionaryProfile_fallback_iff
#print axioms Snappy.Dispatch.V2.planDictionary_wire
#print axioms Snappy.Dispatch.V2.readDictionary_matches
#print axioms Snappy.Dispatch.V2.dictionary_framing_error
#print axioms Snappy.Dispatch.V2.readDictionary_wire
#print axioms Snappy.Dispatch.V2.hasDictionary_selected
#print axioms Snappy.Dispatch.V2.readGroup_route_error
#print axioms Snappy.Dispatch.V2.readGroup_plain_matches
#print axioms Snappy.Dispatch.V2.readGroup_dictionary_matches
#print axioms Snappy.Dispatch.V2.readGroup_dictionary_setup_error
#print axioms Snappy.Dispatch.V2.readGroup_wire
#print axioms Snappy.Dispatch.V2.readBound_first_error
#print axioms Snappy.Dispatch.V2.convert_readback
#print axioms Snappy.Dispatch.V2.convert_open_error
#print axioms Snappy.Dispatch.V2.convert_first_error
#print axioms SnappyV2.pageWire_prepared
#print axioms Dictionary.Snappy.readEntries_wire
#print axioms Dictionary.Snappy.V2.data_decodes
#print axioms Fallback.Snappy.V2.checkGroup_no_reentry
#print axioms Fallback.Snappy.V2.references_decodes
#print axioms Fallback.Snappy.V2.plain_decodes
#print axioms Events.ToIpc.selectedBinding_exact
