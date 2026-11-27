module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms ChunkEncoding.gzipPlainV2_noDictionary
#print axioms Gzip.V2.checkGroup_wire
#print axioms Gzip.V2.decodePage_wire
#print axioms Gzip.V2.pageWire_decodes
#print axioms Gzip.V2.readGroup_wire
#print axioms Gzip.V2.readGroup_first_page_error
#print axioms Gzip.Dispatch.V2.dictionaryProfile_fallback_iff
#print axioms Gzip.Dispatch.V2.planDictionary_wire
#print axioms Gzip.Dispatch.V2.readDictionary_matches
#print axioms Gzip.Dispatch.V2.dictionary_framing_error
#print axioms Gzip.Dispatch.V2.readDictionary_wire
#print axioms Gzip.Dispatch.V2.hasDictionary_selected
#print axioms Gzip.Dispatch.V2.readGroup_route_error
#print axioms Gzip.Dispatch.V2.readGroup_plain_matches
#print axioms Gzip.Dispatch.V2.readGroup_dictionary_matches
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.readBound_first_error
#print axioms Gzip.Dispatch.V2.convert_readback
#print axioms Gzip.Dispatch.V2.convert_first_error
#print axioms Fallback.Gzip.V2.checkGroup_no_reentry
#print axioms Fallback.Gzip.V2.plain_decodes
#print axioms Fallback.Gzip.V2.references_decodes
#print axioms Events.ToIpc.selectedBinding_exact
