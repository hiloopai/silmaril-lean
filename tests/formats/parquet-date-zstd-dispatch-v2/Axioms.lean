module

import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms

open Silmaril.Formats.Parquet

#print axioms Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.route_selected
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_routeError
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_plain_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.planPages_wire
#print axioms Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_wire
#print axioms Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_dictionary_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_fallback_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_dictionarySetupError
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_dictionary_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_fallback_agrees
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_success_iff
#print axioms Date.Leaf.Zstd.Dispatch.V2.readGroup_wire
#print axioms Date.Leaf.Zstd.Dispatch.V2.readAll_firstError
#print axioms Date.Leaf.Zstd.Dispatch.V2.toIpc_firstError
#print axioms Date.Leaf.Zstd.Dispatch.V2.toIpc_readback
