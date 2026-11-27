module

import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Dictionary.Snappy.checkGroupWithCodec_agrees
#print axioms Fallback.Gzip.decodePageWith_reference_agrees
#print axioms Fallback.Gzip.readGroupWith_agrees
#print axioms Dictionary.Gzip.V2.readGroup_wire
#print axioms Fallback.Gzip.V2.readGroup_wire
#print axioms Gzip.Dispatch.V1.readGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V1.readGroup_fallback_agrees
#print axioms Gzip.Dispatch.V2.planPages_wire
#print axioms Gzip.Dispatch.V2.checkGroup_wire
#print axioms Gzip.Dispatch.V2.checkGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V2.checkGroup_fallback_agrees
#print axioms Gzip.Dispatch.V2.readGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V2.readGroup_fallback_agrees
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.readGroup_firstPageError
#print axioms Gzip.Dispatch.V2.readAll_firstError
#print axioms Gzip.Dispatch.V2.toIpc_firstError
#print axioms Gzip.Dispatch.V2.toIpc_readback
