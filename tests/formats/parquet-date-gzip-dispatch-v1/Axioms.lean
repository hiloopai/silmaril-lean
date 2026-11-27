module

import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Dictionary.Gzip.V1.readGroup_wire
#print axioms Fallback.Gzip.readGroup_wire
#print axioms Gzip.Dispatch.V1.planPages_wire
#print axioms Gzip.Dispatch.V1.checkGroup_wire
#print axioms Gzip.Dispatch.V1.checkGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V1.checkGroup_fallback_agrees
#print axioms Gzip.Dispatch.V1.readGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V1.readGroup_fallback_agrees
#print axioms Gzip.Dispatch.V1.readGroup_wire
#print axioms Gzip.Dispatch.V1.readGroup_firstPageError
#print axioms Gzip.Dispatch.V1.readAll_firstError
#print axioms Gzip.Dispatch.V1.toIpc_firstError
#print axioms Gzip.Dispatch.V1.toIpc_readback
