import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Fallback.planPrefixWith_firstError
#print axioms Fallback.planPagesWith_earlierPhaseError
#print axioms Fallback.planPagesWith_headerError
#print axioms Fallback.planPagesWith_wire
#print axioms Dictionary.Snappy.checkGroupWithCodec_wire
#print axioms Fallback.Gzip.planData_wire
#print axioms Fallback.Gzip.planPages_wire
#print axioms Fallback.Gzip.checkGroup_wire
#print axioms Fallback.Gzip.transition_totals
#print axioms Fallback.Gzip.readEntries_wire
#print axioms Fallback.Gzip.decodePage_wire
#print axioms Fallback.Gzip.decodePage_checksum_error
#print axioms Fallback.Gzip.readGroup_wire
#print axioms Fallback.Gzip.readGroup_firstPageError
#print axioms Fallback.Gzip.readAll_firstError
#print axioms Fallback.Gzip.toIpc_firstError
#print axioms Fallback.Gzip.toIpc_readback
