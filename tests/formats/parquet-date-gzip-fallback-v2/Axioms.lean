import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Gzip.V2.prepareFor_frame
#print axioms Gzip.V2.pageWire_exact
#print axioms Fallback.Gzip.readEntries_wire
#print axioms Fallback.Gzip.V2.planData_wire
#print axioms Fallback.Gzip.V2.planPages_wire
#print axioms Fallback.Gzip.V2.checkGroup_wire
#print axioms Fallback.Gzip.V2.transition_totals
#print axioms Fallback.Gzip.V2.checkGroup_dictionary
#print axioms Fallback.Gzip.V2.decodePage_wire
#print axioms Fallback.Gzip.V2.decodePage_checksum_error
#print axioms Fallback.Gzip.V2.readGroup_wire
#print axioms Fallback.Gzip.V2.readGroup_firstPageError
#print axioms Fallback.Gzip.V2.readAll_firstError
#print axioms Fallback.Gzip.V2.toIpc_firstError
#print axioms Fallback.Gzip.V2.toIpc_readback
