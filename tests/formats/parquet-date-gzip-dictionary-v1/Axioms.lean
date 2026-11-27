module

import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Fallback.Gzip.readEntries_wire
#print axioms Fallback.Gzip.prepareFor_frame
#print axioms Fallback.Gzip.decodePage_wire
#print axioms Dictionary.Gzip.V1.planData_wire
#print axioms Dictionary.Gzip.V1.planData_refusesPlain
#print axioms Dictionary.Gzip.V1.planPages_wire
#print axioms Dictionary.Gzip.V1.planPages_firstError
#print axioms Dictionary.Gzip.V1.checkGroup_wire
#print axioms Dictionary.Gzip.V1.checkGroup_dictionary
#print axioms Dictionary.Gzip.V1.decodePage_wire
#print axioms Dictionary.Gzip.V1.decodePage_checksum_error
#print axioms Dictionary.Gzip.V1.readGroup_wire
#print axioms Dictionary.Gzip.V1.readGroup_firstPageError
#print axioms Dictionary.Gzip.V1.readAll_firstError
#print axioms Dictionary.Gzip.V1.toIpc_firstError
#print axioms Dictionary.Gzip.V1.toIpc_readback
