module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Dictionary.Gzip.planDataWith_wire
#print axioms Dictionary.Gzip.prepared_member
#print axioms Fallback.Gzip.planData_wire
#print axioms Fallback.Gzip.checkGroup_wire
#print axioms Fallback.Gzip.plain_decodes
#print axioms Fallback.Gzip.references_decodes
#print axioms Fallback.Gzip.readGroup_wire
#print axioms Fallback.Gzip.data_checksum_error
#print axioms Fallback.Gzip.readGroup_first_page_error
#print axioms Fallback.Gzip.readBound_first_error
#print axioms Fallback.Gzip.convert_first_error
#print axioms Fallback.Gzip.convert_readback
