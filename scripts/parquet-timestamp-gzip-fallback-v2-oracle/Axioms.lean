module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Dictionary.Gzip.readEntries_wire
#print axioms Events.ToIpc.selectedBinding_exact
#print axioms Dictionary.Gzip.V2.planDataWith_wire
#print axioms Dictionary.Gzip.V2.prepared_wire
#print axioms Dictionary.Gzip.V2.data_decodesWith
#print axioms Fallback.Gzip.V2.planData_wire
#print axioms Fallback.Gzip.V2.checkGroup_wire
#print axioms Fallback.Gzip.V2.checkGroup_no_reentry
#print axioms Fallback.Gzip.V2.plain_decodes
#print axioms Fallback.Gzip.V2.references_decodes
#print axioms Fallback.Gzip.V2.readGroup_wire
#print axioms Fallback.Gzip.V2.data_checksum_error
#print axioms Fallback.Gzip.V2.readGroup_first_page_error
#print axioms Fallback.Gzip.V2.readBound_first_error
#print axioms Fallback.Gzip.V2.convert_first_error
#print axioms Fallback.Gzip.V2.convert_readback
