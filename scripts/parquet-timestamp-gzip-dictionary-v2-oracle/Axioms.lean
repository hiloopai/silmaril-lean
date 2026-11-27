module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip

#print axioms readEntries_wire
#print axioms V2.planData_wire
#print axioms V2.checkGroup_wire
#print axioms V2.data_decodes
#print axioms V2.readGroup_wire
#print axioms V2.data_checksum_error
#print axioms V2.readGroup_first_page_error
#print axioms V2.readBound_first_error
#print axioms V2.convert_first_error
#print axioms V2.convert_readback
