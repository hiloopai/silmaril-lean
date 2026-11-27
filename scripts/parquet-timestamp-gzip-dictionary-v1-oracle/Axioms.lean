module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary

#print axioms Snappy.readEntriesWithCodec_wire
#print axioms Gzip.planData_wire
#print axioms Gzip.readEntries_wire
#print axioms Gzip.checkGroup_wire
#print axioms Gzip.data_decodes
#print axioms Gzip.readGroup_wire
#print axioms Gzip.data_checksum_error
#print axioms Gzip.readGroup_first_page_error
#print axioms Gzip.readBound_first_error
#print axioms Gzip.convert_first_error
#print axioms Gzip.convert_readback
