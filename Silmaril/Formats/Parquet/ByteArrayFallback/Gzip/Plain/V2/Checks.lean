module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Thms

open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2

#print axioms data_suffix
#print axioms readFrames_wire
#print axioms readGroup_wire
#print axioms convert_readback
#print axioms convert_first_error
#print axioms Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.decodePlainPage_wire
#print axioms Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.plain_data_suffix
