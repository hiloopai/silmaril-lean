module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Thms

open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch

#print axioms readGroup_agrees
#print axioms readFrames_wire
#print axioms frames_members
#print axioms readGroup_wire
#print axioms convert_readback
#print axioms convert_first_error
#print axioms Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.readFrames_wire
#print axioms Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.readFrames_wire
