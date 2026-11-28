module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms Repeated.Chunk.checkV2Counts_wire
#print axioms Repeated.Chunk.readV2SectionsWith_wire
#print axioms ListPath.Chunk.decodePage_wire
#print axioms ListPath.Chunk.decodeV2Page_wire
#print axioms ListPath.Chunk.decodeDataPage_wire
#print axioms ListPath.Chunk.V2PageWire.counts
#print axioms ListPath.Chunk.ChainWire.counts
#print axioms ListPath.Chunk.Wire.originalHeader
#print axioms ListPath.Chunk.read_wire
#print axioms ListPath.Reader.reconstruct_reframe
#print axioms ListPath.Reader.Events.read_failure
#print axioms ListPath.Reader.ToIpc.convert_source_error
#print axioms ListPath.Reader.ToIpc.convert_exact_eos
