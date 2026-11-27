module

import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

#print axioms Silmaril.Formats.Parquet.FlatColumn.Zstd.decodePayload_sound
#print axioms Chunk.decodeV1Page_wire
#print axioms Chunk.readV2Suffix_wire
#print axioms Chunk.decodeV2Page_wire
#print axioms Chunk.V2PageWire.accounting
#print axioms Chunk.ChainWire.originalFrames
#print axioms Chunk.read_wire
#print axioms Rows.readAll_wire
#print axioms Rows.Events.read_failure
#print axioms Rows.Events.readProjected_preserves
#print axioms Rows.ToIpc.convert_readback
