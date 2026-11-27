module

import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

#print axioms Silmaril.Formats.Parquet.RecursiveSchema.Chunk.admitPageWith_wire
#print axioms Chunk.decodeV1Page_wire
#print axioms Chunk.PageWire.counts
#print axioms Chunk.decodeV2Page_wire
#print axioms Chunk.read_wire
#print axioms Chunk.Writer.emit_wire
#print axioms Rows.readAll_wire
#print axioms Rows.Events.read_failure
#print axioms Rows.Events.readProjected_preserves
#print axioms Rows.ToIpc.convert_readback
