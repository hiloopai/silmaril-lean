module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

#print axioms Chunk.readDictionary_wire
#print axioms Chunk.readPrefix_wire
#print axioms Chunk.decodeDictionaryDataPage_wire
#print axioms Chunk.V2DictionaryPageWire.accounting
#print axioms Chunk.decodeV2Page_wire
#print axioms Chunk.ChainWire.originalFrames
#print axioms Chunk.ChainWire.counts
#print axioms Chunk.read_wire
#print axioms Rows.readAll_wire
#print axioms Rows.Events.read_failure
#print axioms Rows.Events.readProjected_preserves
#print axioms Rows.ToIpc.convert_readback
