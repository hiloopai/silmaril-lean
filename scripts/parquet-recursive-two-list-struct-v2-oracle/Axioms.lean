module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms ListPath.Chunk.ChainWire.page_of_mem
#print axioms ListPath.Chunk.V2PageWire.counts
#print axioms ListPath.Chunk.readCarrier_page_failure
#print axioms TwoListStruct.Reader.readColumn_wire
#print axioms TwoListStruct.Reader.ColumnWire.v2_page
#print axioms TwoListStruct.Reader.readColumn_page_failure
#print axioms TwoListStruct.Reader.readGroup_wire
#print axioms TwoListStruct.Reader.readGroup_typed
#print axioms TwoListStruct.Reader.readGroup_topology_failure
#print axioms TwoListStruct.Reader.Events.read_failure
#print axioms TwoListStruct.Reader.Events.readProjected_wire
#print axioms TwoListStruct.Reader.ToIpc.convert_source_error
#print axioms TwoListStruct.Reader.ToIpc.convert_exact_eos
#print axioms TwoListStruct.Writer.emit_wire
