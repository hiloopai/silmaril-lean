module

import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms

open Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RecursiveSchema

#print axioms Repeated.Chunk.readV1Body_wire
#print axioms Repeated.Chunk.readV2SuffixWith_wire
#print axioms Repeated.Chunk.readFramedDictionary_wire
#print axioms DictionaryIndex.readValues_wire
#print axioms ListPath.Chunk.Codec.column_ofId
#print axioms ListPath.Chunk.Wire.originalHeader
#print axioms ListPath.Chunk.PageWire.counts
#print axioms ListPath.Chunk.V2PageWire.counts
#print axioms ListPath.Chunk.Wire.dictionary_payloadOf
#print axioms ListPath.Chunk.readCarrier_dictionary_failure
#print axioms ListPath.Chunk.readCarrier_page_failure
#print axioms TwoListStruct.Rows.addressed_slot
#print axioms TwoListStruct.Reader.readColumn_wire
#print axioms TwoListStruct.Reader.ColumnBinding.codec_exact
#print axioms TwoListStruct.Reader.ColumnWire.dictionary_anchors
#print axioms TwoListStruct.Reader.ColumnWire.dictionary_payload
#print axioms TwoListStruct.Reader.ColumnWire.v1_page
#print axioms TwoListStruct.Reader.ColumnWire.v2_page
#print axioms TwoListStruct.Reader.readColumn_page_failure
#print axioms TwoListStruct.Reader.readColumn_dictionary_failure
#print axioms TwoListStruct.Reader.readGroup_wire
#print axioms TwoListStruct.Reader.readGroup_typed
#print axioms TwoListStruct.Reader.readGroup_topology_failure
#print axioms TwoListStruct.Reader.Events.read_failure
#print axioms TwoListStruct.Reader.Events.readProjected_wire
#print axioms TwoListStruct.Reader.ToIpc.convert_source_error
#print axioms TwoListStruct.Reader.ToIpc.convert_exact_eos
#print axioms TwoListStruct.Writer.emit_wire
