module

import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms DictionaryIndex.readValues_wire
#print axioms Repeated.Chunk.readDictionaryWith_wire
#print axioms Repeated.Chunk.readFramedDictionary_wire
#print axioms Repeated.Chunk.readV1Body_wire
#print axioms Repeated.Chunk.readV2SuffixWith_wire
#print axioms Repeated.Chunk.V2SuffixWire.eq_of_false
#print axioms ListPath.Chunk.Binding.codec_exact
#print axioms ListPath.Chunk.Binding.span_exact
#print axioms ListPath.Chunk.decodePage_wire
#print axioms ListPath.Chunk.decodeV2Page_wire
#print axioms ListPath.Chunk.decodeDataPage_wire
#print axioms ListPath.Chunk.V2PageWire.counts
#print axioms ListPath.Chunk.Wire.dictionary_anchors
#print axioms ListPath.Chunk.Wire.dictionary_payload
#print axioms ListPath.Chunk.read_wire
#print axioms ListPath.Chunk.read_dictionary_failure
#print axioms ListPath.Chunk.read_page_failure
#print axioms ListPath.Reader.readGroup_wire
#print axioms ListPath.Reader.Events.read_failure
#print axioms ListPath.Reader.ToIpc.convert_source_error
#print axioms ListPath.Reader.ToIpc.convert_exact_eos
