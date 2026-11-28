module

import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

#print axioms Silmaril.Formats.Parquet.Page.readChunk_readPage
#print axioms Silmaril.Formats.Parquet.Page.readPage_exactPrefix
#print axioms decodeV2Page_wire
#print axioms decodeDataPage_wire
#print axioms v2_accounting
#print axioms v2_body
#print axioms page_starts_closed
#print axioms V2PageWire.nextPageStarts
#print axioms ChainWire.counts
#print axioms read_wire
#print axioms chunk_bytes
#print axioms Binding.codec_matches
#print axioms Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV1Body_wire
#print axioms Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV2SuffixWith_wire
#print axioms Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.V2SuffixWire.eq_of_false
#print axioms Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.convert_readback
#print axioms Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.convert_source_failure
