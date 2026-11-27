module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms

open Silmaril.Formats.Parquet
open Timestamp.Leaf

#print axioms ChunkEncoding.plain_noDictionary
#print axioms Uncompressed.V2.checkGroup_wire
#print axioms Uncompressed.V2.effective_codec
#print axioms Uncompressed.V2.exactPayload_literal
#print axioms Uncompressed.V2.decodePage_wire
#print axioms Uncompressed.V2.pageWire_literal
#print axioms Uncompressed.V2.readGroup_wire
#print axioms Uncompressed.V2.readGroup_first_page_error
#print axioms Uncompressed.V2.decodePage_checksum_error
#print axioms Uncompressed.V2.readBound_first_error
#print axioms Uncompressed.V2.convert_first_error
#print axioms Uncompressed.V2.convert_readback
#print axioms Page.Checksum.verify_mismatch_iff
#print axioms Events.ToIpc.selectedBinding_exact
