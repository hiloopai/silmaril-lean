module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Delta.checkGroup_wire
#print axioms Delta.decodePage_wire
#print axioms Delta.pageWire_extents
#print axioms Delta.reconstruct_signed
#print axioms Delta.readGroup_wire
#print axioms Delta.readGroup_first_page_error
#print axioms Delta.decodePage_checksum_error
#print axioms Delta.readBound_first_error
#print axioms Delta.convert_first_error
#print axioms Delta.convert_readback
#print axioms Events.ToIpc.selectedBinding_exact
