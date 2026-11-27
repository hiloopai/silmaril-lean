module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms ByteStreamSplit.checkGroup_wire
#print axioms ByteStreamSplit.decodePage_wire
#print axioms ByteStreamSplit.pageWire_extents
#print axioms ByteStreamSplit.readWord_signed
#print axioms ByteStreamSplit.readGroup_wire
#print axioms ByteStreamSplit.readGroup_first_page_error
#print axioms ByteStreamSplit.decodePage_checksum_error
#print axioms ByteStreamSplit.readBound_first_error
#print axioms ByteStreamSplit.convert_first_error
#print axioms ByteStreamSplit.convert_readback
#print axioms Events.ToIpc.selectedBinding_exact
