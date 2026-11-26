module

import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Arrow.StreamWriter.Thms

open Silmaril Silmaril.Formats.Arrow

example : readEnvelope {} (.leaf 8 0xffffffff) 0 = .ok .eos := by rfl
example : readEnvelope {} (.leaf 16 0x00000008ffffffff) 0 = .ok (.metadata 8) := by
  rfl
example : readEnvelope {} (.leaf 15 0x00000008ffffffff) 0 = .error (.malformed .truncated) := by
  rfl

example : Body.offsetAt (.leaf 4 0x80000000) 0 = none := by rfl
example : Body.validAt (.leaf 2 0x0100) 8 = some true := by rfl

#print axioms readEnvelope_iff
#print axioms metadata_exact
#print axioms readBody_iff
#print axioms body_exact
#print axioms readEnvelope_rechunk
#print axioms BuffersFit.mem_fits
#print axioms BatchFrame.buffer_exact
#print axioms validateBatch_iff

#print axioms Body.validAt_iff
#print axioms Body.offsetAt_iff
#print axioms Body.readCell_iff
#print axioms Body.readColumn_iff
#print axioms decodeBatch_iff
#print axioms BatchWire.shape

#print axioms FileReader.readFooterSpan_verified
#print axioms FileReader.FooterSpan.bytes_exact
#print axioms FileReader.Index.block_range
#print axioms FileReader.Index.block_order
#print axioms FileReader.Index.readBlock_exact
#print axioms FileReader.readRows_indexed

#print axioms Writer.checkInput_iff
#print axioms Writer.packBuffers_exact
#print axioms Writer.emitBatch_of_admitted
#print axioms Writer.emitBatch_roundtrip

#print axioms MetadataWriter.wireSize_aligned
#print axioms MetadataWriter.serialize_extent
#print axioms MetadataWriter.emit_exact
#print axioms StreamWriter.read_eos
#print axioms StreamWriter.emitFrame_exact
#print axioms StreamWriter.emit_roundtrip
#print axioms StreamWriter.emit_readRows
