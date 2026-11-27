module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer.Readback
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column.Writer.Layout

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column.Writer

theorem join_spec (pieces : List KBytes) (wf : ∀ piece ∈ pieces, piece.wf = true) :
    (join pieces).wf = true ∧ (join pieces).toList = pieces.flatMap KBytes.toList ∧
      (join pieces).len = (pieces.map KBytes.len).sum :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.join_spec pieces wf

/-- Successful emission fixes the node, buffer extents, validity, and exact
inline and external byte windows in logical row order. -/
theorem emitBinary_layout {limits : Limits} {nullable : Bool} {values : List (Option KBytes)}
    {result : Emitted} (written : emitBinary limits nullable values = .ok result) :
    Layout limits nullable values result :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.emitBinary_layout written

/-- The checked reader recovers the same ordered nullable octets for any
well-formed segmentation of the supplied values. -/
theorem emitBinary_roundtrip {limits : Limits} {nullable : Bool}
    {values : List (Option KBytes)} {result : Emitted} (written : emitBinary limits nullable values = .ok result) :
    ∃ decoded, BinaryView.Column.readBinary limits result.node nullable result.buffers = .ok decoded ∧
      decoded.map (·.map KBytes.toList) = values.map (·.map KBytes.toList) :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.emitBinary_roundtrip written

theorem utf8Bytes_valid (text : String) : String.fromUTF8? (utf8Bytes text).toByteArray = some text :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.utf8Bytes_valid text

/-- Utf8View uses the same byte layout with the exact UTF-8 payloads of the
input strings. The cutoff and limits are measured in bytes. -/
theorem emitUtf8_layout {limits : Limits} {nullable : Bool} {values : List (Option String)}
    {result : Emitted} (written : emitUtf8 limits nullable values = .ok result) :
    Layout limits nullable (values.map (·.map utf8Bytes)) result :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.emitUtf8_layout written

theorem emitUtf8_roundtrip {limits : Limits} {nullable : Bool}
    {values : List (Option String)} {result : Emitted} (written : emitUtf8 limits nullable values = .ok result) :
    BinaryView.Column.readUtf8 limits result.node nullable result.buffers = .ok values :=
  Proofs.Formats.Arrow.BinaryView.Column.Writer.emitUtf8_roundtrip written

end Silmaril.Formats.Arrow.BinaryView.Column.Writer
