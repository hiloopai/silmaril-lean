module

import Silmaril.Formats.Arrow.StructInt32.Stream.Thms
import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Thms

open Silmaril.Formats.Arrow.StructInt32.Stream

#print axioms readRow_wire
#print axioms readRow_absent
#print axioms readRow_present_nulls
#print axioms readRows_wire
#print axioms readRecord_wire
#print axioms read_wire
#print axioms Writer.emit_readback
#print axioms Writer.emit_frames
