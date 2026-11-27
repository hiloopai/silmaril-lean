module

import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Thms

open Silmaril.Formats.Arrow.MixedFlat.Timestamp
open Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc

#print axioms readSchema_wire
#print axioms readParsed_wire
#print axioms read_wire
#print axioms Writer.emitRecord_wire
#print axioms Writer.emit_readback
#print axioms Writer.emit_wire
#print axioms fields_position
#print axioms batchInput_exact
#print axioms convert_open_error
#print axioms convert_read_error
#print axioms convert_readback
