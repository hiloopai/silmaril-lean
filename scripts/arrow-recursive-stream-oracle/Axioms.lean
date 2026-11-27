module

import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

open Silmaril.Formats.Arrow.RecursiveSchema
open Silmaril.Formats.Arrow.RecursiveSchema.Stream

#print axioms readFrame_source
#print axioms Batch.readFrame_of_envelope
#print axioms poll_wire
#print axioms readTrace_wire
#print axioms RecordWire.coordinates
#print axioms readTrace_open_error
#print axioms CursorChain.end_wire
#print axioms readTrace_eos
#print axioms readTrace_failure
#print axioms read_iff
