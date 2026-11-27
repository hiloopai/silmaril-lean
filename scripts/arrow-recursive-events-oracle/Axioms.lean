module

import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms

open Silmaril.Formats.Arrow.RecursiveSchema
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

#print axioms Batch.Rows.RowFits.cell_at
#print axioms Stream.CursorChain.record_of_mem
#print axioms Stream.RecordWire.rows
#print axioms declarations_signature
#print axioms eraseRow_ofRow
#print axioms eraseBatch_ofBatch
#print axioms eraseBatches_ofTrace
#print axioms read_open_error
#print axioms read_wire
#print axioms read_failure
#print axioms read_eos
#print axioms projectTrace_counts
#print axioms projectTrace_termination
#print axioms projectTrace_rows
#print axioms projectTrace_id
#print axioms projectTrace_comp
