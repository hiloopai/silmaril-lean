module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms

open Silmaril.Formats

#print axioms Arrow.RecursiveSchema.Stream.Events.ToIpc.schemaOf_exact
#print axioms Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_read_error
#print axioms Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_readback
#print axioms Arrow.RecursiveSchema.Stream.Events.ToIpc.agrees_events
#print axioms Parquet.Reader.Recursive.Selection.batches_exact
#print axioms Parquet.RecursiveSchema.TwoListStruct.Reader.Events.readProjected_wire

open Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

#print axioms convert_open_error
#print axioms convert_source_error
#print axioms convert_readback
#print axioms convert_exact_eos
#print axioms agrees_events
