module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

#print axioms Reader.readGroup_wire
#print axioms Reader.ToIpc.convert_open_error
#print axioms Reader.ToIpc.convert_source_error
#print axioms Reader.ToIpc.convert_readback
#print axioms Reader.ToIpc.convert_exact_eos
#print axioms Reader.ToIpc.agrees_events
#print axioms Writer.emit_wire
#print axioms Writer.FromIpc.convert_open_error
#print axioms Writer.FromIpc.convert_terminal_wire
#print axioms Writer.FromIpc.convert_declaration_wire
#print axioms Writer.FromIpc.convert_readback
#print axioms Writer.FromIpc.round_trip
#print axioms Writer.FromIpc.round_trip_parquet
