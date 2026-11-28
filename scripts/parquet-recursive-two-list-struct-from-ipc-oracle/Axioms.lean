module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms

open Silmaril.Formats

#print axioms Arrow.RecursiveSchema.Stream.Import.admit_iff
#print axioms Arrow.RecursiveSchema.Stream.Import.admit_wire
#print axioms Arrow.RecursiveSchema.Stream.Import.admit_terminal_wire

open Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc

#print axioms convert_open_error
#print axioms convert_terminal_error
#print axioms convert_terminal_wire
#print axioms convert_of_strict
#print axioms convert_declaration_error
#print axioms convert_declaration_wire
#print axioms convert_writer_wire
#print axioms convert_readback
#print axioms round_trip
