module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

open Silmaril.Formats Parquet.RecursiveSchema

#print axioms Tree.Writer.FromIpc.convert_open_error
#print axioms Tree.Writer.FromIpc.convert_terminal_error
#print axioms Tree.Writer.FromIpc.convert_terminal_wire
#print axioms Tree.Writer.FromIpc.convert_of_strict
#print axioms Tree.Writer.FromIpc.convert_writer_wire
#print axioms Tree.Writer.FromIpc.convert_readback
#print axioms Tree.Writer.FromIpc.batch_group
#print axioms Arrow.RecursiveSchema.Stream.Import.admit_wire
#print axioms Arrow.RecursiveSchema.Stream.Import.admit_terminal_wire
#print axioms Arrow.RecursiveSchema.Stream.RecordWire.coordinates
#print axioms Tree.Writer.GroupReadback.original_group
#print axioms Tree.Rows.project_exact
#print axioms Tree.Rows.CheckedColumn.wire
