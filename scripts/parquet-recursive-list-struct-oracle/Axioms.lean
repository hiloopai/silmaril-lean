module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.Repeated

#print axioms Compiled.original
#print axioms Chunk.read_wire
#print axioms Rows.partition_wire
#print axioms Rows.ColumnWire.original_atoms
#print axioms Rows.readGroup_wire
#print axioms Rows.readAll_wire
#print axioms Rows.listStruct_steps
#print axioms Rows.listStruct_projection_topology
#print axioms Rows.readGroup_listStruct_wire
