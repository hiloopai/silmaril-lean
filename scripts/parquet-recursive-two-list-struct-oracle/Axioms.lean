module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms ListPath.Chunk.readCarrier_wire
#print axioms ListPath.Rows.reconstruct_wire
#print axioms TwoListStruct.Source.bytes_exact
#print axioms TwoListStruct.Reader.Plan.path_levels
#print axioms TwoListStruct.Rows.addressed_atoms
#print axioms TwoListStruct.Rows.addressed_slot
#print axioms TwoListStruct.Rows.checkTopology_wire
#print axioms TwoListStruct.Rows.checkTopology_failure
#print axioms TwoListStruct.Rows.mergeRows_wire
#print axioms TwoListStruct.Reader.readColumn_wire
#print axioms TwoListStruct.Reader.readGroup_wire
#print axioms TwoListStruct.Reader.readGroup_topology_failure
#print axioms TwoListStruct.Reader.readAll_wire
