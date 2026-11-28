module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms ListPath.Rows.reconstruct_wire
#print axioms ListPath.Rows.reconstruct_of_relation

open TwoListStruct

#print axioms openRequired_exact
#print axioms Reader.Plan.path_levels
#print axioms Reader.Plan.optional_step
#print axioms Rows.mergeRows_wire
#print axioms Rows.mergeRows_typed
#print axioms Reader.readGroup_wire
#print axioms Reader.readGroup_typed
#print axioms Reader.readGroup_topology_failure
#print axioms Reader.Events.readProjected_wire
#print axioms Reader.ToIpc.convert_source_error
#print axioms Writer.certify_readback
#print axioms Writer.FromIpc.convert_declaration_error
