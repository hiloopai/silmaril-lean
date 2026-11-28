module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms Tree.LeafPath.projected_levels
#print axioms Tree.LeafPath.scan_levels
#print axioms Tree.LeafBinding.read_wire
#print axioms Tree.LeafBinding.original_page
#print axioms Tree.LeafBinding.read_page_failure
#print axioms ListPath.Chunk.decodePage_wire
#print axioms ListPath.Chunk.decodeV2Page_wire
#print axioms ListPath.Chunk.readCarrier_wire
#print axioms Tree.Rows.project_exact
#print axioms Tree.Rows.readGroupChecked_join_failure
#print axioms Tree.Rows.Events.ProjectedWire.groups
#print axioms Tree.Rows.Events.ToIpc.convert_readback
#print axioms Tree.Rows.Events.ToIpc.convert_group_failure
