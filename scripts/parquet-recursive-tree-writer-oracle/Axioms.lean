module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms Tree.Writer.emit_wire
#print axioms Tree.Writer.ColumnWire.footer_exact
#print axioms Tree.Writer.GroupsReadback.group_at
#print axioms Tree.Writer.GroupReadback.original_group
#print axioms Tree.Rows.GroupResult.order
#print axioms Tree.Rows.project_exact
#print axioms Tree.Rows.CheckedColumn.wire
#print axioms Tree.LeafBinding.original_page
#print axioms Repeated.Writer.Schema.wrap_bytes
#print axioms ListPath.Writer.frameSize_exact
