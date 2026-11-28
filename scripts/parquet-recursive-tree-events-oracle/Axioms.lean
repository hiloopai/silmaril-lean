module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.Tree

#print axioms Rows.Projection.trace_typed
#print axioms Rows.GroupResult.typed
#print axioms Rows.readGroup_checked
#print axioms Rows.Events.read_open_error
#print axioms Rows.Events.readProjected_open_error
#print axioms Rows.Events.readSource_wire
#print axioms Rows.Events.read_wire
#print axioms Rows.Events.SourceWire.failure
#print axioms Rows.Events.readSource_complete
#print axioms Rows.Events.erase_projectColumns
#print axioms Rows.Events.projected_observations
#print axioms Rows.Events.readProjected_wire
#print axioms Rows.Events.ProjectedWire.groups
#print axioms Rows.Events.projected_failure
