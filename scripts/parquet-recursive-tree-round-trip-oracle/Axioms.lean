module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms

open Silmaril.Formats Parquet.RecursiveSchema

#print axioms Tree.RoundTrip.ipc_projected
#print axioms Tree.RoundTrip.ipc_identity
#print axioms Tree.RoundTrip.parquet_identity
#print axioms Tree.Writer.FromIpc.convert_readback
#print axioms Tree.Rows.Events.ToIpc.convert_readback
#print axioms Tree.Rows.Events.projected_observations
#print axioms Tree.Rows.project_exact
#print axioms Tree.LeafBinding.original_page
