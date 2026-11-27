import Silmaril.Formats.Parquet.Footer.PageLessRecursive.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms

open Silmaril.Formats.Parquet

#print axioms Footer.PageLessRecursive.empty_counts
#print axioms Footer.PageLessRecursive.groupStop_empty
#print axioms Snapshot.checkRecursive_exact
#print axioms RecursiveSchema.Repeated.Chunk.read_wire
#print axioms RecursiveSchema.Repeated.Chunk.Wire.noSpan
#print axioms RecursiveSchema.Repeated.Rows.readAll_wire
#print axioms RecursiveSchema.Repeated.Rows.Events.read_eos
#print axioms RecursiveSchema.Repeated.Rows.Events.readProjected_preserves
#print axioms RecursiveSchema.Repeated.Rows.ToIpc.convert_readback
