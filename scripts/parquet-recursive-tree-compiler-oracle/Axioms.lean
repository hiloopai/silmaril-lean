module

import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms Tree.Compiled.original_nodes
#print axioms Tree.Compiled.leaf_order
#print axioms Tree.Compiled.leaf_ordinals_increase
#print axioms Tree.Compiled.leaf_column
#print axioms Tree.Compiled.leaf_original
#print axioms Tree.Compiled.leaf_coverage
#print axioms Tree.Compiled.distinct_ordinals
#print axioms Tree.Compiled.same_ordinal
#print axioms Tree.Compiled.shared_ancestor
#print axioms Tree.LeafPath.steps_prefix
#print axioms Tree.LeafPath.nullable_level
#print axioms Tree.LeafPath.repeated_level
#print axioms Tree.LeafPath.projected_levels
#print axioms Tree.LeafBinding.read_wire
#print axioms Repeated.Compiled.steps_original
