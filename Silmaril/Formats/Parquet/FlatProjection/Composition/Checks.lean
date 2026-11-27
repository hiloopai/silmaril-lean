module

import Silmaril.Formats.Parquet.FlatProjection.Composition.Thms
import Silmaril.Formats.Parquet.FlatProjection.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms

open Silmaril.Formats.Parquet.FlatProjection
open Silmaril.Formats.Parquet.FlatProjection.Composition

#print axioms bindProjection_lookup
#print axioms open_bindings
#print axioms bound_read_congr
#print axioms group_lookup
#print axioms select_map
#print axioms select_bound
#print axioms project_compose
#print axioms project_rowCounts
#print axioms Silmaril.Formats.Parquet.Int32ByteArrayGroup.decoders_congr
#print axioms open_compose
#print axioms project_compose_success
#print axioms project_compose_of_caps
