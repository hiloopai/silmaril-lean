module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection

#print axioms readAll_opened
#print axioms bindOrdinals_first_error
#print axioms openFile_bound
#print axioms openFile_selected
#print axioms readCounts_failure
#print axioms readGroup_first_column_error
#print axioms readGroup_footer
#print axioms readGroup_column
#print axioms readGroup_project
#print axioms projected_group_succeeds_iff
#print axioms trace_first_error
#print axioms trace_eos_iff
#print axioms trace_project_prefix
#print axioms trace_scan
#print axioms trace_scan_equivalent
#print axioms projected_eos_but_full_fails_iff
