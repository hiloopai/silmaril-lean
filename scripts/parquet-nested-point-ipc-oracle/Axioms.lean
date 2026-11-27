module

import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms

open Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc

#print axioms Silmaril.Formats.Parquet.Snapshot.check_bytes
#print axioms openFile_wire
#print axioms readGroup_wire
#print axioms readAll_reader
#print axioms convert_trace
#print axioms convert_open_error
#print axioms convert_first_error
#print axioms nativeBatches_of_groups
#print axioms convert_readback
