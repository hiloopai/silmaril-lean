module

import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms

open Silmaril.Formats.Parquet
open Date.Leaf.Dictionary.Snappy

#print axioms Date.Leaf.bind_exact
#print axioms Snapshot.check_groups
#print axioms stored_verified
#print axioms readEntries_wire
#print axioms planData_wire
#print axioms checkGroup_wire
#print axioms decodePage_wire
#print axioms pageWire_exact
#print axioms readGroup_wire
#print axioms readGroup_firstPageError
#print axioms readAll_firstError
#print axioms toIpc_firstError
#print axioms toIpc_readback
#print axioms decodePage_checksum_error
#print axioms toIpc_openError
