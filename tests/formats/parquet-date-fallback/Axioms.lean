module

import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms

open Silmaril.Formats.Parquet

#print axioms Snapshot.check_groups
#print axioms Date.Leaf.bind_exact
#print axioms Date.Leaf.Dictionary.checkGroup_exact
#print axioms Date.Leaf.Dictionary.decodePage_wire
#print axioms Date.Leaf.Dictionary.pageWire_exact
#print axioms Date.Leaf.Fallback.checkSequence_wire
#print axioms Date.Leaf.Fallback.checkGroup_wire
#print axioms Date.Leaf.Fallback.decodePage_wire
#print axioms Date.Leaf.Fallback.readGroup_wire
#print axioms Date.Leaf.Fallback.plainWire_exact
#print axioms Date.Leaf.Fallback.readGroup_firstPageError
#print axioms Date.Leaf.Fallback.readAll_firstError
#print axioms Date.Leaf.Fallback.toIpc_firstError
#print axioms Date.Leaf.Fallback.toIpc_readback
