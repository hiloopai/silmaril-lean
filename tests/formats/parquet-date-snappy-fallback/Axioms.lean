module

import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Thms

open Silmaril.Formats.Parquet

#print axioms Date.Leaf.bind_exact
#print axioms Date.Leaf.Dictionary.Snappy.stored_verified
#print axioms Date.Leaf.Dictionary.Snappy.planDataWith_wire
#print axioms Date.Leaf.Dictionary.Snappy.checkGroupWith_wire
#print axioms Date.Leaf.Dictionary.Snappy.verifyData_wire
#print axioms Date.Leaf.Dictionary.Snappy.pageWire_exact
#print axioms Date.Leaf.Fallback.Snappy.planPrefix_firstError
#print axioms Date.Leaf.Fallback.Snappy.planPages_earlierPhaseError
#print axioms Date.Leaf.Fallback.Snappy.planPages_headerError
#print axioms Date.Leaf.Fallback.Snappy.planPages_wire
#print axioms Date.Leaf.Fallback.Snappy.checkGroup_wire
#print axioms Date.Leaf.Fallback.Snappy.transition_totals
#print axioms Date.Leaf.Fallback.Snappy.decodePage_wire
#print axioms Date.Leaf.Fallback.Snappy.plainWire_exact
#print axioms Date.Leaf.Fallback.Snappy.readGroup_wire
#print axioms Date.Leaf.Fallback.Snappy.readGroup_firstPageError
#print axioms Date.Leaf.Fallback.Snappy.readAll_firstError
#print axioms Date.Leaf.Fallback.Snappy.toIpc_firstError
#print axioms Date.Leaf.Fallback.Snappy.toIpc_readback
