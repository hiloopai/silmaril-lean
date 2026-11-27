module

import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Thms

open Silmaril.Formats.Parquet

#print axioms Date.Leaf.Dictionary.Zstd.V2.readEntries_wire
#print axioms Date.Leaf.Dictionary.Zstd.V2.decodePage_wire
#print axioms Date.Leaf.Zstd.V2.decodePage_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.planData_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.planPages_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.planPages_reentry
#print axioms Date.Leaf.Fallback.Zstd.V2.checkGroup_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.checkGroup_dictionary
#print axioms Date.Leaf.Fallback.Zstd.V2.transition_totals
#print axioms Date.Leaf.Fallback.Zstd.V2.decodePage_checksum_error
#print axioms Date.Leaf.Fallback.Zstd.V2.decodePage_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.readGroup_wire
#print axioms Date.Leaf.Fallback.Zstd.V2.readGroup_firstPageError
#print axioms Date.Leaf.Fallback.Zstd.V2.readAll_firstError
#print axioms Date.Leaf.Fallback.Zstd.V2.toIpc_firstError
#print axioms Date.Leaf.Fallback.Zstd.V2.toIpc_readback
