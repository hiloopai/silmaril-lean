module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms MixedCodec.V2.selectedCodec_exact
#print axioms MixedCodec.V2.readGroup_selection_error
#print axioms MixedCodec.V2.readGroup_unsupported_codec
#print axioms MixedCodec.V2.readGroup_gzip_agrees
#print axioms MixedCodec.V2.readGroup_zstd_agrees
#print axioms MixedCodec.V2.readGroup_wire
#print axioms MixedCodec.V2.trace_first_error
#print axioms MixedCodec.V2.convert_first_error
#print axioms MixedCodec.V2.convert_readback
#print axioms Gzip.Dispatch.V2.planDictionary_wire
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Zstd.Dispatch.V2.planDictionary_wire
#print axioms Zstd.Dispatch.V2.readGroup_wire
#print axioms Events.ToIpc.selectedBinding_exact
