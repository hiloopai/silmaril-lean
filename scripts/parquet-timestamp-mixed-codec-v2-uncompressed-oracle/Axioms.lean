module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms MixedCodec.V2.WithUncompressed.selectedCodec_exact
#print axioms MixedCodec.V2.WithUncompressed.readGroup_uncompressed_agrees
#print axioms MixedCodec.V2.WithUncompressed.readGroup_threeCodec_agrees
#print axioms MixedCodec.V2.WithUncompressed.readGroup_snappy_agrees
#print axioms MixedCodec.V2.WithUncompressed.readGroup_gzip_agrees
#print axioms MixedCodec.V2.WithUncompressed.readGroup_zstd_agrees
#print axioms MixedCodec.V2.WithUncompressed.readGroup_wire
#print axioms MixedCodec.V2.WithUncompressed.trace_first_error
#print axioms MixedCodec.V2.WithUncompressed.convert_first_error
#print axioms MixedCodec.V2.WithUncompressed.convert_readback
#print axioms MixedCodec.V2.WithUncompressed.trace_threeCodec_agrees
#print axioms MixedCodec.V2.WithUncompressed.convert_threeCodec_agrees
#print axioms Uncompressed.Dispatch.V2.planDictionary_wire
#print axioms Uncompressed.Dispatch.V2.readGroup_wire
#print axioms Snappy.Dispatch.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Zstd.Dispatch.V2.readGroup_wire
#print axioms MixedCodec.V2.WithSnappy.readGroup_wire
#print axioms Events.ToIpc.selectedBinding_exact
