module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms MixedCodec.V2.WithSnappy.selectedCodec_exact
#print axioms MixedCodec.V2.WithSnappy.readGroup_snappy_agrees
#print axioms MixedCodec.V2.WithSnappy.readGroup_twoCodec_agrees
#print axioms MixedCodec.V2.WithSnappy.readGroup_gzip_agrees
#print axioms MixedCodec.V2.WithSnappy.readGroup_zstd_agrees
#print axioms MixedCodec.V2.WithSnappy.readGroup_wire
#print axioms MixedCodec.V2.WithSnappy.trace_first_error
#print axioms MixedCodec.V2.WithSnappy.convert_first_error
#print axioms MixedCodec.V2.WithSnappy.convert_readback
#print axioms MixedCodec.V2.WithSnappy.trace_twoCodec_agrees
#print axioms MixedCodec.V2.WithSnappy.convert_twoCodec_agrees
#print axioms MixedCodec.V2.traceUsing_first_error
#print axioms MixedCodec.V2.traceUsing_eos
#print axioms MixedCodec.V2.emitUsing_readback
#print axioms MixedCodec.V2.readGroup_wire
#print axioms Snappy.Dispatch.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Zstd.Dispatch.V2.readGroup_wire
#print axioms Events.ToIpc.selectedBinding_exact
