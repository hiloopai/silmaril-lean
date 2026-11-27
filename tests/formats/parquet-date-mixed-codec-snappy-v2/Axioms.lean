module

import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Thms

open Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy

#print axioms readGroup_twoCodec_agrees
#print axioms readGroup_selectionError
#print axioms readGroup_unsupportedCodec
#print axioms readGroup_gzip_agrees
#print axioms readGroup_zstd_agrees
#print axioms readGroup_snappy_agrees
#print axioms readGroup_wire
#print axioms readAll_firstError
#print axioms toIpc_firstError
#print axioms toIpc_readback
