module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms ScalarDispatch.checkGroup_wire
#print axioms ScalarDispatch.checkGroup_encodings
#print axioms ScalarDispatch.route_ok_iff
#print axioms ScalarDispatch.decodePage_branch
#print axioms ScalarDispatch.decodePage_wire
#print axioms ScalarDispatch.decodeZstd_wire
#print axioms ScalarDispatch.gzipWire_extents
#print axioms ScalarDispatch.zstdWire_extents
#print axioms ScalarDispatch.readGroup_wire
#print axioms ScalarDispatch.readGroup_first_page_error
#print axioms ScalarDispatch.readBound_first_error
#print axioms ScalarDispatch.convert_first_error
#print axioms ScalarDispatch.convert_readback
#print axioms ScalarDispatch.readGroup_agrees_gzip_v2
#print axioms ScalarDispatch.readGroup_agrees_zstd_v2
#print axioms ScalarDispatch.convert_agrees
