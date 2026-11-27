module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms ScalarDispatch.checkGroup_wire
#print axioms ScalarDispatch.route_ok_iff
#print axioms ScalarDispatch.decodePage_wire
#print axioms ScalarDispatch.readGroup_wire
#print axioms ScalarDispatch.readGroup_first_page_error
#print axioms ScalarDispatch.readGroup_agrees_delta
#print axioms ScalarDispatch.readGroup_agrees_split
#print axioms ScalarDispatch.readGroup_agrees_plain
#print axioms ScalarDispatch.readGroup_agrees_plain_v2_uncompressed
#print axioms ScalarDispatch.readGroup_agrees_plain_v2_snappy
#print axioms ScalarDispatch.convert_agrees
#print axioms ScalarDispatch.convert_readback
#print axioms ScalarDispatch.decodePage_branch
#print axioms ScalarDispatch.decodePage_route_error
#print axioms ScalarDispatch.readBound_first_error
#print axioms ScalarDispatch.convert_first_error
#print axioms Events.ToIpc.selectedBinding_exact
