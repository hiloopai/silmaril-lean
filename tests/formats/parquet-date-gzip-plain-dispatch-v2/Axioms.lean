module

import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms Gzip.V2.pageWire_exact
#print axioms Gzip.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.readGroup_wire
#print axioms Gzip.Dispatch.V2.WithPlain.route_selected
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_routeError
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_plain_agrees
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_dictionaryBacked_agrees
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_dictionary_agrees
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_fallback_agrees
#print axioms Gzip.Dispatch.V2.WithPlain.readGroup_wire
#print axioms Gzip.Dispatch.V2.WithPlain.readAll_firstError
#print axioms Gzip.Dispatch.V2.WithPlain.toIpc_firstError
#print axioms Gzip.Dispatch.V2.WithPlain.toIpc_readback
