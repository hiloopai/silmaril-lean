module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms Dictionary.frameGroupUsing_wire
#print axioms Gzip.Dispatch.V1.profile_fallback_iff
#print axioms Gzip.Dispatch.V1.planGroup_wire
#print axioms Gzip.Dispatch.V1.readGroup_matches
#print axioms Gzip.Dispatch.V1.framing_error
#print axioms Gzip.Dispatch.V1.readGroup_wire
#print axioms Gzip.Dispatch.V1.readBound_first_error
#print axioms Gzip.Dispatch.V1.convert_first_error
#print axioms Gzip.Dispatch.V1.convert_readback
