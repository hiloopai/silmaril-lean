module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds

#print axioms binding_exact
#print axioms millis_nonintegral_iff
#print axioms millis_exact
#print axioms rescaleSlot_nonintegral
#print axioms rescaleGroups_exact
#print axioms readGroups_agree
#print axioms convert_first_source_error
#print axioms rescaleGroup_first_error
#print axioms convert_first_rescale_error
#print axioms convert_readback
#print axioms ipc_roundtrip
#print axioms convert_output_eos
