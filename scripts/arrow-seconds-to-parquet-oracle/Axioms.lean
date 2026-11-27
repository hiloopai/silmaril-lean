module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Thms
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds

#print axioms admit_exact
#print axioms rescale_seconds
#print axioms seconds_inverse
#print axioms overflow_iff
#print axioms rescaleSlot_overflow
#print axioms prepare_exact
#print axioms convert_source_error
#print axioms rescaleBatch_first_error
#print axioms convert_first_rescale_error
#print axioms convert_readback
#print axioms convert_inverse
#print axioms convert_source_eos

#print axioms Silmaril.Formats.Parquet.Timestamp.FromIpc.certify_readback
