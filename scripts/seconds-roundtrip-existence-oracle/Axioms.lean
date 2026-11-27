module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Thms
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Thms
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence

#print axioms emit_iff_sink
#print axioms rescale_of_recovery
#print axioms rescale_writer_image
#print axioms roundtrip_of_sink
#print axioms roundtrip_exists

#print axioms Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.convert_image
#print axioms Silmaril.Formats.Parquet.Timestamp.FromIpc.certifyWith_readback
