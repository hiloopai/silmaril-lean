module

import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Thms
import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Thms

open Silmaril.Formats.Parquet.NestedPoint.Multi.Writer

#print axioms levelPair_contract
#print axioms emit_readback
#print axioms FromIpc.bind_exact
#print axioms FromIpc.convert_source_error
#print axioms FromIpc.convert_readback
#print axioms FromIpc.roundtrip_ipc
