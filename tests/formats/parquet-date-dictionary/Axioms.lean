module

import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Thms

open Silmaril.Formats.Parquet.Date.Leaf

#print axioms bind_exact
#print axioms selectChunk_exact
#print axioms Events.traceWith_firstError
#print axioms Events.traceWith_eof
#print axioms Events.emitWith_readback
#print axioms Dictionary.readGroup_exact
#print axioms Dictionary.pageWire_exact
#print axioms Dictionary.readAll_firstError
#print axioms Dictionary.toIpc_firstError
#print axioms Dictionary.toIpc_readback
#print axioms Dictionary.toIpc_openError
