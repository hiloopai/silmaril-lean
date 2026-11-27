module

import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Thms

open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

#print axioms read_emittedWith
#print axioms Rows.toTable_columns
#print axioms prepare_observe
#print axioms emitted_table
#print axioms convert_readback
#print axioms encoded_readback
#print axioms convert_source_error
