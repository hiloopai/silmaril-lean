module

import Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Thms
import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Thms

open Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv

#print axioms Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.decode_agrees
#print axioms convert_readback
#print axioms roundtrip
#print axioms convert_csv_error
#print axioms convert_writer_error
