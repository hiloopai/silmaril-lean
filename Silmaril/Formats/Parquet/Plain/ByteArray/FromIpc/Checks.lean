module

import Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Thms
import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Thms

open Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File (emit_ofSlots_readback)

#print axioms Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Input.ofSlots_exact
#print axioms emit_ofSlots_readback
#print axioms readSource_exact
#print axioms Source.slots_octets
#print axioms convert_readback
#print axioms convert_source_error
#print axioms convert_wrong_kind
#print axioms convert_writer_error
