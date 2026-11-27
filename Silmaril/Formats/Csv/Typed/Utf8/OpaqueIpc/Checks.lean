module

import Silmaril.Formats.Csv.Typed.Codecs.Hex.Thms
import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Thms

open Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

#print axioms Silmaril.Formats.Csv.Typed.Codecs.Hex.parsePrint
#print axioms Silmaril.Formats.Csv.Typed.Codecs.Hex.printParse
#print axioms decode_encode
#print axioms toCsv_observation
#print axioms emitIpc_readback
#print axioms fromCsv_readback
#print axioms roundtrip
