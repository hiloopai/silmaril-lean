module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy

#print axioms stored_wire
#print axioms readDictionary_wire
#print axioms decodePage_wire
#print axioms storedBytes_chain
#print axioms readGroup_wire
#print axioms convert_readback
#print axioms convert_first_error
