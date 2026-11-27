module

import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary

#print axioms readDictionary_wire
#print axioms dictionary_member
#print axioms decodePage_wire
#print axioms decodePage_plain
#print axioms data_member
#print axioms readGroup_wire
#print axioms convert_readback
#print axioms convert_first_error

#print axioms Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.readDictionaryBytesWith_wire
#print axioms Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.decodeIndexPageWith_wire
