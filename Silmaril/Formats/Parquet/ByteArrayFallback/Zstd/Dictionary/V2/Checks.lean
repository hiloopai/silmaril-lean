module

import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Thms

open Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2

#print axioms readDictionary_checksum_error
#print axioms readDictionary_wire
#print axioms decodePage_checksum_error
#print axioms decodePage_wire
#print axioms decodePage_plain
#print axioms suffix_profile
#print axioms readFrames_wire
#print axioms readFrames_first_page_error
#print axioms readGroup_wire
#print axioms convert_readback
#print axioms convert_first_error
