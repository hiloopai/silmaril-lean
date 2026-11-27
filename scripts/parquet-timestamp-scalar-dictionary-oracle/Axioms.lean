module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms ScalarAndDictionary.codec_ok_iff
#print axioms ScalarAndDictionary.classify_ok_iff
#print axioms ScalarAndDictionary.selectedColumn_ok_iff
#print axioms ScalarAndDictionary.route_ok_iff
#print axioms ScalarAndDictionary.readGroup_scalar_agrees
#print axioms ScalarAndDictionary.readGroup_uncompressed_agrees
#print axioms ScalarAndDictionary.readGroup_snappy_agrees
#print axioms ScalarAndDictionary.readGroup_gzip_agrees
#print axioms ScalarAndDictionary.readGroup_zstd_agrees
#print axioms ScalarAndDictionary.readGroup_wire
#print axioms ScalarAndDictionary.trace_first_error
#print axioms ScalarAndDictionary.convert_first_error
#print axioms ScalarAndDictionary.convert_readback
#print axioms ScalarAndDictionary.dictionaryEncodings_ok_iff
#print axioms ScalarAndDictionary.classify_codec_error
#print axioms ScalarAndDictionary.classify_dictionary_error
#print axioms ScalarAndDictionary.readGroup_route_error
#print axioms Events.ToIpc.selectedBinding_exact
