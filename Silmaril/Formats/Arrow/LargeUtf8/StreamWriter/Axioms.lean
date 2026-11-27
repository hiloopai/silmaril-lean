module

import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Thms
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms

open Silmaril.Formats.Arrow

#print axioms LargeUtf8.StreamWriter.schema_extent
#print axioms LargeUtf8.StreamWriter.encodeValue_octets
#print axioms LargeUtf8.StreamWriter.encodeColumn_dataSize
#print axioms LargeUtf8.StreamWriter.emit_readback
#print axioms Binary.StreamWriter.serializeProfile_exact
