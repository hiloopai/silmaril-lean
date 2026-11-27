module

import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs
meta import Batteries.Data.Except

namespace Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform

private def transformed (ordinal : Nat) (word : List UInt8) : Except Error (List UInt8) :=
  (applyTransform ordinal ⟨word.toArray⟩).map (·.data.toList)

#guard transformed 0 [97, 98, 99, 100] = .ok [97, 98, 99, 100]
#guard transformed 73 [97, 98, 99, 100] = .ok (" the abcd of the ".toUTF8.toList)
#guard transformed 102 [97, 98, 99, 100] = .ok [0xc2, 0xa0, 97, 98, 99, 100]
#guard transformed 120 [97, 98, 99, 100] = .ok (" Abcd='".toUTF8.toList)
#guard transformed 3 [97, 98, 99, 100] = .ok [98, 99, 100]
#guard transformed 12 [97, 98, 99, 100] = .ok [97, 98, 99]
#guard transformed 34 [97, 98, 99, 100] = .ok []
#guard transformed 54 [97, 98, 99, 100] = .ok []
#guard transformed 64 [97, 98, 99, 100] = .ok []
#guard transformed 9 [0xc3, 0xa9, 97, 122] = .ok [0xc3, 0x89, 97, 122]
#guard transformed 44 [0xe2, 0x82, 0xac, 122] = .ok [0xe2, 0x82, 0xa9, 90]
#guard transformed 44 [0xf0, 0x9f, 0x98, 0x80, 97] = .ok [0xf0, 0x9f, 0x9d, 0x80, 65]
#guard transformed 44 [97, 98, 99, 0xc0] = .ok [65, 66, 67, 0xc0]
#guard transformed 44 [97, 98, 0xe0, 0x80] = .ok [65, 66, 0xe0, 0x80]
#guard transformed 121 [97, 98, 99, 100] = .error .transformOrdinal
#guard transformed 121 [97, 98, 99] = .error .baseLength
#guard transformed 0 (List.replicate 25 97) = .error .baseLength
#guard (transformed 73 (List.replicate 24 97)).map List.length = .ok 37

#guard (materialize 4 0).map (·.data.toList) = .ok [116, 105, 109, 101]
#guard (materialize 4 (121 * wordCount 4 - 1)).isOk
#guard (materialize 4 (121 * wordCount 4)).map ByteArray.size = .error (.address .wordId)
#guard (materialize 3 0).map ByteArray.size = .error (.address .wordLength)

end Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform
