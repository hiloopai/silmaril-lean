module

import Silmaril.Formats.Compression.Brotli.StaticDictionary.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli.StaticDictionary

#guard canonicalBytes.size == 122784
#guard [bucketOffset 4, bucketOffset 5, bucketOffset 24, bucketOffset 25] == [0, 4096, 122016, 122784]
#guard splitAddress 4 0 = .ok ⟨4, 0, 0⟩
#guard splitAddress 4 1023 = .ok ⟨4, 1023, 0⟩
#guard splitAddress 4 1024 = .ok ⟨4, 0, 1⟩
#guard splitAddress 24 3871 = .ok ⟨24, 31, 120⟩
#guard splitAddress 24 3872 = .error .wordId
#guard splitAddress 3 0 = .error .wordLength
#guard splitAddress 25 0 = .error .wordLength
#guard (lookup 4 0).map ByteArray.toList = .ok [116, 105, 109, 101]
#guard (lookup 24 31).map ByteArray.toList =
  .ok [224, 164, 184, 224, 164, 149, 224, 165, 141, 224, 164, 176,
       224, 164, 191, 224, 164, 175, 224, 164, 164, 224, 164, 190]
#guard (lookup 24 32).map ByteArray.toList = .error .wordIndex
#guard (lookup 25 0).map ByteArray.toList = .error .wordLength
