module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs

/-! Kernel checks for `Silmaril.Formats.Compression.Corpus.Thms`: corrupted vectors. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badBody_take : Zlib.take badBody = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badHeader_take : Zlib.take badHeader = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badAdler_take : Zlib.take badAdler = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badCrc_decompress : gzipDecompress ⟨badCrc.toArray⟩ = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badIsize_decompress : gzipDecompress ⟨badIsize.toArray⟩ = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badHcrc_decompress : gzipDecompress ⟨badHcrc.toArray⟩ = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem badReserved_decompress : gzipDecompress ⟨badReserved.toArray⟩ = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibDict_take : Zlib.take zlibDict = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibDict_wrongDictionary :
    Zlib.takeWithDictionary wrongDictionary zlibDict = none := by decide +kernel

end Silmaril.Proofs.Formats.Compression.Corpus
