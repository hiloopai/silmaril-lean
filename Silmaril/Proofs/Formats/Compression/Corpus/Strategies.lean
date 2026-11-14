module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs

/-! Kernel checks for `Silmaril.Formats.Compression.Corpus.Thms`: zlib strategies. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibHuffmanOnly_take :
    Zlib.take zlibHuffmanOnly = some (zlibHuffmanOnlyData, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibRle_take : Zlib.take zlibRle = some (zlibRleData, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibFixed_take : Zlib.take zlibFixed = some (zlibFixedData, []) := by decide +kernel

end Silmaril.Proofs.Formats.Compression.Corpus
