module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs

/-! Kernel checks for `Silmaril.Formats.Compression.Corpus.Thms`: raw DEFLATE and zlib at levels 1, 6 and 9. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem rawLevel1_decoder :
    Deflate.decoder rawLevel1 = some (rawLevel1Data, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibLevel6_take : Zlib.take zlibLevel6 = some (zlibLevel6Data, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibLevel9Blocks_take :
    Zlib.take zlibLevel9Blocks = some (zlibLevel9BlocksData, []) := by decide +kernel

end Silmaril.Proofs.Formats.Compression.Corpus
