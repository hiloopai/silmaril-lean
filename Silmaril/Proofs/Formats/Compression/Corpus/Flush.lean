module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs

/-! Kernel checks for `Silmaril.Formats.Compression.Corpus.Thms`: flushes, a small window and a preset dictionary. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibFlushes_take : Zlib.take zlibFlushes = some (zlibFlushesData, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibWindow9_take : Zlib.take zlibWindow9 = some (zlibWindow9Data, []) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zlibDict_takeWithDictionary :
    Zlib.takeWithDictionary dictionary zlibDict = some (zlibDictData, []) := by decide +kernel

end Silmaril.Proofs.Formats.Compression.Corpus
