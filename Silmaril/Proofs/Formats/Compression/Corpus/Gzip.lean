module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs

/-! Kernel checks for `Silmaril.Formats.Compression.Corpus.Thms`: gzip files. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem gzipNamed_decompress :
    gzipDecompress ⟨gzipNamed.toArray⟩ = some ⟨gzipNamedData.toArray⟩ := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem gzipTwoMembers_decompress :
    gzipDecompress ⟨gzipTwoMembers.toArray⟩ = some ⟨gzipTwoMembersData.toArray⟩ := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem gzipFhcrc_decompress :
    gzipDecompress ⟨gzipFhcrc.toArray⟩ = some ⟨gzipFhcrcData.toArray⟩ := by decide +kernel

end Silmaril.Proofs.Formats.Compression.Corpus
