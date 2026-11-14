module

public import Silmaril.Formats.Compression.ContainerSpec.Thms
public import Silmaril.Proofs.Formats.Compression.ContainerSpec
public import Silmaril.Proofs.Formats.Compression.Corpus.Deflate
public import Silmaril.Proofs.Formats.Compression.Corpus.Strategies
public import Silmaril.Proofs.Formats.Compression.Corpus.Flush
public import Silmaril.Proofs.Formats.Compression.Corpus.Gzip
public import Silmaril.Proofs.Formats.Compression.Corpus.Rejects

/-! The corpus as instances of the independent specifications. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Corpus

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Corpus

theorem rawLevel1_stream : DeflateSpec.Stream .strict rawLevel1 rawLevel1Data [] :=
  ContainerSpec.deflate_decoder_eq_some.1 rawLevel1_decoder

/-- `zlibDict` sets `FDICT`, so it is a dictionary member and not a plain one. -/
theorem zlibDict_member : ContainerSpec.ZlibDictMember dictionary zlibDict zlibDictData [] := by
  rcases ContainerSpec.zlib_takeWithDictionary_iff.1 zlibDict_takeWithDictionary with h | h
  · have := ContainerSpec.zlib_take_iff.2 h
    rw [zlibDict_take] at this
    cases this
  · exact h

end Silmaril.Proofs.Formats.Compression.Corpus
