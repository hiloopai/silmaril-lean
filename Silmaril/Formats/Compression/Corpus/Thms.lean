module

public import Silmaril.Formats.Compression.Corpus.Defs
public import Silmaril.Formats.Compression.ContainerSpec.Thms
public import Silmaril.Formats.Compression.DeflateSpec.Thms
import Silmaril.Proofs.Formats.Compression.Corpus.Spec

/-!
# The external-encoder corpus: checked

Checked by kernel evaluation (`decide +kernel`) in
`Silmaril.Proofs.Formats.Compression.Corpus.*`; no compiled evaluation.

* Every vector of `Corpus.Defs`, produced by zlib 1.3.1 through CPython 3.13.5,
  decodes to exactly the data it was made from: raw DEFLATE through
  `Deflate.decoder`, zlib through `Zlib.take`, the preset-dictionary member
  through `Zlib.takeWithDictionary`, gzip files (one or two members, FNAME,
  MTIME, all optional fields with FHCRC) through `gzipDecompress`.
* Through the soundness theorems these are instances of the independent
  specifications: `DeflateSpec.Stream`, `ContainerSpec.ZlibMember`,
  `ZlibDictMember` and `GzipFile` (`*_spec`).
* Every corrupted vector is rejected: a flipped bit in a dynamic block header, in
  `FLG` (`FCHECK`), in the Adler-32, CRC-32 and `ISIZE` trailers, in FHCRC, a
  reserved `FLG` bit, the dictionary member without or with a wrong dictionary.

These are decoder checks against an independent encoder, not round trips of
this library's encoders.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Corpus

/-! ## Accepted, with zlib's data -/

theorem rawLevel1_decoder : Deflate.decoder rawLevel1 = some (rawLevel1Data, []) :=
  Proofs.Formats.Compression.Corpus.rawLevel1_decoder

theorem zlibLevel6_take : Zlib.take zlibLevel6 = some (zlibLevel6Data, []) :=
  Proofs.Formats.Compression.Corpus.zlibLevel6_take

theorem zlibLevel9Blocks_take : Zlib.take zlibLevel9Blocks = some (zlibLevel9BlocksData, []) :=
  Proofs.Formats.Compression.Corpus.zlibLevel9Blocks_take

theorem zlibHuffmanOnly_take : Zlib.take zlibHuffmanOnly = some (zlibHuffmanOnlyData, []) :=
  Proofs.Formats.Compression.Corpus.zlibHuffmanOnly_take

theorem zlibRle_take : Zlib.take zlibRle = some (zlibRleData, []) :=
  Proofs.Formats.Compression.Corpus.zlibRle_take

theorem zlibFixed_take : Zlib.take zlibFixed = some (zlibFixedData, []) :=
  Proofs.Formats.Compression.Corpus.zlibFixed_take

theorem zlibFlushes_take : Zlib.take zlibFlushes = some (zlibFlushesData, []) :=
  Proofs.Formats.Compression.Corpus.zlibFlushes_take

theorem zlibWindow9_take : Zlib.take zlibWindow9 = some (zlibWindow9Data, []) :=
  Proofs.Formats.Compression.Corpus.zlibWindow9_take

theorem zlibDict_takeWithDictionary :
    Zlib.takeWithDictionary dictionary zlibDict = some (zlibDictData, []) :=
  Proofs.Formats.Compression.Corpus.zlibDict_takeWithDictionary

theorem gzipNamed_decompress : gzipDecompress ⟨gzipNamed.toArray⟩ = some ⟨gzipNamedData.toArray⟩ :=
  Proofs.Formats.Compression.Corpus.gzipNamed_decompress

theorem gzipTwoMembers_decompress :
    gzipDecompress ⟨gzipTwoMembers.toArray⟩ = some ⟨gzipTwoMembersData.toArray⟩ :=
  Proofs.Formats.Compression.Corpus.gzipTwoMembers_decompress

theorem gzipFhcrc_decompress : gzipDecompress ⟨gzipFhcrc.toArray⟩ = some ⟨gzipFhcrcData.toArray⟩ :=
  Proofs.Formats.Compression.Corpus.gzipFhcrc_decompress

/-! ## As instances of the specifications -/

theorem rawLevel1_spec : DeflateSpec.Stream .strict rawLevel1 rawLevel1Data [] :=
  Proofs.Formats.Compression.Corpus.rawLevel1_stream

theorem zlibLevel6_spec : ContainerSpec.ZlibMember zlibLevel6 zlibLevel6Data [] :=
  ContainerSpec.zlib_take_iff.1 zlibLevel6_take

theorem zlibLevel9Blocks_spec : ContainerSpec.ZlibMember zlibLevel9Blocks zlibLevel9BlocksData [] :=
  ContainerSpec.zlib_take_iff.1 zlibLevel9Blocks_take

theorem zlibHuffmanOnly_spec : ContainerSpec.ZlibMember zlibHuffmanOnly zlibHuffmanOnlyData [] :=
  ContainerSpec.zlib_take_iff.1 zlibHuffmanOnly_take

theorem zlibRle_spec : ContainerSpec.ZlibMember zlibRle zlibRleData [] :=
  ContainerSpec.zlib_take_iff.1 zlibRle_take

theorem zlibFixed_spec : ContainerSpec.ZlibMember zlibFixed zlibFixedData [] :=
  ContainerSpec.zlib_take_iff.1 zlibFixed_take

theorem zlibFlushes_spec : ContainerSpec.ZlibMember zlibFlushes zlibFlushesData [] :=
  ContainerSpec.zlib_take_iff.1 zlibFlushes_take

theorem zlibWindow9_spec : ContainerSpec.ZlibMember zlibWindow9 zlibWindow9Data [] :=
  ContainerSpec.zlib_take_iff.1 zlibWindow9_take

theorem gzipNamed_spec : ContainerSpec.GzipFile gzipNamed gzipNamedData :=
  ContainerSpec.gzipDecompress_iff.1 gzipNamed_decompress

theorem gzipTwoMembers_spec : ContainerSpec.GzipFile gzipTwoMembers gzipTwoMembersData :=
  ContainerSpec.gzipDecompress_iff.1 gzipTwoMembers_decompress

theorem gzipFhcrc_spec : ContainerSpec.GzipFile gzipFhcrc gzipFhcrcData :=
  ContainerSpec.gzipDecompress_iff.1 gzipFhcrc_decompress

theorem zlibDict_spec : ContainerSpec.ZlibDictMember dictionary zlibDict zlibDictData [] :=
  Proofs.Formats.Compression.Corpus.zlibDict_member

/-! ## Rejected -/

theorem badBody_take : Zlib.take badBody = none :=
  Proofs.Formats.Compression.Corpus.badBody_take

theorem badHeader_take : Zlib.take badHeader = none :=
  Proofs.Formats.Compression.Corpus.badHeader_take

theorem badAdler_take : Zlib.take badAdler = none :=
  Proofs.Formats.Compression.Corpus.badAdler_take

theorem badCrc_decompress : gzipDecompress ⟨badCrc.toArray⟩ = none :=
  Proofs.Formats.Compression.Corpus.badCrc_decompress

theorem badIsize_decompress : gzipDecompress ⟨badIsize.toArray⟩ = none :=
  Proofs.Formats.Compression.Corpus.badIsize_decompress

theorem badHcrc_decompress : gzipDecompress ⟨badHcrc.toArray⟩ = none :=
  Proofs.Formats.Compression.Corpus.badHcrc_decompress

theorem badReserved_decompress : gzipDecompress ⟨badReserved.toArray⟩ = none :=
  Proofs.Formats.Compression.Corpus.badReserved_decompress

theorem zlibDict_take : Zlib.take zlibDict = none :=
  Proofs.Formats.Compression.Corpus.zlibDict_take

theorem zlibDict_wrongDictionary : Zlib.takeWithDictionary wrongDictionary zlibDict = none :=
  Proofs.Formats.Compression.Corpus.zlibDict_wrongDictionary

end Silmaril.Formats.Compression.Corpus
