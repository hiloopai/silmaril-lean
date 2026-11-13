module

public import Silmaril.Formats.Compression.Defs
public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Formats.Compression.Deflate.WithHistory

/-!
# DEFLATE (RFC 1951)

The raw DEFLATE format, as a member `Decoder` of the compression framework. The
specification is a total, list-based, fuel-bounded decoder; it is not an
optimised implementation (an `Array`-accumulating mirror is registered with
`@[csimp]` for evaluation).

* `deflateTake bytes`: decode the DEFLATE stream at the front of `bytes`
  (`BFINAL`-terminated blocks; stored, fixed-Huffman and dynamic-Huffman blocks;
  reserved `BTYPE = 11` and distance codes 30/31 rejected) and return the output
  and the unread, byte-aligned remainder;
* `decoder`: `deflateTake` as a framework `Decoder`; `encoder`: the stored-block
  (`BTYPE = 00`) writer `storedBytes`; `encoderFixed`: the compressing encoder
  (`compress`, as a list function);
* `decompress`, `Compresses data c`: the whole-buffer `ByteArray` decoder and its
  relation (`decompress c = some data`);
* `compress`: a greedy LZ77 matcher with one fixed-Huffman block;
* `deflateTakeWithHistory`: decoding with a preset history (zlib dictionaries);
* `validCodeLengths`: the decoder accepts dynamic code lengths only when the
  code is complete (or the degenerate single-code case RFC 1951 §3.2.7 allows);
  `isValidLengths` is the Kraft inequality; `fixedLitLenLengths`,
  `fixedDistLengths`: the RFC 1951 §3.2.6 fixed codes.

`Task.local` is the append law for DEFLATE members; it is proved as
`Deflate.local` (see `Deflate.Thms`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- The RFC 1951 member decoder. -/
abbrev decoder : Decoder := Decoder.ofExcept deflateTake

/-- The stored-block encoder: correct and linear-time, it does not shrink data. -/
abbrev encoder : Encoder := storedBytes

/-- The **compressing** encoder: greedy LZ77 matching and one fixed-Huffman block
(`compress`). `compress` never fails (`compress_isSome`), so the stored fallback
is unreachable; it only makes the encoder total by definition. -/
def encoderFixed : Encoder := fun data =>
  match compress ⟨data.toArray⟩ with
  | some c => c.data.toList
  | none => storedBytes data

/-- Bytes after a DEFLATE member never change its decoding. **Proved** as
`Deflate.local` (and `Deflate.task_local`): every decoder stage is monotone under
appended input, and its fuel (`bitsLeft + 1`) only grows. The definition is kept
for compatibility with statements that take it as a hypothesis. -/
def Task.local : Prop := decoder.Local

end Silmaril.Formats.Compression.Deflate
