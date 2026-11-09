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
  (`BTYPE = 00`) writer `storedBytes`;
* `decompress`, `Compresses data c`: the whole-buffer `ByteArray` decoder and its
  relation (`decompress c = some data`);
* `compress`: a greedy LZ77 matcher with one fixed-Huffman block;
* `deflateTakeWithHistory`: decoding with a preset history (zlib dictionaries);
* `validCodeLengths`: the decoder accepts dynamic code lengths only when the
  code is complete (or the degenerate single-code case RFC 1951 §3.2.7 allows);
  `isValidLengths` is the Kraft inequality; `fixedLitLenLengths`,
  `fixedDistLengths`: the RFC 1951 §3.2.6 fixed codes.

`Task.local` (frozen, open) is the append law for DEFLATE members (see
`Deflate.Thms`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- The RFC 1951 member decoder. -/
abbrev decoder : Decoder := Decoder.ofExcept deflateTake

/-- The stored-block encoder: correct and linear-time, it does not shrink data. -/
abbrev encoder : Encoder := storedBytes

/-- **Open (frozen):** bytes after a DEFLATE member never change its decoding.
Proved for stored encodings (`roundTrip`); the general law needs monotonicity of
every decoder stage, whose fuel (`bitsLeft + 1`) grows with appended input.
`Inflate.deflate_local_of_task` derives it from completeness of the streaming
raw inflater. -/
def Task.local : Prop := decoder.Local

end Silmaril.Formats.Compression.Deflate
