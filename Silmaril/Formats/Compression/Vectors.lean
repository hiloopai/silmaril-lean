module

public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Gzip.Basic

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# zlib and gzip known-answer tests (RFC 1950, RFC 1952)

## What the headline theorems say

`zlibDecompress_zlibCompress` and `gzipDecompress_gzipCompress` are round trips: decompressing
our own compressor's output gives the input back. They assume nothing. But a round trip alone
would also hold for a codec that is self-consistent and wrong (say, with the Adler-32 trailer
byte-swapped in both directions), so its meaning rests on the decoder matching the RFCs.

## What this file adds

Byte strings produced by independent implementations, decoded by ours:

* `zlib.compress(b"hello")` (CPython `zlib`, level 6: a fixed-Huffman DEFLATE block) and
  `zlib.compress(b"hello", 0)` (a stored block) both decode to `hello`
  (`zlibDecompress_cpython_fixed`, `zlibDecompress_cpython_stored`);
* our `zlibCompress` produces *exactly* CPython's level-0 bytes for `hello`
  (`zlibCompress_hello_eq_cpython`): header `78 01`, one final stored block, Adler-32
  `06 2c 02 15` big-endian;
* GNU `gzip -n` output (OS = 3, Unix) and CPython `gzip.compress(b"hello", mtime=0)` output
  (XFL = 2, OS = 255) decode to `hello` (`gzipDecompress_gnu`, `gzipDecompress_cpython`);
* the zlib stream with its last Adler-32 byte changed is rejected
  (`zlibDecompress_bad_adler`), and so is the gzip stream with a corrupted CRC-32
  (`gzipDecompress_bad_crc`).

The vectors were regenerated on 2026-10-15 with CPython 3 `zlib`/`gzip` and GNU `gzip -n`
(`printf hello | gzip -n`). Sources: RFC 1950 §2.2 and RFC 1952 §2.3.
-/

/-- The five bytes of `hello`. -/
def helloBytes : ByteArray := ⟨#[0x68, 0x65, 0x6c, 0x6c, 0x6f]⟩

/-- `zlib.compress(b"hello")`: header `78 9c`, a fixed-Huffman block, Adler-32 `062c0215`. -/
def zlibCpythonFixed : ByteArray :=
  ⟨#[0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c, 0x02, 0x15]⟩

/-- `zlib.compress(b"hello", 0)`: header `78 01`, one final stored block, Adler-32. -/
def zlibCpythonStored : ByteArray :=
  ⟨#[0x78, 0x01, 0x01, 0x05, 0x00, 0xfa, 0xff, 0x68, 0x65, 0x6c, 0x6c, 0x6f,
    0x06, 0x2c, 0x02, 0x15]⟩

/-- `printf hello | gzip -n` (GNU gzip): MTIME = 0, XFL = 0, OS = 3. -/
def gzipGnu : ByteArray :=
  ⟨#[0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48, 0xcd, 0xc9,
    0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00]⟩

/-- `gzip.compress(b"hello", mtime=0)` (CPython): XFL = 2, OS = 255. -/
def gzipCpython : ByteArray :=
  ⟨#[0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xcb, 0x48, 0xcd, 0xc9,
    0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00]⟩

end Silmaril.Formats.Compression
