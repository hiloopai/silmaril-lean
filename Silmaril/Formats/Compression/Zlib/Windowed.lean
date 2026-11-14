module

public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Deflate.Profile

/-!
# zlib profiles: the `CINFO` window and dictionaries for every window size

RFC 1950 §2.2: "CINFO is the base-2 logarithm of the LZ77 window size, minus
eight (CINFO=7 indicates a 32K window size)". `Zlib.take` does not bound
back-reference distances by that window, and neither does zlib's `inflate`
unless it is built with `INFLATE_STRICT` (`inflate.c` then rejects a distance
above `dmax = 1 << (CINFO + 8)`: "invalid distance too far back"). Observed:
zlib 1.3.1 (default build) accepts the `CINFO = 0` member with distance 257 of
`ContainerSpec.zlibWindowOnly`, with `windowBits` 15 and 8. This module adds
separately named profiles; the existing decoders are unchanged.

* `takeWindowed`: `Zlib.take` with every distance at most `2 ^ (CINFO + 8)`;
* `takeWithDictionaryAnyWindow`: `takeWithDictionary` for every `CINFO`, not just
  7. The dictionary is installed as history; as distances are at most 32768,
  only its last 32 KiB can be referenced (and only those are passed to the raw
  decoder), whatever `CINFO` says;
* `takeWithDictionaryWindowed`: both, so distances are at most
  `2 ^ (CINFO + 8)`, and only the last `2 ^ (CINFO + 8)` bytes of the dictionary
  can be referenced (only those are passed to the raw decoder).

zlib's `inflateSetDictionary` keeps the last `wsize` bytes of a dictionary, where
`wsize = 1 << wbits` is the window of the *inflate stream* (the `windowBits`
given to `inflateInit2`, or `CINFO + 8` when that was 0), not necessarily the
header's `CINFO` (our reading of zlib 1.3.1's `inflate.c`, not formalized). With
the default `windowBits = 15`, zlib therefore keeps the last 32 KiB, as
`takeWithDictionaryAnyWindow` does.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zlib

open ZlibDictionary

/-- The window a zlib header announces: `2 ^ (CINFO + 8)` bytes. -/
def windowSize (cmf : UInt8) : Nat := 2 ^ (cmf.toNat / 16 + 8)

/-- **Strict-window zlib member decoder**: `Zlib.take`, with every
back-reference distance at most the header's window `2 ^ (CINFO + 8)`. -/
def takeWindowed (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  match bytes with
  | [] => none
  | cmf :: _ =>
    match zlibCheckHeader bytes with
    | none => none
    | some body => finish (Deflate.deflateTakeProfile (.windowed (windowSize cmf)) body)

/-- A member with an offered preset dictionary, for every `CINFO`: a member
without `FDICT` ignores the dictionary; with `FDICT`, the dictionary's Adler-32
must equal `DICTID` and its last 32 KiB are the DEFLATE history. -/
def takeWithDictionaryAnyWindow (dictionary input : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  (checkHeader input).bind fun (header, body) =>
    match header.dictionaryID with
    | none => finish (Deflate.deflateTake body)
    | some expected =>
      if dictionaryChecksum dictionary = expected then
        finish (Deflate.deflateTakeWithHistory (history dictionary) body)
      else none

/-- `takeWithDictionaryAnyWindow` with every distance at most the header's window
`2 ^ (CINFO + 8)`; the history is the last `2 ^ (CINFO + 8)` dictionary bytes. -/
def takeWithDictionaryWindowed (dictionary input : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  (checkHeader input).bind fun (header, body) =>
    match header.dictionaryID with
    | none => finish (Deflate.deflateTakeProfile (.windowed (2 ^ header.windowBits)) body)
    | some expected =>
      if dictionaryChecksum dictionary = expected then
        finish (Deflate.deflateTakeWithHistoryProfile (.windowed (2 ^ header.windowBits))
          (dictionary.drop (dictionary.length - 2 ^ header.windowBits)) body)
      else none

end Silmaril.Formats.Compression.Zlib
