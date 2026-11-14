module

public import Silmaril.Formats.Compression.Defs

/-!
# xxHash: XXH32 and XXH64

The non-cryptographic hashes XXH32 and XXH64, following the numbered steps of
the xxHash specification (`doc/xxhash_spec.md`, version 0.1.1): initialise four
accumulators from the seed, consume the input in stripes of four lanes (16 bytes
for XXH32, 32 for XXH64), converge the accumulators (XXH64 then merges each of
them back in), add the input length, consume the remaining bytes, avalanche.
Inputs shorter than one stripe skip the stripe steps and start from
`seed + PRIME_5`.

Compressed formats use them as content checksums: the LZ4 frame format stores
`xxh32 0` of the content (and optionally of each block), and Zstandard
(RFC 8878 §3.1.1) stores the low 32 bits of `xxh64 0` of the content. Both write
the value little-endian (`le32`), not in xxHash's big-endian "canonical" form.

* `xxh32 seed bytes : UInt32`, `xxh64 seed bytes : UInt64`: the hashes;
* `Stream`, `Stream.push`: the running state of a streaming implementation, the
  stripe accumulators plus a partial stripe of fewer than 16 (or 32) bytes;
* `Checksum.xxh32 seed`: XXH32 as a framework `Checksum`;
* `Checksum.xxh64Low32 seed`: the low 32 bits of XXH64 (zstd's
  `Content_Checksum`) as a `Checksum`. The full 64-bit digest of a stream is
  `XXH64.finish` of its state (`Checksum` finishes into `UInt32`).

xxHash is not a byte-at-a-time fold: whole stripes are mixed into the
accumulators, and the remaining bytes are mixed with different rounds only
once the length is known. It still fits `Checksum` because the state buffers
the partial stripe; `XxHash.Thms` proves that the streaming digests equal
`xxh32` and `xxh64`.

## References

* Yann Collet, *xxHash fast digest algorithm*, specification version 0.1.1,
  <https://github.com/Cyan4973/xxHash/blob/dev/doc/xxhash_spec.md>.
* The LZ4 frame format,
  <https://github.com/lz4/lz4/blob/dev/doc/lz4_Frame_format.md>.
* RFC 8878, *Zstandard Compression and the 'application/zstd' Media Type*.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace XxHash

/-! ## Words and stripes -/

/-- The little-endian value of a byte string. -/
def leNat (bytes : List UInt8) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- Rotate left by `r`. Shift amounts are taken modulo 32, so this is a rotation
for every `r`. -/
def rotl32 (x r : UInt32) : UInt32 := (x <<< r) ||| (x >>> (32 - r))

/-- Rotate left by `r`. Shift amounts are taken modulo 64, so this is a rotation
for every `r`. -/
def rotl64 (x r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))

/-- The four accumulators of the stripe loop. -/
structure Lanes (α : Type) where
  v1 : α
  v2 : α
  v3 : α
  v4 : α

/-- Mix whole stripes of `width` bytes into the accumulators with `step`, while
at least `width` bytes remain; return the accumulators and the remaining bytes.
`fuel` bounds the number of stripes: the input length is always enough. -/
def stripes {σ : Type} (width : Nat) (step : σ → List UInt8 → σ) :
    Nat → σ → List UInt8 → σ × List UInt8
  | 0, acc, bytes => (acc, bytes)
  | fuel + 1, acc, bytes =>
    if width ≤ bytes.length then
      stripes width step fuel (step acc (bytes.take width)) (bytes.drop width)
    else (acc, bytes)

/-! ## XXH32 -/

namespace XXH32

def prime1 : UInt32 := 0x9E3779B1
def prime2 : UInt32 := 0x85EBCA77
def prime3 : UInt32 := 0xC2B2AE3D
def prime4 : UInt32 := 0x27D4EB2F
def prime5 : UInt32 := 0x165667B1

/-- A little-endian 32-bit lane. -/
def lane (bytes : List UInt8) : UInt32 := (leNat bytes).toUInt32

def round (acc input : UInt32) : UInt32 := rotl32 (acc + input * prime2) 13 * prime1

/-- Step 1: the accumulators before the first stripe. -/
def init (seed : UInt32) : Lanes UInt32 := ⟨seed + prime1 + prime2, seed + prime2, seed, seed - prime1⟩

/-- Step 2: one 16-byte stripe, a 4-byte lane per accumulator. -/
def stripe (v : Lanes UInt32) (s : List UInt8) : Lanes UInt32 :=
  ⟨round v.v1 (lane (s.take 4)), round v.v2 (lane ((s.drop 4).take 4)),
   round v.v3 (lane ((s.drop 8).take 4)), round v.v4 (lane ((s.drop 12).take 4))⟩

/-- Step 3: accumulator convergence. -/
def converge (v : Lanes UInt32) : UInt32 :=
  rotl32 v.v1 1 + rotl32 v.v2 7 + rotl32 v.v3 12 + rotl32 v.v4 18

/-- Step 5: the remaining bytes, as 4-byte lanes and then single bytes. -/
def tail : Nat → UInt32 → List UInt8 → UInt32
  | 0, h, _ => h
  | fuel + 1, h, bytes =>
    if 4 ≤ bytes.length then
      tail fuel (rotl32 (h + lane (bytes.take 4) * prime3) 17 * prime4) (bytes.drop 4)
    else
      match bytes with
      | [] => h
      | b :: rest => tail fuel (rotl32 (h + b.toUInt32 * prime5) 11 * prime1) rest

/-- Step 6: the final mix. -/
def avalanche (h : UInt32) : UInt32 :=
  let h := (h ^^^ (h >>> 15)) * prime2
  let h := (h ^^^ (h >>> 13)) * prime3
  h ^^^ (h >>> 16)

/-- Steps 3–6, from the stripe accumulators `v`, the input length `len` and the
bytes after the last stripe. Inputs shorter than a stripe start from
`seed + PRIME32_5` instead (step 1). -/
def finish (seed : UInt32) (v : Lanes UInt32) (len : Nat) (rest : List UInt8) : UInt32 :=
  let h := if len < 16 then seed + prime5 else converge v
  avalanche (tail rest.length (h + len.toUInt32) rest)

end XXH32

/-- **XXH32** of `bytes` with `seed`. -/
def xxh32 (seed : UInt32) (bytes : List UInt8) : UInt32 :=
  let (v, rest) := stripes 16 XXH32.stripe bytes.length (XXH32.init seed) bytes
  XXH32.finish seed v bytes.length rest

/-! ## XXH64 -/

namespace XXH64

def prime1 : UInt64 := 0x9E3779B185EBCA87
def prime2 : UInt64 := 0xC2B2AE3D27D4EB4F
def prime3 : UInt64 := 0x165667B19E3779F9
def prime4 : UInt64 := 0x85EBCA77C2B2AE63
def prime5 : UInt64 := 0x27D4EB2F165667C5

/-- A little-endian 64-bit lane. -/
def lane (bytes : List UInt8) : UInt64 := (leNat bytes).toUInt64

def round (acc input : UInt64) : UInt64 := rotl64 (acc + input * prime2) 31 * prime1

def mergeRound (acc v : UInt64) : UInt64 := (acc ^^^ round 0 v) * prime1 + prime4

/-- Step 1: the accumulators before the first stripe. -/
def init (seed : UInt64) : Lanes UInt64 := ⟨seed + prime1 + prime2, seed + prime2, seed, seed - prime1⟩

/-- Step 2: one 32-byte stripe, an 8-byte lane per accumulator. -/
def stripe (v : Lanes UInt64) (s : List UInt8) : Lanes UInt64 :=
  ⟨round v.v1 (lane (s.take 8)), round v.v2 (lane ((s.drop 8).take 8)),
   round v.v3 (lane ((s.drop 16).take 8)), round v.v4 (lane ((s.drop 24).take 8))⟩

/-- Steps 3 and 4: accumulator convergence, then each accumulator merged in. -/
def converge (v : Lanes UInt64) : UInt64 :=
  let h := rotl64 v.v1 1 + rotl64 v.v2 7 + rotl64 v.v3 12 + rotl64 v.v4 18
  mergeRound (mergeRound (mergeRound (mergeRound h v.v1) v.v2) v.v3) v.v4

/-- Step 6: the remaining bytes, as 8-byte lanes, then at most one 4-byte lane,
then single bytes. -/
def tail : Nat → UInt64 → List UInt8 → UInt64
  | 0, h, _ => h
  | fuel + 1, h, bytes =>
    if 8 ≤ bytes.length then
      tail fuel (rotl64 (h ^^^ round 0 (lane (bytes.take 8))) 27 * prime1 + prime4) (bytes.drop 8)
    else if 4 ≤ bytes.length then
      tail fuel (rotl64 (h ^^^ lane (bytes.take 4) * prime1) 23 * prime2 + prime3) (bytes.drop 4)
    else
      match bytes with
      | [] => h
      | b :: rest => tail fuel (rotl64 (h ^^^ b.toUInt64 * prime5) 11 * prime1) rest

/-- Step 7: the final mix. -/
def avalanche (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 33)) * prime2
  let h := (h ^^^ (h >>> 29)) * prime3
  h ^^^ (h >>> 32)

/-- Steps 3–7, from the stripe accumulators `v`, the input length `len` and the
bytes after the last stripe. Inputs shorter than a stripe start from
`seed + PRIME64_5` instead (step 1). -/
def finish (seed : UInt64) (v : Lanes UInt64) (len : Nat) (rest : List UInt8) : UInt64 :=
  let h := if len < 32 then seed + prime5 else converge v
  avalanche (tail rest.length (h + len.toUInt64) rest)

end XXH64

/-- **XXH64** of `bytes` with `seed`. -/
def xxh64 (seed : UInt64) (bytes : List UInt8) : UInt64 :=
  let (v, rest) := stripes 32 XXH64.stripe bytes.length (XXH64.init seed) bytes
  XXH64.finish seed v bytes.length rest

/-! ## Streaming -/

/-- The running state of a streaming xxHash: the stripe accumulators, the bytes
of the current partial stripe, and the number of bytes absorbed. -/
structure Stream (σ : Type) where
  lanes : σ
  buffer : List UInt8
  length : Nat

/-- Absorb one byte: buffer it, and mix the buffer in once it is a whole stripe
of `width` bytes. -/
def Stream.push {σ : Type} (width : Nat) (step : σ → List UInt8 → σ) (s : Stream σ)
    (b : UInt8) : Stream σ :=
  let buffer := s.buffer ++ [b]
  if width ≤ buffer.length then ⟨step s.lanes buffer, [], s.length + 1⟩
  else ⟨s.lanes, buffer, s.length + 1⟩

/-- The stream before any input. -/
def Stream.start {σ : Type} (lanes : σ) : Stream σ := ⟨lanes, [], 0⟩

end XxHash

open XxHash in
/-- XXH32 with `seed` as an incremental checksum (the LZ4 frame checksums use
seed 0). -/
def Checksum.xxh32 (seed : UInt32) : Checksum where
  State := Stream (Lanes UInt32)
  init := .start (XXH32.init seed)
  update := Stream.push 16 XXH32.stripe
  finish s := XXH32.finish seed s.lanes s.length s.buffer

open XxHash in
/-- The low 32 bits of XXH64 with `seed` as an incremental checksum (Zstandard's
`Content_Checksum` uses seed 0). -/
def Checksum.xxh64Low32 (seed : UInt64) : Checksum where
  State := Stream (Lanes UInt64)
  init := .start (XXH64.init seed)
  update := Stream.push 32 XXH64.stripe
  finish s := (XXH64.finish seed s.lanes s.length s.buffer).toUInt32

end Silmaril.Formats.Compression
