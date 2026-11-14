module

public import Silmaril.Formats.Compression.XxHash.Defs
public import Silmaril.Formats.Compression.Thms
import Silmaril.Proofs.Formats.Compression.XxHash

/-!
# xxHash: facts

Proved (standard axioms):

* `Checksum.xxh32_digest`, `Checksum.xxh64Low32_digest`, `xxh64_stream`: the
  streaming states, which buffer at most one partial stripe, compute `xxh32`,
  the low 32 bits of `xxh64`, and `xxh64`;
* known answers. The empty input, `"a"` and `"abc"` (seed 0) and
  `"Nobody inspects the spammish repetition"` are widely published vectors
  (the last is the example of the `python-xxhash` binding). The others exercise
  exactly two (XXH32) or one (XXH64) whole stripes with an empty tail, and a
  non-zero seed over four 16-byte or two 32-byte stripes; all values agree with
  an independent implementation of the specification.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace Checksum

theorem xxh32_digest (seed : UInt32) (bytes : List UInt8) :
    (xxh32 seed).digest bytes = XxHash.xxh32 seed bytes :=
  Proofs.Formats.Compression.XxHash.xxh32_digest seed bytes

theorem xxh64Low32_digest (seed : UInt64) (bytes : List UInt8) :
    (xxh64Low32 seed).digest bytes = (XxHash.xxh64 seed bytes).toUInt32 :=
  Proofs.Formats.Compression.XxHash.xxh64Low32_digest seed bytes

end Checksum

namespace XxHash

/-- The 64-bit digest of the streaming state is `xxh64`. -/
theorem xxh64_stream (seed : UInt64) (bytes : List UInt8) :
    let s := bytes.foldl (Stream.push 32 XXH64.stripe) (Stream.start (XXH64.init seed))
    XXH64.finish seed s.lanes s.length s.buffer = xxh64 seed bytes :=
  Proofs.Formats.Compression.XxHash.xxh64_stream seed bytes

/-! ## Known answers -/

/-- The 39 bytes of `"Nobody inspects the spammish repetition"`. -/
def spammish : List UInt8 :=
  [0x4E, 0x6F, 0x62, 0x6F, 0x64, 0x79, 0x20, 0x69, 0x6E, 0x73, 0x70, 0x65, 0x63, 0x74,
   0x73, 0x20, 0x74, 0x68, 0x65, 0x20, 0x73, 0x70, 0x61, 0x6D, 0x6D, 0x69, 0x73, 0x68,
   0x20, 0x72, 0x65, 0x70, 0x65, 0x74, 0x69, 0x74, 0x69, 0x6F, 0x6E]

theorem xxh32_empty : xxh32 0 [] = 0x02CC5D05 := by decide
theorem xxh32_a : xxh32 0 [0x61] = 0x550D7456 := by decide
theorem xxh32_abc : xxh32 0 [0x61, 0x62, 0x63] = 0x32D153FF := by decide
theorem xxh32_spammish : xxh32 0 spammish = 0xE2293B2F := by decide +kernel
/-- 32 bytes `'A'`: two whole stripes, no tail. -/
theorem xxh32_A32 : xxh32 0 (List.replicate 32 0x41) = 0xCF0D92E7 := by decide +kernel
/-- Bytes `00 … 3F` with seed `0x9E3779B1`: four stripes. -/
theorem xxh32_seeded :
    xxh32 0x9E3779B1 ((List.range 64).map UInt8.ofNat) = 0xD22DAE28 := by decide +kernel

theorem xxh64_empty : xxh64 0 [] = 0xEF46DB3751D8E999 := by decide
theorem xxh64_a : xxh64 0 [0x61] = 0xD24EC4F1A98C6E5B := by decide
theorem xxh64_abc : xxh64 0 [0x61, 0x62, 0x63] = 0x44BC2CF5AD770999 := by decide
theorem xxh64_spammish : xxh64 0 spammish = 0xFBCEA83C8A378BF1 := by decide +kernel
/-- 32 bytes `'A'`: one whole stripe, no tail. -/
theorem xxh64_A32 : xxh64 0 (List.replicate 32 0x41) = 0x160433E895A3D5AF := by decide +kernel
/-- Bytes `00 … 3F` with seed `0x9E3779B185EBCA87`: two stripes. -/
theorem xxh64_seeded :
    xxh64 0x9E3779B185EBCA87 ((List.range 64).map UInt8.ofNat) = 0x2006C268B7D34F54 := by
  decide +kernel

end XxHash

/-- The LZ4 content checksum of the empty input. -/
theorem Checksum.xxh32_check_empty : (Checksum.xxh32 0).digest [] = 0x02CC5D05 := by
  rw [Checksum.xxh32_digest]; exact XxHash.xxh32_empty

/-- The Zstandard content checksum of the empty input: the low half of
`0xEF46DB3751D8E999`. -/
theorem Checksum.xxh64Low32_check_empty : (Checksum.xxh64Low32 0).digest [] = 0x51D8E999 := by
  rw [Checksum.xxh64Low32_digest, XxHash.xxh64_empty]; decide

end Silmaril.Formats.Compression
