module

public import Silmaril.Data.IncludeBytes.Types

/-! # Pinned files as blobs, by arithmetic on `include_bytes` chunks (`Silmaril.Elf.Pin`)

`include_bytes` elaborates a file to `IncludeBytes.decode chunk len [c₀, c₁, …]`: chunk literals
`cᵢ`, each `chunk` bytes little-endian (the last one `len - chunk · i`). The blob the ELF
specification reads (`blobOf`) is a number and a length. `chunksVal` and `chunksLen` compute them
from the chunk literals alone, so the kernel compares a pinned file with another blob by Nat
arithmetic on a few literals (GMP), without decoding a byte (`blobOf_decode` in `Thms`).

This is what makes **file identity** a theorem rather than metadata: two pins of the same file (a
`Blob` literal and an `include_bytes` pin, `Examples`) are proved equal, where comparing their
paths and SHA-256 strings would only compare what each declares. -/

@[expose] public section

namespace Silmaril.Elf.Pin

/-- The value of the chunks: `c₀ mod 2^(8·k₀) + 2^(8·k₀) · (the rest)`, with `k₀ = min chunk len`. -/
def chunksVal (chunk : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | len, c :: cs => c % 2 ^ (8 * min chunk len) + 2 ^ (8 * min chunk len) * chunksVal chunk (len - chunk) cs

/-- The number of bytes the chunks decode to. -/
def chunksLen (chunk : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | len, _ :: cs => min chunk len + chunksLen chunk (len - chunk) cs

end Silmaril.Elf.Pin

end
