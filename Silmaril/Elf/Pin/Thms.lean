module

public import Silmaril.Elf.Pin.Defs
public import Silmaril.Elf.Parse.Defs
import Silmaril.Proofs.Elf.Pin

/-! # Pinned files as blobs: theorems

* `blobOf_decode`: the blob of an `include_bytes` file is `⟨chunksVal …, chunksLen …⟩`, computed
  from its chunk literals. With `unfold` of the pin's `raw` (which exposes `decode chunk len [c₀,
  …]`) and `decide +kernel`, an equality of a pinned file with a `Blob` literal costs Nat
  arithmetic on the literals, not a decoding of the bytes (`Examples`). -/

@[expose] public section

namespace Silmaril.Elf.Pin

open Silmaril.IncludeBytes

theorem blobOf_decode (chunk len : Nat) (cs : List Nat) :
    Silmaril.Elf.blobOf ⟨decode chunk len cs⟩ = ⟨chunksVal chunk len cs, chunksLen chunk len cs⟩ :=
  Silmaril.Proofs.Elf.Pin.blobOf_decode chunk len cs

end Silmaril.Elf.Pin

end
