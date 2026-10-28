module

public import Silmaril.Crypto.X86.Sha256O2
public import Silmaril.Crypto.X86.Lifted.Sha256ClangO2
public import Silmaril.X86.Lift.Step

/-!
# The clang `-O2` `sha256_compress` image, read through its transcription

`Lifted.Sha256ClangO2` is the kernel-checked transcription of the 459 bytes
that `tools/x86-lift` produced (`transcript_verify`, by `decide +kernel`). This
module makes it the single source of decode facts for the execution proof in
`Sha256O2/Exec.lean`, and extends it from the unrelocated bytes to the loaded
image at **every** layout.

* `decode_raw`: a listed instruction is what `Ext.decode` reads from its slice
  of `raw`. An execution proof asks for this at each step; it is now a lookup
  into the listing (`at?`) rather than a fresh run of the decoder over a byte
  slice.
* `image_decode`: the relocated image `image textBase rodataBase` decodes, for
  every `textBase` and `rodataBase`, to `imageListing`: the transcription with
  the `lea` at `0xd4` carrying the relocated displacement `kLeaDisp`. The other
  132 instructions are the transcription's, unchanged. This is the theorem
  `Sha256O2/Decode.lean` deferred ("`decodeLengths_image` is a check at one
  layout, not a theorem about all of them"), proved through the generic
  `Lift.decodeFrom_splice`.

The relocation lemmas `kLeaDisp`, `image_lea_slice` and `image_decode_lea`
lived in `Exec.lean`; they are here now, next to the theorem that uses them.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.X86 (Word Reg)
open Silmaril.X86.Ext (decode)
open Silmaril.X86.Decompile (Decoded Region at? decodeFrom)

namespace Lifted
export Silmaril.Crypto.X86.Lifted.Sha256ClangO2 (listing region fuel verified bytes_eq_Sha256O2_raw)
end Lifted

/-! ## Decode facts from the listing -/

/-- The transcription's region is `raw` at section offset `0x20`. -/
theorem lifted_region : Lifted.region = ⟨0x20, raw⟩ := by
  simp only [Silmaril.Crypto.X86.Lifted.Sha256ClangO2.region, Lifted.bytes_eq_Sha256O2_raw]

/-- **A decode fact is a lookup.** If the listing has `i`, `n` bytes long, at
function offset `o` (section address `o + 0x20`), then `Ext.decode` reads `i`
from `n` bytes of `raw` at `o`. The hypothesis is closed by `decide +kernel`:
`at?` compares addresses, and only the one entry found is compared. -/
theorem decode_raw {o n : Nat} {i : Silmaril.X86.Ext.Instr}
    (h : at? Lifted.listing (o + 0x20) = some ⟨o + 0x20, i, n⟩) :
    decode ((raw.drop o).take n) = some (i, n) := by
  have hv : (⟨0x20, raw⟩ : Region).decode? Lifted.fuel = some Lifted.listing := by
    rw [← lifted_region]; exact Lifted.verified.decode?
  have := Silmaril.X86.Lift.decode_of_at hv h
  simpa using this

/-! ## The relocated `lea`

The `lea` at function offset 180 carries the single `R_X86_64_PC32`
displacement, so its seven bytes depend on where the object is loaded and no
closed `decide` reaches it. **It is the only layout-dependent instruction in
the function.**

What closes it is Track 1's `Ext.encode_lea_rip`: the encoding of
`lea r, [rip + d]` is three fixed bytes and `imm32Bytes d`. That is the fact
that **relocation is a local edit** — `encodeMem` for a `.rip` base does not
inspect the displacement at all, it emits `.d32 m.disp` unconditionally — so
the seven image bytes at offset 180 *are* the canonical encoding, and
`Ext.decode_encode` finishes it. -/

/-- The operand the relocated `lea` decodes to: RIP-relative, displacement
`S + A - P`. -/
def kLeaDisp (L : Layout) : BitVec 32 :=
  (L.rodataBase - L.textBase - BitVec.ofNat 64 (relocOffset + 4)).setWidth 32

/-- The relocated `lea` itself. -/
abbrev kLea (L : Layout) : Silmaril.X86.Ext.Instr :=
  .lea .q .rcx (Silmaril.X86.Ext.Mem.ofRip (kLeaDisp L))

theorem kLea_length (L : Layout) : (Silmaril.X86.Ext.encode (kLea L)).length = 7 := by
  simp

theorem imm32Bytes_eq (v : BitVec 32) :
    [v.setWidth 8, (v >>> 8).setWidth 8, (v >>> 16).setWidth 8, (v >>> 24).setWidth 8]
      = Silmaril.X86.imm32Bytes v := by
  simp only [Silmaril.X86.imm32Bytes, BitVec.extractLsb', List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_toNat_eq
      simp

set_option maxRecDepth 100000 in
/-- **The image around the relocation.** The relocated image is `raw` up to
offset 180, then the canonical encoding of `kLea`, then `raw` from offset 187. -/
theorem image_split (L : Layout) :
    image L.textBase L.rodataBase
      = raw.take 180 ++ (Silmaril.X86.Ext.encode (kLea L) ++ raw.drop 187) := by
  have hraw : raw.take relocOffset = raw.take 180 ++ [0x48#8, 0x8d#8, 0x0d#8] := by
    decide
  rw [Silmaril.X86.Ext.encode_lea_rip,
    show (Silmaril.X86.Ext.Rex.byte ⟨true, Silmaril.X86.Ext.hiBit Reg.rcx, false, false⟩)
      = 0x48#8 from by decide,
    show (Silmaril.X86.Ext.ModRM.byte ⟨0#2, Reg.rcx.lo, 5#3⟩) = 0x0d#8 from by decide,
    ← imm32Bytes_eq]
  simp only [image, patch32, kLeaDisp, hraw, List.append_assoc, List.cons_append,
    List.nil_append]
  rfl

set_option maxRecDepth 100000 in
/-- The seven image bytes at offset 180 are the canonical encoding of the
`lea`. -/
theorem image_lea_slice (L : Layout) :
    ((image L.textBase L.rodataBase).drop 180).take 7
      = Silmaril.X86.Ext.encode
          (.lea .q .rcx (Silmaril.X86.Ext.Mem.ofRip (kLeaDisp L))) := by
  have htk : (raw.take 180).length = 180 := by
    rw [List.length_take, raw_length]; simp [size]
  rw [image_split, List.drop_left' htk, ← kLea_length L, List.take_left]

/-- **The relocated `lea` decodes, at every layout.** -/
theorem image_decode_lea (L : Layout) :
    decode (((image L.textBase L.rodataBase).drop 180).take 7)
      = some (.lea .q .rcx (Silmaril.X86.Ext.Mem.ofRip (kLeaDisp L)), 7) := by
  rw [image_lea_slice]
  have h := Silmaril.X86.Ext.decode_encode (kLea L)
  rwa [kLea_length] at h

/-! ## The whole image, at every layout -/

/-- The listing of the loaded image: the transcription, with the `lea` at
`0xd4` (function offset 180, entry 52 of 133) carrying the relocated
displacement. -/
def imageListing (L : Layout) : List Decoded :=
  Lifted.listing.take 52 ++ ⟨0xd4, kLea L, 7⟩ :: Lifted.listing.drop 53

set_option maxRecDepth 100000 in
/-- The 52 instructions before the relocated `lea` decode on their own. -/
theorem decode_pre : decodeFrom 52 0x20 (raw.take 180) = .ok (Lifted.listing.take 52) :=
  Silmaril.X86.Lift.ok_of_toOption (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The 80 instructions after it decode on their own. -/
theorem decode_post : decodeFrom 80 0xdb (raw.drop 187) = .ok (Lifted.listing.drop 53) :=
  Silmaril.X86.Lift.ok_of_toOption (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The loaded image decodes, at every layout, to `imageListing`.** The
relocation changes the `lea`'s displacement and no instruction boundary. -/
theorem image_decode (L : Layout) :
    (⟨0x20, image L.textBase L.rodataBase⟩ : Region).decode? 133 = some (imageListing L) := by
  have htk : (raw.take 180).length = 180 := by
    rw [List.length_take, raw_length]; simp [size]
  have hpost : decodeFrom 80 (0x20 + (raw.take 180).length
      + (Silmaril.X86.Ext.encode (kLea L)).length) (raw.drop 187) =
      .ok (Lifted.listing.drop 53) := by
    rw [htk, kLea_length]; exact decode_post
  have h := Silmaril.X86.Lift.decodeFrom_splice (kLea L) decode_pre hpost
  rw [htk, kLea_length] at h
  simp only [Region.decode?, Region.decode, image_split, h]
  rfl

/-- A decode fact about the loaded image, at every layout, from a lookup in
`imageListing`. -/
theorem decode_image {L : Layout} {o n : Nat} {i : Silmaril.X86.Ext.Instr}
    (h : at? (imageListing L) (o + 0x20) = some ⟨o + 0x20, i, n⟩) :
    decode (((image L.textBase L.rodataBase).drop o).take n) = some (i, n) := by
  have := Silmaril.X86.Lift.decode_of_at (image_decode L) h
  simpa using this

end Silmaril.Crypto.X86.Sha256O2
