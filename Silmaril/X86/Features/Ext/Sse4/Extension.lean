module

public import Silmaril.X86.Features.Ext.Sse4.Semantics
public import Silmaril.X86.Features.Ext.Sse2.Extension
public import Silmaril.X86.Features.Ext.SsePacked.Extension

/-!
# The SSE3/SSSE3/SSE4 lane as an extension

`sse4Ext` packages the codec of `Encoding.lean`, `Instr.requires` (SSE3,
SSSE3, SSE4.1 or SSE4.2 from the SDM page) and `exec`.

## Disjointness

* `decode_none_of_head`: the lane rejects any bytes that start with a
  mandatory prefix, a REX nibble, `0F` and an opcode that is neither an escape
  (`38`/`3A`) nor in its `0F`-map table, whatever follows.
* `sse2Ext_disjoint_sse4Ext` and `ssePacked_disjoint_sse4Ext` apply it to the
  heads of the two SSE/SSE2 lanes (`Sse2.ownedHead`, `SsePacked.opcTable`,
  checked by `decide`). `floatExt_disjoint_sse4Ext` is the recovered
  `float_decode_disjoint`.
* `ext_decode_encode` (recovered) shows that the integer decoder rejects the
  lane, so `step_of_ext` gives its machine step.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Byte Prefix OpMap)
open Silmaril.Process (Memory)

namespace Sse4

/-- Bytes with a `0F`-map head that the lane's table does not know are rejected. -/
theorem decode_none_of_head (pfx : Prefix) (rexn : BitVec 4) (opc : Byte) (tail : List Byte)
    (hesc : opc ≠ 0x38#8 ∧ opc ≠ 0x3A#8) (hk : ∀ w, lookup ⟨pfx, .m0F, opc, w⟩ = none) :
    decoder.decode (pfx.bytes ++ (X86.rexBytes rexn ++ (0x0F#8 :: opc :: tail))) = none := by
  have hh := pHead_bytes false pfx
    (if rexn = 0#4 then none else some (Ext.Rex.ofByte (X86.rexByte rexn))) .m0F opc
    (fun _ => hesc) tail
  rw [← float_rexBytes] at hh
  simp only [Ext.segBytes_false, OpMap.bytes, List.nil_append] at hh
  simp only [decode_eq, canonicalDecode, candidate]
  cases hp : parse (pfx.bytes ++ (X86.rexBytes rexn ++ (0x0F#8 :: opc :: tail))) with
  | ok r rest =>
    obtain ⟨h1, h2, h3⟩ := parse_head hh hp
    simp only [ofRaw, h1, h2, h3, hk, Option.map_none]
  | eof => rfl
  | bad => rfl

/-- No head of the SSE2 lane is in the table. -/
theorem lookup_sse2 : ∀ pfx ∈ [Prefix.none, .p66, .pF3], ∀ opc : Byte,
    Sse2.ownedHead pfx opc = true → ∀ w, lookup ⟨pfx, .m0F, opc, w⟩ = none := by
  decide +kernel

/-- No head of the SsePacked lane is an escape or in the table. -/
theorem lookup_ssePacked : ∀ p ∈ SsePacked.opcTable,
    (p.2 ≠ 0x38#8 ∧ p.2 ≠ 0x3A#8) ∧ ∀ w, lookup ⟨p.1, .m0F, p.2, w⟩ = none := by
  decide +kernel

theorem sse2_disjoint (bytes : List Byte) :
    Sse2.decode bytes = none ∨ decoder.decode bytes = none := by
  cases h : Sse2.decode bytes with
  | none => exact .inl rfl
  | some r =>
    right
    obtain ⟨i, n⟩ := r
    obtain ⟨-, -, hb⟩ := Sse2.decode_sound h
    have hh := Sse2.toRaw_ownedHead i
    have hsafe := Sse2.ownedHead_safe hh
    have hbytes : bytes = (Sse2.toRaw i).1.pfx.bytes ++ (X86.rexBytes (Sse2.toRaw i).1.rex ++
        (0x0F#8 :: (Sse2.toRaw i).1.opc :: (((Sse2.toRaw i).1.rm.bytes
          (X86.nibbleLo (Sse2.toRaw i).1.reg) ++ (Sse2.toRaw i).1.imm.toList) ++
          ((Sse2.toRaw i).2.toList ++ bytes.drop n)))) := by
      conv_lhs => rw [hb]
      simp [Sse2.encode, X86.Raw.bytes, Sse2.toRaw_map, OpMap.bytes]
    rw [hbytes]
    exact decode_none_of_head _ _ _ _ ⟨hsafe.1, hsafe.2.1⟩
      (lookup_sse2 _ (Sse2.ownedHead_pfx hh) _ hh)

theorem ssePacked_disjoint (bytes : List Byte) :
    SsePacked.decode bytes = none ∨ decoder.decode bytes = none := by
  cases h : SsePacked.decode bytes with
  | none => exact .inl rfl
  | some r =>
    right
    obtain ⟨j, n⟩ := r
    obtain ⟨-, -, hb⟩ := SsePacked.decode_sound h
    have hm := lookup_ssePacked _ (SsePacked.toRaw_mem_opcTable j)
    rw [hb, SsePacked.encode, SsePacked.PRaw.bytes]
    simp only [List.append_assoc, List.cons_append]
    exact decode_none_of_head _ _ _ _ hm.1 hm.2

end Sse4

/-- The SSE3/SSSE3/SSE4.1/SSE4.2 lane as an extension. -/
def sse4Ext : Extension where
  name := "SSE3/SSSE3/SSE4.1/SSE4.2 (legacy encoding)"
  Syntax := Sse4.Instr
  decoder := Sse4.decoder
  requires := Sse4.Instr.requires
  exec := Sse4.exec

theorem sse2Ext_disjoint_sse4Ext : Extension.Disjoint sse2Ext sse4Ext := Sse4.sse2_disjoint

theorem ssePacked_disjoint_sse4Ext : Extension.Disjoint SsePacked.ext sse4Ext :=
  Sse4.ssePacked_disjoint

theorem floatExt_disjoint_sse4Ext : Extension.Disjoint floatExt sse4Ext :=
  Sse4.float_decode_disjoint

theorem sse4Ext_disjoint_floatExt : Extension.Disjoint sse4Ext floatExt := fun bytes =>
  (Sse4.float_decode_disjoint bytes).symm

end Silmaril.X86.Features
