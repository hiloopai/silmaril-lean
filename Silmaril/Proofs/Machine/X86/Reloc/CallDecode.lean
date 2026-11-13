module

public import Silmaril.Machine.Link.Thms
public import Silmaril.Machine.X86.Reloc.Defs
public import Silmaril.X86.Ext.Semantics

/-! # A PC32/PLT32-patched `call rel32` decodes to a call of the symbol

The imported profile proves the byte arithmetic (`patch_spec`, `patch_decoded`).
This file connects it to the public `Silmaril.X86.Ext` decoder and semantics:

* `encoded_rel32`: the 4-byte field the linker writes is exactly the decoder's
  `imm32Bytes (BitVec.ofInt 32 v)`;
* `call_patch_decodes`: patching the field after an `E8` opcode makes the
  bytes from the opcode decode (`Ext.decode`) to `.call rel` of length 5;
* `call_patch_target`: the call's target `next + sext rel` is `S + A + 4`
  (mod 2^64), where `next = P + 4` is the address after the 5-byte call;
  `plt_call_target` specialises to gcc's addend `A = -4`, giving target `S`;
* `call_patch_exec`: `Ext.exec` of that call jumps to `S + A + 4`;
* `linkSection_call`/`link_call`: the same facts inside a successful
  `Relocation.link`, read from the linked section bytes, provided the opcode
  byte is covered by no relocation of that section.

Note: DESIGN.md WP-L1 says the target is `S + A`; the exact statement is
`S + A + 4`, which is `S` for the `A = -4` that compilers emit for
`call foo` (`R_X86_64_PLT32 foo-4`).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Reloc

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link Silmaril.X86.Linking.Relocation
open Silmaril.Machine.Link

theorem encode_call (rel : BitVec 32) :
    Silmaril.X86.Ext.encode (.call rel) = 0xE8#8 :: Silmaril.X86.imm32Bytes rel := rfl

theorem encodeLE_four (v : Nat) :
    encodeLE 4 v = Silmaril.X86.imm32Bytes (BitVec.ofNat 32 v) := by
  simp only [encodeLE, Silmaril.X86.imm32Bytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat] <;> omega

/-- Every 4-byte field is the decoder's little-endian `imm32` of `v mod 2^32`. -/
theorem encoded_rel32 {kind : Nat} (hk : kind ≠ 1) (v : Int) :
    (encoded kind v).toList = Silmaril.X86.imm32Bytes (BitVec.ofInt 32 v) := by
  simp only [encoded, width, hk, ite_false, List.toList_toArray]
  rw [encodeLE_four]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

theorem signExtend_ofInt (v : Int) (lo : -(2 ^ 31) ≤ v) (hi : v < 2 ^ 31) :
    (BitVec.ofInt 32 v).signExtend 64 = BitVec.ofInt 64 v := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

theorem splice_drop {α} (l q : List α) {o k : Nat} {x : α} (hx : l[o]? = some x)
    (hb : o + 1 + k ≤ l.length) :
    (l.take (o + 1) ++ q ++ l.drop (o + 1 + k)).drop o = x :: (q ++ l.drop (o + 1 + k)) := by
  have hlt : o < l.length := by omega
  rw [List.append_assoc, List.drop_append_of_le_length (by simp; omega), List.drop_take]
  have : (l.drop o).take (o + 1 - o) = [x] := by
    rw [show o + 1 - o = 1 by omega]
    rw [List.getElem?_eq_getElem hlt] at hx
    cases hx
    simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem hlt]
  rw [this]; rfl

/-- A patch starting one byte after an `E8` opcode leaves the opcode in front. -/
theorem applyPatch_drop {d d' : Bytes} {p : Patch} (h : applyPatch d p = some d')
    {o : Nat} (ho : p.offset = o + 1) (hop : d[o]? = some 0xE8#8) :
    d'.toList.drop o = 0xE8#8 :: (p.bytes.toList ++ d.toList.drop (p.offset + p.bytes.size)) := by
  unfold applyPatch at h
  by_cases hb : p.offset + p.bytes.size ≤ d.size
  · simp only [hb, guard_true] at h
    cases h
    rw [ho] at hb ⊢
    have hx : d.toList[o]? = some 0xE8#8 := by simpa using hop
    have := splice_drop d.toList p.bytes.toList (k := p.bytes.size) hx (by simpa using hb)
    simpa using this
  · simp [hb] at h

/-- A successful PC32/PLT32 patch satisfies the signed 32-bit range. -/
theorem pc_fits {r : ResolvedRelocation} {d : Bytes} {p : Patch}
    (hk : r.kind = 2 ∨ r.kind = 4) (hp : patch r d = .ok p) :
    -(2 ^ 31) ≤ value r ∧ value r < 2 ^ 31 := by
  have h := (patch_spec hp).2.1
  have h1 : r.kind ≠ 1 := by omega
  have h10 : r.kind ≠ 10 := by omega
  simpa [Fits, h1, h10] using h

/-- Decoder splice: the patched bytes, read from the `E8` opcode, are a canonical
`call rel32` whose displacement is the relocation value `S + A - P`. -/
theorem call_patch_decodes {r : ResolvedRelocation} {d d' : Bytes} {p : Patch}
    (hk : r.kind = 2 ∨ r.kind = 4) (hp : patch r d = .ok p) (ha : applyPatch d p = some d')
    {o : Nat} (ho : r.offset = o + 1) (hop : d[o]? = some 0xE8#8) :
    Silmaril.X86.Ext.decode (d'.toList.drop o) =
      some (.call (BitVec.ofInt 32 (value r)), 5) := by
  obtain ⟨-, -, hoff, hbytes, -, -⟩ := patch_spec hp
  rw [applyPatch_drop ha (hoff.trans ho) hop, hbytes, encoded_rel32 (by omega),
    ← List.cons_append, ← encode_call, Silmaril.X86.Ext.decode_encode_append]
  rfl

/-- The address after the call (`P + 4`) plus the sign-extended displacement is
`S + A + 4`, modulo 2^64. -/
theorem call_patch_target {r : ResolvedRelocation} {d : Bytes} {p : Patch}
    (hk : r.kind = 2 ∨ r.kind = 4) (hp : patch r d = .ok p) :
    BitVec.ofNat 64 (r.place + 4) + (BitVec.ofInt 32 (value r)).signExtend 64 =
      BitVec.ofInt 64 ((r.symbolValue : Int) + r.addend + 4) := by
  obtain ⟨lo, hi⟩ := pc_fits hk hp
  rw [signExtend_ofInt _ lo hi, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  have : value r = (r.symbolValue : Int) + r.addend - r.place := by
    simp [value]; omega
  push_cast; omega

/-- With the compiler's `A = -4`, the call goes to the symbol itself. -/
theorem plt_call_target {r : ResolvedRelocation} {d : Bytes} {p : Patch}
    (hk : r.kind = 2 ∨ r.kind = 4) (hp : patch r d = .ok p) (ha : r.addend = -4) :
    BitVec.ofNat 64 (r.place + 4) + (BitVec.ofInt 32 (value r)).signExtend 64 =
      BitVec.ofNat 64 r.symbolValue := by
  rw [call_patch_target hk hp, ha, ← BitVec.ofInt_natCast]
  congr 1; omega

/-- Executing the decoded call at address `P - 1` pushes `P + 4` and jumps to
`S + A + 4`. -/
theorem call_patch_exec {r : ResolvedRelocation} {d : Bytes} {p : Patch}
    (hk : r.kind = 2 ∨ r.kind = 4) (hp : patch r d = .ok p) (hplace : 1 ≤ r.place)
    (s : Silmaril.X86.State) (memory : Silmaril.Process.Memory)
    (hrip : s.rip = BitVec.ofNat 64 (r.place - 1))
    {t : Silmaril.X86.State} {m : Silmaril.Process.Memory}
    (hpush : Silmaril.X86.pushWord s memory (BitVec.ofNat 64 (r.place + 4)) = some (t, m)) :
    Silmaril.X86.Ext.exec (.call (BitVec.ofInt 32 (value r))) s memory =
      .ok { t with rip := BitVec.ofInt 64 ((r.symbolValue : Int) + r.addend + 4) } m := by
  have hnext : s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.call
      (BitVec.ofInt 32 (value r))).length = BitVec.ofNat 64 (r.place + 4) := by
    rw [hrip, show (Silmaril.X86.Ext.Instr.call (BitVec.ofInt 32 (value r))).length = 5 from rfl,
      ← BitVec.ofNat_add]
    congr 1; omega
  simp only [Silmaril.X86.Ext.exec, hnext, hpush, call_patch_target hk hp]

theorem patch_of_mapM {rels : List ResolvedRelocation} {data : Bytes} {r : ResolvedRelocation}
    {p : Patch}
    (h : (do
      let patch ← relocate rels r data
      guard (patch.offset = r.offset ∧ 0 < patch.bytes.size)
      pure patch : Option Patch) = some p) :
    patch r data = .ok p := by
  cases hr : relocate rels r data with
  | none => simp [hr] at h
  | some q =>
    simp only [hr] at h
    by_cases hg : q.offset = r.offset ∧ 0 < q.bytes.size
    · simp [hg] at h; subst h; exact relocate_success hr
    · simp [hg] at h

/-- Inside a successful section link: if byte `o` of the input section is `E8`,
no relocation of the section overwrites it, and a PC32/PLT32 relocation patches
`o + 1`, then the linked bytes from `o` decode to that call. -/
theorem linkSection_call {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {placement : Placement} {out : LinkedSection} {part : ObjectSection}
    {r : ResolvedRelocation} {o : Nat}
    (h : linkSection objects rels relocate placement = some out)
    (hpart : sectionAt objects placement.key = some part)
    (hr : r ∈ rels) (hkey : r.key = placement.key) (hk : r.kind = 2 ∨ r.kind = 4)
    (ho : r.offset = o + 1) (hop : part.data[o]? = some 0xE8#8)
    (hfree : ∀ r' ∈ rels, r'.key = placement.key →
      ¬ (r'.offset ≤ o ∧ o < r'.offset + width r'.kind)) :
    Silmaril.X86.Ext.decode (out.data.toList.drop o) =
      some (.call (BitVec.ofInt 32 (value r)), 5) := by
  obtain ⟨part', patches, hpart', hmap, hpw, hfold, -, -⟩ := linkSection_some h
  rw [hpart] at hpart'; cases hpart'
  have hrf : r ∈ rels.filter (fun r => r.key == placement.key) := by simp [hr, hkey]
  obtain ⟨p, hp, hpe⟩ := mapM_some_mem hmap r hrf
  have hpatch := patch_of_mapM hpe
  obtain ⟨-, -, hoff, hbytes, hsize, hbound⟩ := patch_spec hpatch
  have hw : width r.kind = 4 := by simp [width]; omega
  have hsize' : out.data.size = part.data.size := foldl_patches_size hfold
  have hrel : p.bytes.toList = Silmaril.X86.imm32Bytes (BitVec.ofInt 32 (value r)) := by
    rw [hbytes]; exact encoded_rel32 (by omega) _
  rw [drop_eq_of_getElem? (pre := Silmaril.X86.Ext.encode (.call (BitVec.ofInt 32 (value r))))
    (fun j hj => ?_), Silmaril.X86.Ext.decode_encode_append]
  · rfl
  · rw [encode_call] at hj ⊢
    simp only [List.length_cons, Silmaril.X86.length_imm32Bytes] at hj
    simp only [Array.getElem?_toList]
    rcases j with _ | j
    · rw [Nat.add_zero, foldl_patches_get hpw hfold o ?_]
      · rw [hop]; rfl
      · intro q hq hc
        obtain ⟨r', hr', hqe⟩ := mapM_some_mem' hmap q hq
        have hq' := patch_spec (patch_of_mapM hqe)
        simp only [List.mem_filter, beq_iff_eq] at hr'
        apply hfree r' hr'.1 hr'.2
        simp only [Covers] at hc
        rw [← hq'.2.2.1, ← hq'.2.2.2.2.1]; exact hc
    · have hc : Covers p (o + (j + 1)) := by
        simp only [Covers]; rw [hsize, hoff, hw]
        omega
      rw [foldl_patches_get_mem hpw hfold p hp _ hc, ← Array.getElem?_toList, hrel,
        hoff, ho, List.getElem?_cons_succ]
      congr 1; omega

/-- **Call decode in a linked image.** For a successful x86-64 static link, a
PC32/PLT32 relocation that patches the `rel32` of an `E8` in a placed section
yields, in the output section at the same offset, bytes that decode to a call
whose target (from the address after the instruction) is `S + A + 4`. -/
theorem link_call {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} {rels : List ResolvedRelocation} {placement : Placement}
    {part : ObjectSection} {r : ResolvedRelocation} {o : Nat}
    (h : Silmaril.X86.Linking.Relocation.link objects layout absolute = some out)
    (hrels : resolveRelocations objects layout absolute = some rels)
    (hplace : placement ∈ layout) (hpart : sectionAt objects placement.key = some part)
    (hr : r ∈ rels) (hkey : r.key = placement.key) (hk : r.kind = 2 ∨ r.kind = 4)
    (ho : r.offset = o + 1) (hop : part.data[o]? = some 0xE8#8)
    (hfree : ∀ r' ∈ rels, r'.key = placement.key →
      ¬ (r'.offset ≤ o ∧ o < r'.offset + width r'.kind)) :
    ∃ s ∈ out, s.key = placement.key ∧ s.address = placement.address ∧
      Silmaril.X86.Ext.decode (s.data.toList.drop o) =
        some (.call (BitVec.ofInt 32 (value r)), 5) ∧
      BitVec.ofNat 64 (s.address + o + 5) + (BitVec.ofInt 32 (value r)).signExtend 64 =
        BitVec.ofInt 64 ((r.symbolValue : Int) + r.addend + 4) := by
  unfold Silmaril.X86.Linking.Relocation.link at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨hnd, rels', hrels', hsec, -⟩ := link_some h
  rw [hrels] at hrels'; cases hrels'
  obtain ⟨s, hs, hls⟩ := mapM_some_mem hsec placement hplace
  obtain ⟨-, -, -, -, -, -, hsa, hsk⟩ := linkSection_some hls
  refine ⟨s, hs, hsk, hsa, linkSection_call hls hpart hr hkey hk ho hop hfree, ?_⟩
  obtain ⟨base, hbase, hplace'⟩ := resolveRelocations_mem hrels hr
  rw [hkey, addressAt_of_mem hplace hnd] at hbase
  cases hbase
  obtain ⟨part', patches, hpart', hmap, -, -, -, -⟩ := linkSection_some hls
  rw [hpart] at hpart'; cases hpart'
  have hrf : r ∈ rels.filter (fun r => r.key == placement.key) := by simp [hr, hkey]
  obtain ⟨p, -, hpe⟩ := mapM_some_mem hmap r hrf
  rw [← call_patch_target hk (patch_of_mapM hpe), hsa, hplace', ho]
  congr 2

/-- A successful link resolved its relocations. -/
theorem link_resolved {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link objects layout absolute = some out) :
    ∃ rels, resolveRelocations objects layout absolute = some rels := by
  unfold Silmaril.X86.Linking.Relocation.link at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨-, rels, hrels, -⟩ := link_some h
  exact ⟨rels, hrels⟩

end Silmaril.Machine.X86.Reloc
