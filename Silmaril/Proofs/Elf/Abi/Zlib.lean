module

public import Silmaril.Machine.Abi.Conformance.Zlib.Defs
public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # zlib-checksums: the file facts of the conformance rows

Each one kernel read on the file's kernel bytes, or a computation on the parse it gives. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.Zlib

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.ZlibChecksums
open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib

abbrev A0 : File := L.assemble bodies ld

def funcSymB (i : Nat) (f : String) : Bool :=
  match (A0.symbols .symtab)[i]? with
  | some s => s.name == nameOf f && s.kind == 2
  | none => false

theorem funcSym {i : Nat} {f : String} (h : funcSymB i f = true) :
    ∃ s, SymbolAt F .symtab i s ∧ s.name = nameOf f ∧ s.kind = 2 := by
  unfold funcSymB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, ⟨_, parses, hs⟩, h.1, h.2⟩
  · exact absurd h (by simp)

theorem crcTable_mapped : MappedAt F 0x4021e0 Silmaril.X86.Ladder.ZlibChecksums.crcTableBytes :=
  ⟨_, parses, ph2, by decide +kernel, sub_kbytes K.wf_true K.toByteArray_eq _ _ _ (by decide +kernel)⟩

theorem image_eq : ∃ A, Parses F A ∧
    image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) :=
  ⟨_, parses, by decide +kernel⟩

theorem codeOf (f : String) (c : Code) (i : Nat)
    (hl : A0.select (Binding.symtab.sel f) = some (some ⟨i, c.base.toNat + c.off, c.len, false, false⟩))
    (hs : funcSymB i f = true) (hc : CodeAt F c.base.toNat c.bytes)
    (hd : ∀ d ∈ c.data, MappedAt F d.1.toNat d.2) (hi : c.image = image) :
    CodeOf F .symtab f c :=
  ⟨⟨_, ⟨_, parses, hl⟩, rfl, rfl, rfl, rfl, funcSym hs⟩, hc, hd, hi ▸ image_eq⟩

theorem crcData_mapped : ∀ d ∈ crcData, MappedAt F d.1.toNat d.2 := by
  intro d hd
  simp only [crcData, List.mem_singleton] at hd
  subst hd
  exact crcTable_mapped

theorem crc32z_code : CodeOf F .symtab "crc32_z" crc32zCode :=
  codeOf _ _ 14 (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel))
    crcData_mapped rfl

theorem crc32_code : CodeOf F .symtab "crc32" crc32Code :=
  codeOf _ _ 15 (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel))
    crcData_mapped rfl

theorem adler32z_code : CodeOf F .symtab "adler32_z" adler32zCode :=
  codeOf _ _ 25 (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel))
    (fun _ h => nomatch h) rfl

theorem adler32_code : CodeOf F .symtab "adler32" adler32Code :=
  codeOf _ _ 13 (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel))
    (fun _ h => nomatch h) rfl

theorem relocs_empty : A0.relocs .dynamic = [] := by decide +kernel

theorem untouched (c : Code) : Untouched F c :=
  ⟨_, parses, by decide +kernel, by rw [relocs_empty]; simp⟩

/-- `zlib-checksums` is `ET_EXEC`: it admits base `0` and no other. -/
theorem placement_zero_ok : Placement F 0 :=
  ⟨_, parses, .inl ⟨by decide +kernel, rfl⟩, fun ph h => by revert ph; decide +kernel⟩

theorem placement_zero {b : Nat} (h : Placement F b) : b = 0 := by
  obtain ⟨A, hA, hk, -⟩ := h
  have : A = A0 := Option.some.inj (hA.symm.trans parses)
  subst this
  rcases hk with ⟨-, h0⟩ | ⟨ht, -⟩
  · exact h0
  · exact absurd ht (by decide +kernel)

end Silmaril.Proofs.Elf.Abi.Zlib

end
