module

public import Silmaril.Elf.Abi.ZlibLibz.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # libz.so.1.3: the file facts of the conformance rows

Each one kernel read on the file's kernel bytes, or a computation on the parse it gives. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibLibz

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.ZlibLibz
open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.ZlibLibz
open Silmaril.Elf.Abi.ZlibLibz (zlib129)

abbrev A0 : File := L.assemble bodies ld

/-- Entry `i` of `.dynsym` is an `STT_FUNC` named `f`. -/
def funcSymB (i : Nat) (f : String) : Bool :=
  match (A0.symbols .dynsym)[i]? with
  | some s => s.name == nameOf f && s.kind == 2
  | none => false

theorem funcSym {i : Nat} {f : String} (h : funcSymB i f = true) :
    ∃ s, SymbolAt F .dynsym i s ∧ s.name = nameOf f ∧ s.kind = 2 := by
  unfold funcSymB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, ⟨_, parses, hs⟩, h.1, h.2⟩
  · exact absurd h (by simp)

/-- The read-only `PT_LOAD` at `0x14000` holds `rodata`. -/
theorem rodata_mapped : MappedAt F 0x14000 rodata :=
  ⟨_, parses, ph2, by decide +kernel, sub_kbytes K.wf_true K.toByteArray_eq _ _ _ (by decide +kernel)⟩

theorem crcData_mapped : ∀ d ∈ crcData, MappedAt F d.1.toNat d.2 := by
  intro d hd
  simp only [crcData, List.mem_singleton] at hd
  subst hd
  exact rodata_mapped

theorem image_eq : ∃ A, Parses F A ∧
    image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) :=
  ⟨_, parses, by decide +kernel⟩

theorem codeOf (b : Binding) (f : String) (c : Code) (i : Nat)
    (hb : b.table = .dynsym)
    (hl : A0.select (b.sel f) = some (some ⟨i, c.base.toNat + c.off, c.len, false, false⟩))
    (hs : funcSymB i f = true) (hc : CodeAt F c.base.toNat c.bytes)
    (hd : ∀ d ∈ c.data, MappedAt F d.1.toNat d.2) (hi : c.image = image) :
    CodeOf F b f c :=
  ⟨⟨_, ⟨_, parses, hl⟩, rfl, rfl, rfl, rfl, hb ▸ funcSym hs⟩, hc, hd, hi ▸ image_eq⟩

theorem crc32z_code : CodeOf F (.dynsym (some zlib129)) "crc32_z" crc32zCode :=
  codeOf _ _ _ 26 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped rfl

theorem crc32_code : CodeOf F (.dynsym none) "crc32" crc32Code :=
  codeOf _ _ _ 52 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped rfl

theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode :=
  codeOf _ _ _ 38 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) rfl

theorem adler32_code : CodeOf F (.dynsym none) "adler32" adler32Code :=
  codeOf _ _ _ 46 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) rfl

/-- A selector the parse answers `none` for has no `Lookup`. -/
theorem no_lookup_unversioned {f : String} (h : A0.select ((Binding.dynsym none).sel f) = none) (d : Option Def) :
    ¬ Lookup F ((Binding.dynsym none).sel f) d := by
  rintro ⟨A, hA, hs⟩
  have : A = A0 := Option.some.inj (hA.symm.trans parses)
  subst this
  rw [h] at hs
  cases hs

/-- Without a version, ld.so's lookup of a `_z` function has no answer: its definition has a
non-base version (index 14), which `check_match` does not accept for an unversioned reference
(glibc's `num_versions` fallback, `File.checkMatch`). -/
theorem crc32z_unversioned (d : Option Def) : ¬ Lookup F ((Binding.dynsym none).sel "crc32_z") d :=
  no_lookup_unversioned (by decide +kernel) d

theorem adler32z_unversioned (d : Option Def) : ¬ Lookup F ((Binding.dynsym none).sel "adler32_z") d :=
  no_lookup_unversioned (by decide +kernel) d

/-- The file is x86-64, and its dynamic relocations are `GLOB_DAT` (6), `JUMP_SLOT` (7) and
`RELATIVE` (8) only: 8 bytes each (`File.relocWidth`). -/
theorem machine_x86_64 : A0.header.machine = EM_X86_64 := by decide +kernel

theorem reloc_kinds : (A0.relocs .dynamic).all (fun r => [6, 7, 8].contains r.kind) = true := by
  decide +kernel

/-- Every dynamic relocation is 8 bytes (`File.relocWidth`) and neither `COPY` nor `IRELATIVE`. -/
theorem reloc_width : (A0.relocs .dynamic).all (fun r => A0.relocWidth r == some 8 &&
    r.kind != R_X86_64_COPY && r.kind != R_X86_64_IRELATIVE) = true := by
  decide +kernel

/-- No dynamic relocation (`.rela.dyn`, `.rela.plt`), 8 bytes each, writes `[v, v + n)`. -/
def missesAllB (v n : Nat) : Bool :=
  (A0.relocs .dynamic).all fun r => Silmaril.Elf.Image.Misses r.offset 8 v n

theorem untouched_of {c : Code} (hc : missesAllB c.base.toNat c.bytes.length = true)
    (hd : ∀ d ∈ c.data, missesAllB d.1.toNat d.2.length = true) : Untouched F c := by
  have hw' := fun r hr => List.all_eq_true.mp reloc_width r hr
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hw'
  exact ⟨_, parses, fun r hr => ⟨8, (hw' r hr).1.1, List.all_eq_true.mp hc r hr⟩,
    fun d hdm r hr => ⟨8, (hw' r hr).1.1, List.all_eq_true.mp (hd d hdm) r hr⟩,
    fun r hr => ⟨(hw' r hr).1.2, (hw' r hr).2⟩⟩

theorem rodata_untouched : ∀ d ∈ crcData, missesAllB d.1.toNat d.2.length = true := by
  intro d hd
  simp only [crcData, List.mem_singleton] at hd
  subst hd
  decide +kernel

theorem crc32z_untouched : Untouched F crc32zCode :=
  untouched_of (by decide +kernel) rodata_untouched
theorem crc32_untouched : Untouched F crc32Code :=
  untouched_of (by decide +kernel) rodata_untouched
theorem adler32z_untouched : Untouched F adler32zCode :=
  untouched_of (by decide +kernel) (fun _ h => nomatch h)
theorem adler32_untouched : Untouched F adler32Code :=
  untouched_of (by decide +kernel) (fun _ h => nomatch h)

/-- `libz.so.1.3` is `ET_DYN` and admits the load base `0`. -/
theorem placement_zero_ok : Placement F 0 :=
  ⟨_, parses, .inr ⟨by decide +kernel, rfl⟩, fun ph h => by revert ph; decide +kernel⟩

end Silmaril.Proofs.Elf.Abi.ZlibLibz

end
