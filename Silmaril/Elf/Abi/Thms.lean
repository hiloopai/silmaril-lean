module

public import Silmaril.Elf.Abi.Defs
import Silmaril.Proofs.Elf.Abi.Basic

/-! # ABI conformance of an ELF function: theorems

* `AbiConforms.placement`: a row names a file that admits a load base;
* `not_abiConforms_of_noPlacement`: **regression**: on a file that admits no load base (an
  `ET_EXEC` whose `PT_LOAD` has `p_filesz > p_memsz` or reaches past `2^47`, …) no function
  conforms, for any spec and any machine: the rebased-conformance conjunct cannot be vacuous;
* **relocations are checked at their real width** (`Untouched`: the ELF core's
  `Image.Untouched` and `File.relocWidth`, with `COPY` and `IRELATIVE` refused):
  - `not_untouched_tlsdesc`: a `TLSDESC` (16 bytes) at 12 bytes below the code touches its first
    4 bytes and is refused; the former 8-byte check accepted it (`misses8_tlsdesc`);
  - `not_untouched_copy`: a `COPY` relocation (it writes the symbol's `st_size`) is refused
    wherever it is;
  - `not_untouched_unknown`: so is a relocation of any type `File.relocWidth` does not know;
  - `not_untouched_irelative`: and any `IRELATIVE` (ld.so runs its IFUNC resolver);
  - `not_untouched_machine`: and every relocation of a file that is not x86-64;
* `Present.not_absent`: **`absent` cannot be faked**: a function some symbol table of the file
  defines (in any table and version) is not absent, so an `absent` exclusion of it is refused;
* `CodeOf.bytes_unique`, `not_codeOf_of_bytes`: **the bytes are the file's**: two codes of one
  binding at one address with bytes of one length have the same bytes, so a code whose bytes
  differ from the file's (one byte changed) is the function of no binding.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {F : Blob} {b : Binding} {c : Code} {frame : Nat} {S : CallSpec A.V p}

theorem AbiConforms.placement (h : AbiConforms A M mode hdr f p F b c frame S) :
    ∃ base, Placement F base :=
  h.2.2.1

theorem not_abiConforms_of_noPlacement (hno : ∀ base, ¬ Placement F base) :
    ¬ AbiConforms A M mode hdr f p F b c frame S :=
  fun h => let ⟨base, hb⟩ := h.placement; hno base hb

theorem not_untouched_tlsdesc {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = 36) (ho : r.offset + 12 = c.base.toNat)
    (hn : 0 < c.bytes.length) : ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.not_untouched_tlsdesc hA hr hk ho hn

/-- A check that took every relocation as 8 bytes would pass that `TLSDESC`. -/
theorem misses8_tlsdesc (o n : Nat) :
    Silmaril.Elf.Image.Misses o 8 (o + 12) n = true ∧ (0 < n → Silmaril.Elf.Image.Misses o 16 (o + 12) n = false) := by
  refine ⟨by simp [Silmaril.Elf.Image.Misses], fun hn => ?_⟩
  simp only [Silmaril.Elf.Image.Misses, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem not_untouched_copy {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = R_X86_64_COPY) : ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.not_untouched_kind hA hr (.inl hk)

theorem not_untouched_irelative {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = R_X86_64_IRELATIVE) : ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.not_untouched_kind hA hr (.inr hk)

theorem not_untouched_unknown {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : A.relocWidth r = none) : ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.not_untouched_of_width hA hr hk

theorem not_untouched_machine {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hm : A.header.machine ≠ Silmaril.Elf.Image.EM_X86_64_MACHINE) :
    ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.not_untouched_machine hA hr hm

/-- The core's widths the check uses: `TLSDESC` 16, `RELATIVE`/`GLOB_DAT`/`JUMP_SLOT` 8, `32` 4;
unknown numbers none. (`COPY` and `IRELATIVE` are refused by `Untouched` itself.) -/
theorem relocWidth_examples :
    Silmaril.Elf.Image.x86RelocWidth 8 = some 8 ∧ Silmaril.Elf.Image.x86RelocWidth 6 = some 8 ∧
    Silmaril.Elf.Image.x86RelocWidth 7 = some 8 ∧ Silmaril.Elf.Image.x86RelocWidth 36 = some 16 ∧
    Silmaril.Elf.Image.x86RelocWidth 10 = some 4 ∧ Silmaril.Elf.Image.x86RelocWidth 39 = none ∧
    Silmaril.Elf.Image.x86RelocWidth 1000 = none := by decide

/-- A file with no dynamic relocation touches nothing. -/
theorem untouched_of_norelocs {A : File} (hA : Parses F A) (h : A.relocs .dynamic = []) : Untouched F c :=
  Silmaril.Proofs.Elf.Abi.untouched_of_norelocs hA h

theorem Present.not_absent (h : Present F f) : ¬ Absent F f := by
  rintro ⟨B, hB, hn⟩
  obtain ⟨A, hA, hf⟩ := h
  cases (Option.some.inj (hA.symm.trans hB) : A = B)
  rw [Silmaril.Proofs.Elf.Abi.definesName_of_definesFn hf] at hn
  cases hn

theorem CodeOf.bytes_unique {c' : Code} {b' : Binding} {f' : String} (h : CodeOf F b f c)
    (h' : CodeOf F b' f' c') (hb : c.base = c'.base) (hl : c.bytes.length = c'.bytes.length) :
    c.bytes = c'.bytes :=
  Silmaril.Proofs.Elf.Abi.codeAt_unique h.2.1 (hb ▸ h'.2.1) hl

theorem not_codeOf_of_bytes {c' : Code} {b' : Binding} {f' : String} (h : CodeOf F b f c)
    (hb : c.base = c'.base) (hl : c.bytes.length = c'.bytes.length) (hne : c.bytes ≠ c'.bytes) :
    ¬ CodeOf F b' f' c' :=
  fun h' => hne (h.bytes_unique h' hb hl)

end Silmaril.Elf.Abi

end
