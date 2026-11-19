module

public import Silmaril.Elf.Abi.Asm.Defs
public import Silmaril.Elf.Asm.Thms

/-! # The typed adapter: proofs -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.Asm

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Asm
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)

theorem codeOf_ofAsmWith {F : Blob} {b : Binding} {f : AsmFunction} {data : List (Silmaril.X86.Word × List Silmaril.X86.Byte)}
    {image : List (Silmaril.X86.Word × Nat)}
    {d : Silmaril.Elf.Def} (hv : f.extent.vaddr < 2 ^ 64)
    (hb : BytesAt F f)
    (hseg : ∃ A i, Parses F A ∧ f.extent.segment = some i ∧
      A.phdrs.find? (codeSeg f.extent.vaddr f.bytes.length) = A.phdrs[i]?)
    (hs : SymbolOf F f) (hsym : f.symbol = some ⟨b.table, d.index⟩)
    (hnotIfunc : ∀ s, SymbolAt F b.table d.index s → s.kind ≠ 10)
    (hl : Lookup F (b.sel f.name) (some d)) (hval : d.value = f.extent.vaddr)
    (hsize : d.size = f.extent.size) (hif : d.ifunc = false) (habs : d.abs = false)
    (hd : ∀ x ∈ data, MappedAt F x.1.toNat x.2)
    (himg : ∃ A, Parses F A ∧ image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)) :
    CodeOf F b f.name (Code.ofAsmWith f data image) := by
  have hbase : (BitVec.ofNat 64 f.extent.vaddr).toNat = f.extent.vaddr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hv
  obtain ⟨r, s, hr, hsa, hname, -, -, hk⟩ := hs
  rw [hsym] at hr
  cases hr
  have hk2 : s.kind = 2 := hk.resolve_right (hnotIfunc s hsa)
  refine ⟨⟨d, hl, ?_, hsize, hif, habs, s, hsa, hname, hk2⟩, ?_, hd, himg⟩
  · show d.value = (BitVec.ofNat 64 f.extent.vaddr).toNat + 0
    rw [hbase, hval]; rfl
  · show CodeAt F (BitVec.ofNat 64 f.extent.vaddr).toNat f.bytes
    rw [hbase]
    exact bytesAt_codeAt hb hseg


theorem codeOf_ofAsm {F : Blob} {b : Binding} {f : AsmFunction} {image : List (Silmaril.X86.Word × Nat)}
    {d : Silmaril.Elf.Def} (hv : f.extent.vaddr < 2 ^ 64)
    (hb : BytesAt F f)
    (hseg : ∃ A i, Parses F A ∧ f.extent.segment = some i ∧
      A.phdrs.find? (codeSeg f.extent.vaddr f.bytes.length) = A.phdrs[i]?)
    (hs : SymbolOf F f) (hsym : f.symbol = some ⟨b.table, d.index⟩)
    (hnotIfunc : ∀ s, SymbolAt F b.table d.index s → s.kind ≠ 10)
    (hl : Lookup F (b.sel f.name) (some d)) (hval : d.value = f.extent.vaddr)
    (hsize : d.size = f.extent.size) (hif : d.ifunc = false) (habs : d.abs = false)
    (himg : ∃ A, Parses F A ∧ image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)) :
    CodeOf F b f.name (Code.ofAsm f image) :=
  codeOf_ofAsmWith hv hb hseg hs hsym hnotIfunc hl hval hsize hif habs (fun _ h => nomatch h) himg

end Silmaril.Proofs.Elf.Abi.Asm

end
