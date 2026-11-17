module

public import Silmaril.Elf.Abi.Asm.Defs
public import Silmaril.Elf.Asm.Thms
import Silmaril.Proofs.Elf.Abi.Asm.Basic

/-! # The typed adapter: theorems

PROVED (standard axioms), proof in `Silmaril.Proofs.Elf.Abi.Asm`:

* `codeOf_ofAsm`: an assembly function's grounded bytes (`BytesAt`, in the file's first read-only
  executable segment) and symbol (`SymbolOf`, an `STT_FUNC` at the binding's lookup index), with
  the binding's lookup finding it, give the conformance row's code binding
  `CodeOf F b f.name (Code.ofAsm f image)`. No other evidence of the function (decodings,
  contracts, listing, `abiRef`) enters a row through this adapter;
* `codeOf_ofAsmWith`: the same with read-only data, each range mapped read-only by the file
  (`MappedAt`).
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Elf Silmaril.Elf.Asm
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
    CodeOf F b f.name (Code.ofAsmWith f data image) :=
  Silmaril.Proofs.Elf.Abi.Asm.codeOf_ofAsmWith hv hb hseg hs hsym hnotIfunc hl hval hsize hif habs hd himg

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
  Silmaril.Proofs.Elf.Abi.Asm.codeOf_ofAsm hv hb hseg hs hsym hnotIfunc hl hval hsize hif habs himg

end Silmaril.Elf.Abi

end
