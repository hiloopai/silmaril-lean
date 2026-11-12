module

public import Silmaril.X86.BinInstitution.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
public import Silmaril.X86.Ladder.LibMini.Thms

/-!
# Worked example: an ELF-level sentence about a pinned executable

silmaril's ladder rung 02 pins the statically linked executable `mem-loops` (GCC 13.3, GNU ld
2.42, `-O2`, 9456 bytes, SHA-256 `3daa8710…b023`) byte-exactly as the `Blob`
`Pinned.MemLoops.exe`, and proves that the LPS loader puts libmini's `strlen` (35 bytes) at
`0x401400` in an `rx` segment (`Pinned.memLoops_strlen`, by `decide +kernel`), and that
`strlen` meets its contract on `Open.isa` at every address (`LibMini.strlen_total`).

Here they are one sentence of the `Ext8` signature `sOpen`:

* `sentence = elf ELoader.x86 MemLoops.exe place listing contract`: *under the x86-64 LPS
  loader, `mem-loops` places `strlen`'s code at `0x401400`, and the function there returns the
  length of the C string at `rdi`, writing nothing*;
* `places`: the loader fact (from `Pinned.memLoops_strlen`), so the sentence is about the
  real file; `wf`: the linear-sweep listing is what `Open.decode` reads (`decide +kernel`);
* `sat_open`: **the sentence holds in the model `Open`**; `sat_open9`: its translation along
  `Ext8 ⊆ Ext9` holds in the model `Open9` (`Open9` extends `Open`: `Spec.Total.lift`).

**Assumed (trusted):** the LPS loader (`ELFImage.parse`, `Records.image`) as the meaning of
"loads", that a process of `mem-loops` starts with the loader's image in memory (the sentence
does not model process creation), the `Blob` transcription of the file (`pin.sh --check`).
**Not shown:** a concrete entry state at `0x401400` meeting the contract (silmaril's
`strlen_nonvacuous` places the code at `0x9000`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BinInstitution.Strlen

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.RelIsa (Views)
open Silmaril.X86.FnContract (Spec)
open Silmaril.Project.Shapes (Placement)
open Silmaril.X86.Ladder.LibMini (strlenCode strlen_total)
open Silmaril.X86.Ladder.Pinned (MemLoops.exe)
open Silmaril.X86.Stencils.ByteLoop (CStr arg0 scanContract)
open Silmaril.X86.BinInstitution

/-- `strlen` in `mem-loops`: its 35 bytes at `0x401400`, entered at offset `0`. -/
def place : Placement := ⟨0x401400, strlenCode, 0⟩

/-- Its disassembly in the `Ext8` vocabulary: the linear sweep of `Open.decode`. -/
def listing : Listing Silmaril.X86.Ext8.Instr := Listing.linear Silmaril.X86.Open.decode strlenCode

/-- The contract: `rdi` points to a C string; `rax` is its length; nothing is written. -/
def contract : Spec MState where
  entry m := ∃ k, CStr m.memory (arg0 m) k
  footprint _ _ := False
  post := (scanContract strlenCode 0x401400).post

/-- **The ELF-level sentence.** -/
def sentence : Sen Silmaril.X86.Ext8.Instr MState :=
  .elf ELoader.x86 MemLoops.exe place listing contract

/-- **The loader places `strlen` at `0x401400`** (silmaril's pinned binary tie). -/
theorem places : Places ELoader.x86 MemLoops.exe place :=
  (places_x86_iff _ _).2 Silmaril.X86.Ladder.Pinned.memLoops_strlen

/-- The sweep reads the whole function. -/
theorem listing_length : listing.length = 12 := by decide +kernel

/-- **The sentence is well formed in `Ext8`.** -/
theorem wf : sentence.WF (σ := MState) sOpen.sig := by
  rintro _ _ ⟨⟩
  show ∀ it ∈ listing, it.off + it.len ≤ strlenCode.length ∧
    Silmaril.X86.Open.decode ((strlenCode.drop it.off).take it.len) =
      some (it.form, ((strlenCode.drop it.off).take it.len).length)
  decide +kernel

/-- The placed contract is `scanContract`'s at `0x401400`, so it is total on `Open`. -/
theorem total_open : (Spec.at Views.mstate place contract).Total Silmaril.X86.Open.isa := by
  intro s hl ha he
  have hrip : s.core.rip = 0x401400 := he.2.1.trans (by decide)
  obtain ⟨t, hr, h⟩ := strlen_total 0x401400 s hl ha ⟨hrip, he.1, he.2.2⟩
  exact ⟨t, hr, ⟨h.silent, h.abi, h.frame, h.post⟩⟩

/-- **The ELF-level sentence holds in the model `Open`.** -/
theorem sat_open : Sat Views.mstate openModel.1 sentence :=
  ⟨places, mustTotal_ofIsa_of_total total_open⟩

/-- The sentence translated along `Ext8 ⊆ Ext9`. -/
def sentence₉ : Sen Silmaril.X86.Ext9.Instr MState := sentence.map openOpen9.ρ

/-- **The translation holds in the model `Open9`** (by the satisfaction condition, on the reduct
of `Open9` to `Ext8`). -/
theorem sat_open9 : Sat Views.mstate open9Model.1 sentence₉ :=
  (satisfaction openOpen9 open9Model sentence).2
    ⟨places, mustTotal_ofIsa_of_total (total_open.lift_same Silmaril.X86.Open9.extendsOpen rfl)⟩

/-- The translation is well formed in `Ext9`. -/
theorem wf₉ : sentence₉.WF sOpen9.sig := wf_map openOpen9 wf

end Silmaril.Proofs.X86.BinInstitution.Strlen
