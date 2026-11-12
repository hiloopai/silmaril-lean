module

public import Silmaril.X86.BinInstitution.Thms
public import Silmaril.X86.BlockCert9.Examples

/-!
# Worked example: `ilog2_u32` as a sentence of the ISA institution

silmaril's ladder example `Silmaril.X86.BlockCert9.Examples` proves the System V contract of
the 22 bytes gcc 13.3 `-O2` emits for

```c
int ilog2_u32(uint32_t x) { int r = -1; while (x) { x >>= 1; r++; } return r; }
```

on `Open9.isa` (`ilog2_total`). Here the same function is a **sentence about a binary** of
the `Ext9` signature `sOpen9`:

* `place`: the code `ilogCode` at `0x401430`, the function at offset `0`;
* `listing`: its disassembly as `Ext9` forms, computed with `Open9.decode` at the instruction
  offsets (the `nopl` padding included); `wf`: the sentence is well formed (`decide`);
* `contract`: no extra precondition, nothing written, `rax = ilog2_u32(edi)`;
* `sat_open9`: **the sentence holds in the model `Open9`** (from `ilog2_total` through
  `mustTotal_ofIsa_of_total`);
* `sentence₉`: its translation along the inclusion `Ext9 ⊆ Str9` (every form wrapped in
  `.ext9`); `wf₉`: well formed over `Str9`; `sat_str9`: it holds in the model `Str9`, by the
  satisfaction condition from the reduct of `Str9` to `Ext9` (`Spec.Total.toStr9`).

What is *not* proved: that the sentence holds on the loose top of `sOpen9`, and so in every
model of `Ext9`; that needs the run on the top, not on one machine. It is `Task.ilogTop`, and
`sat_all_of_top` is the conditional result.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BinInstitution.Ilog2

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.RelIsa (Views)
open Silmaril.X86.FnContract (Spec)
open Silmaril.Project.Shapes (Placement)
open Silmaril.X86.BlockCert9.Examples (ilogBase ilogCode ilog2Spec r32 ilogSpec ilog2_total)
open Silmaril.X86.BinInstitution

/-- The function: `ilogCode` at `0x401430`, entered at offset `0`. -/
def place : Placement := ⟨ilogBase, ilogCode, 0⟩

/-- Its disassembly in the `Ext9` vocabulary: `test`, `je`, `bsr`, `ret`, `nopl`, `mov`,
`ret`. -/
def listing : Listing Silmaril.X86.Ext9.Instr :=
  Listing.ofFn Silmaril.X86.Open9.decode ilogCode [0x0, 0x2, 0x4, 0x7, 0x8, 0x10, 0x15]

/-- The contract: a leaf function, no memory written, `rax = ilog2_u32(edi)`. -/
def contract : Spec MState where
  entry _ := True
  footprint _ _ := False
  post m t := t.core.read .rax = (ilog2Spec (r32 .rdi m)).setWidth 64

/-- **The sentence**: the function placed by `place`, listed as `listing`, meets
`contract`. -/
def sentence : Sen Silmaril.X86.Ext9.Instr MState := .fn place listing contract

/-- All seven offsets are read by the decoder. -/
theorem listing_length : listing.length = 7 := by decide +kernel

/-- **The sentence is well formed in `Ext9`**: `Open9.decode` reads each listed slice as its
form. -/
theorem wf : sentence.WF (σ := MState) sOpen9.sig := by
  rintro _ _ ⟨⟩
  show ∀ it ∈ listing, it.off + it.len ≤ ilogCode.length ∧
    Silmaril.X86.Open9.decode ((ilogCode.drop it.off).take it.len) =
      some (it.form, ((ilogCode.drop it.off).take it.len).length)
  decide +kernel

/-- The placed contract is `ilogSpec`'s, so it is totally correct on `Open9`. -/
theorem total_open9 : (Spec.at Views.mstate place contract).Total Silmaril.X86.Open9.isa := by
  intro s hl ha he
  obtain ⟨t, hr, h⟩ := ilog2_total s hl ha ⟨he.1, he.2.1⟩
  exact ⟨t, hr, ⟨h.silent, h.abi, h.frame, h.post⟩⟩

/-- **The sentence holds in the model `Open9`.** -/
theorem sat_open9 : Sat Views.mstate open9Model.1 sentence :=
  mustTotal_ofIsa_of_total total_open9

/-- The sentence translated along `Ext9 ⊆ Str9`. -/
def sentence₉ : Sen Silmaril.X86.Str9.Instr MState := sentence.map open9Str9.ρ

/-- The translation wraps each listed form in `.ext9` and keeps the rest. -/
theorem sentence₉_eq :
    sentence₉ = .fn place (listing.map Silmaril.X86.Str9.Instr.ext9) contract := rfl

/-- The translation is well formed in `Str9`. -/
theorem wf₉ : sentence₉.WF sStr9.sig := wf_map open9Str9 wf

/-- **The translated sentence holds in the model `Str9`**: by the satisfaction condition, it
is the sentence on the reduct of `Str9` to `Ext9`, where `Spec.Total.toStr9` applies. -/
theorem sat_str9 : Sat Views.mstate str9Model.1 sentence₉ :=
  (satisfaction open9Str9 str9Model sentence).2
    (mustTotal_ofIsa_of_total total_open9.toStr9)

/-- **Open**: the sentence holds on the loose top of `Ext9` (every model of `sOpen9`). -/
def Task.ilogTop : Prop := Sat Views.mstate (sOpen9.sig.top Views.mstate) sentence

/-- Given `Task.ilogTop`, the sentence holds in every model of `Ext9`. -/
theorem sat_all_of_top (h : Task.ilogTop) (M : Model Views.mstate sOpen9) :
    Sat Views.mstate M.1 sentence :=
  sat_of_top h M

end Silmaril.Proofs.X86.BinInstitution.Ilog2
