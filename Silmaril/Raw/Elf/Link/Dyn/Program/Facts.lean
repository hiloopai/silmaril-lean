module

public import Silmaril.Elf.Link.Dyn.Program.Defs
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Basic

/-! # What the per-binary check gives

`Bin.facts`: `B.ok libc ld = true` as separate facts. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte)
open Silmaril.Elf.Link.Dyn

/-- **What `Bin.ok` gives.** -/
structure Bin.Facts (B : Bin) (libc ld : LibPin) : Prop where
  info : Elf.dynInfo.run (blobRead B.file) = some B.info
  refs : Hello.refsHold B.file B.info B.refs = true
  slotsK : Dyn.slotsWith (Dyn.resolveK [Hello.exeFacts B.refs, libc.facts, ld.facts]) false B.file B.info =
    some B.slots
  layout : B.layout.ok = true
  img : B.layout.imageOk B.file B.info B.tx B.ro B.rw B.slots B.lsmOff B.cxaOff = true
  extra : Crt.extraOk B.file B.info B.tx B.rw B.slots B.extraCode B.extraSlots = true
  mainL : Proc.listingOk B.layout.cMain B.mainL = true
  pltL : Proc.listingOk B.plt B.pltL = true
  codeIn : ∀ c ∈ B.extraCode, c.1 + c.2.length ≤ B.layout.size
  slotIn : ∀ s ∈ B.extraSlots, s.1 + 8 ≤ B.layout.size
  nodup : ([B.lsmOff, B.cxaOff] ++ B.imports.map (·.off)).Nodup
  offs : ∀ o ∈ [B.lsmOff, B.cxaOff] ++ B.imports.map (·.off), o < 2 ^ 32
  stubs : ∀ i ∈ B.imports, B.stubOk i = true
  pltIn : B.pltAt + B.plt.length ≤ B.layout.size
  strs : ∀ e ∈ B.strs, B.cstrAt e.1 = some e.2
  blks : ∀ k ∈ B.blks, k.ok B.layout.cMain = true
  tx : B.tx ∈ B.info.phs
  txk : B.tx.kind = 1
  txf : B.tx.flags = 5
  tx1 : B.tx.vaddr ≤ B.layout.main
  tx2 : B.layout.main + B.layout.cMain.length ≤ B.tx.vaddr + B.tx.memsz

theorem Bin.facts {B : Bin} {libc ld : LibPin} (h : B.ok libc ld = true) : B.Facts libc ld := by
  simp only [Bin.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi, hrefs⟩, hK⟩, hL⟩, himg⟩, hext⟩, hm⟩, hp⟩, hcs⟩, hss⟩, hnd⟩, hlt⟩, hst⟩, hpl⟩, hs⟩,
    hb⟩, htx⟩, htk⟩, htf⟩, ht1⟩, ht2⟩ := h
  exact ⟨hi, hrefs, hK, hL, himg, hext, hm, hp, hcs, hss, hnd, hlt, hst, hpl, hs, hb, by simpa using htx,
    htk, htf, ht1, ht2⟩

end Silmaril.Elf.Link.Dyn.Program
