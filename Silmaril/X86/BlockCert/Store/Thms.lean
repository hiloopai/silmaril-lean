module

public import Silmaril.X86.BlockCert.Store.Defs
public import Silmaril.X86.BlockCert.Thms
import Silmaril.Proofs.X86.BlockCert.Store.Bridge

/-!
# Block certificates with a memory write: bridge and assembly

* `runLW_open`: **a listing checked by `listingAtW` at the program counter of a loaded image,
  whose run succeeds, is a run of `Open.step`** (one step per instruction). Unlike
  `BlockCert.runL_open` it says nothing about the memory: the block VC computes it.
* `FunCert.next_ofW`, `FunCert.vcW_of_blocks`, `FunCert.totalW`, `FunCert.contractW`: a
  function certificate with writing blocks whose VCs hold is a total System V `FnContract`
  on the open machine (strong induction on the block measure; arriving at a block carries the
  code image's loadedness, which the VC proves).
* `loaded_of_writesWithin`: writes outside the code image keep it loaded.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (LInstr)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

/-- **The bridge with a final write.** -/
theorem runLW_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAtW code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    Reaches Open.step m m' :=
  Silmaril.Proofs.X86.BlockCert.Store.runLW_open hok hl hrip h

/-- Writes outside the code image keep it loaded. -/
theorem loaded_of_writesWithin {mem mem' : Memory} {base : Word} {code : List Byte}
    {fp : Nat → Prop} (hl : Loaded mem base code) (hw : mem.WritesWithin mem' fp)
    (hout : ∀ i < code.length, ¬ fp (base.toNat + i)) : Loaded mem' base code := by
  unfold Loaded; rw [hw.fetchBytes hout]; exact hl

namespace FunCert

/-- Arriving at an annotated block with a smaller measure, the code still loaded. -/
theorem next_ofW {F : FunCert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (b : Blk) (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded m'.memory F.base F.code) (ha : F.ann b.off m0 m')
    (hμ : F.measure b.off m0 m' < μ) : F.NextW Q m0 μ m' :=
  .inr ⟨b, hb, hrip, hl, ha, hμ⟩

theorem vcW_of_blocks {F : FunCert} {Q : MState → MState → Prop}
    (h : ∀ b ∈ F.blocks, F.BlockVCW Q b) : F.VCW Q :=
  fun b hb => h b hb

/-- **Total correctness from a function certificate with writing blocks.** -/
theorem totalW {F : FunCert} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Silmaril.Proofs.X86.BlockCert.Store.totalW S hentry hc hvc hpre

/-- **The function contract** of a certificate with writing blocks. -/
def contractW (F : FunCert) (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    FnContract Open.isa :=
  ⟨S, totalW S hentry hc hvc hpre⟩

end FunCert

end Silmaril.X86.BlockCert
