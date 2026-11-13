module

public import Silmaril.X86.Ladder.LeafArith.Defs
import Silmaril.X86.BlockCert.Thms
public import Silmaril.X86.Open.Thms
/-!
# `bswap32_manual` (gcc -O2): one Bir block

`mov %edi,%eax; bswap %eax; ret`. The block VC is closed by `bir_simp`/`bir_close`; the only
mathematics is `byteSwap32_eq`: x86 `bswap` is the C shift-and-mask expression, bit by bit.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (Block)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Ladder.LeafArith

set_option linter.unusedSimpArgs false

theorem byteSwap32_bit (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).getLsbD i =
      (bswap32Spec x).getLsbD i := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb']
  unfold bswap32Spec
  iterate 32 (rcases i with _ | i; · simp)
  omega

/-- x86 `bswap` at 32 bits is `bswap32_manual`. -/
theorem byteSwap32_eq (x : BitVec 32) : Silmaril.X86.Ext.byteSwap32 x = bswap32Spec x :=
  BitVec.eq_of_getLsbD_eq fun i hi => byteSwap32_bit x i hi

theorem bswap_checked : bswapCert.checked = true := by decide +kernel

theorem bswap_vc : bswapCert.VC fun m0 t => bswapSpec.Result Open.isa m0 t := by
  intro b hb m0 m ⟨hm, hab⟩ hrip hl
  simp only [bswapCert, List.mem_singleton] at hb
  subst hb hm
  rw [runL_eq_runB Bir.bswap32_manual.lifts_401420]
  bir_simp [Bir.bswap32_manual.I_401420, pop_ret hab]
  refine .inl (result_leaf ?_ ?_ ?_ rfl ?_) <;>
    bir_close [bswapSpec, leafSpec, r32, Silmaril.X86.Ext.byteSwap, byteSwap32_eq]

theorem bswap_total : bswapSpec.Total Open.isa :=
  FunCert.total bswapSpec (entry := ⟨0xb0, Bir.bswap32_manual.L_401420⟩) (by simp [bswapCert])
    bswap_checked bswap_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

end Silmaril.Proofs.X86.Ladder.LeafArith
