module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameCmp

/-! # `set_program_name` (`sha256sum-min`): the `"/.libs/"` loop at byte 0

`vc_libs_k0` (VERIFIED): at the loop head `0x403476` with `rax = 0`, the byte `argv[0][i-6]`
is compared with `'/'` (`.rodata` `0x4060dc`): a mismatch goes to the join with `common`; a
match goes back to the loop head with `rax = 1` (`libsInv`, `k = 1`).

As in `SetNameLt.lean`: `cmp r8, m8` goes through `execNew_aluR_cmp_mem` (`SetNameCmp.lean`) (the load
in `Option.map` form), and `rax` stays a variable `A` with `A = 0`, so the impossible
`cmp rax, 7` branch closes by `decide` after `rw`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN Mem)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup
open Silmaril.Machine.Execution (Reaches)

set_option maxRecDepth 200000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** The `"/.libs/"` loop at byte 0 (`'/'`): a mismatch goes to the join with
`common`; a match goes back to the loop head with `rax = 1` (`libsInv`). -/
theorem vc_libs_k0 (c : Ctx) (hc : LaunchFacts c) :
    ∀ (s : XState) {n i : Nat}, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 134 →
      n < c.arg.length → c.arg[n]! = 0 → i < n → 6 ≤ i →
      s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i → (s.core.read .rax).toNat = 0 →
      s.core.read .rsp = c.sp0 - 240#64 → s.core.read .rdi = c.argv0 → s.core.read .r11 = c.sp0 →
      s.core.read .rsi = 1#64 → s.core.read .r14 = 1#64 →
      Memory.WritesWithin c.m0 s.memory (W1 c.sp0) →
      LibsGoal c s := by
  intro s n i hlv hl hrip hn hn0 hi h6 hrcx hraxN hsp hdi hr11 hrsi hr14 hww
  unfold LibsGoal
  have hm : libsMeasure s = 10 - 0 := by simp only [libsMeasure, hraxN]
  rw [hm]
  have hrax : s.core.read .rax = 0#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hraxN]; rfl
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hnw := hc.argStr.noWrap
  have hRn : (c.argv0 + BitVec.ofNat 64 i).toNat = c.argv0.toNat + i := toNat_add_ofNat _ _ (by omega)
  generalize hR : c.argv0 + BitVec.ofNat 64 i = R at hrcx hRn
  generalize hA : s.core.read .rax = A at hrax
  have hL : loadN s.memory (R + (A + 18446744073709551610#64)) 1 =
      some (c.arg[i-6+0]!.setWidth 64) := by
    rw [hrax, show (0#64 + 18446744073709551610#64 : Word) = 18446744073709551610#64 from rfl]
    exact arg_byte hc hww (by omega) _ (by rw [BitVec.toNat_add, hRn]; simp; omega)
  have hro : loadN s.memory (A + 4219100#64) 1 = some 47#64 := by
    rw [hrax, show (0#64 + 4219100#64 : Word) = BitVec.ofNat 64 (0x406000 + 0xdc) from rfl]
    exact ro_byte hc hww 0xdc _ (by decide) (by decide +kernel)
  cmp_go [postListing, slashCuts, hrip, hl, hrcx, hA, hdi, hL, hro]
  all_goals first
  | common_close
  | (exfalso; rename_i hb; revert hb; rw [hrax]; decide)
  | (subst hrax; simp only [libsMeasure]; seg_read []; decide)
  | (refine ⟨n, i, 1, hn, hn0, hi, h6, by omega, ?_, ?_, ?_⟩
     · subst hR; seg_read [hrcx]
     · subst hrax; seg_read []; decide
     · common_close)

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
