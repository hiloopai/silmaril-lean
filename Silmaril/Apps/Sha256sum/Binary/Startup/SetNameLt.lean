module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameCmp

/-! # `set_program_name` (`sha256sum-min`): the `"lt-"` loop VC

The loop at `0x4036ea` (cut `762`) compares `argv[0][i+1+k]` (the byte after the last `/`,
in bounds since `i + 1 + k ≤ n` and `argv[0][n] = 0`) with `"lt-"[k]` (`.rodata`,
`0x4060e4`): a mismatch goes to the join `0x403486` (cut `150`) with `common`, a match to
`k + 1`, a full match (`k = 2`) strips the prefix (`r8`) and goes to the join.

* `LtGoal`: the VC at the loop head, behind an irreducible name like `LibsGoal`;
* `vc_lt_k0`, `vc_lt_k1`, `vc_lt_k2` (VERIFIED): one iteration at byte `k`;
* `vc_lt` (VERIFIED): the loop-cut VC, by cases on `k` (the statement of `VcLt`).

The steps go through `cmp_go` (`SetNameCmp.lean`: `cmp r8, m8` with the load in map form);
`vc_lt_k2` keeps `rax` a variable `A` with `A = 2` (with the literal, the full match's
`cmp rax, 3` leaves a proof the kernel rejects with deep recursion).

Status: VERIFIED (no `sorry`, no new axiom).
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

/-- The VC at the `"lt-"` loop head (cut `762`), behind an irreducible name like `LibsGoal`. -/
@[irreducible] def LtGoal (c : Ctx) (s : XState) : Prop :=
  wpN Isa.sys8 Main.code postListing (slashCuts c) [(150, common c)] [] [] Main.base
    (some (ltMeasure s)) 20 762 s

/-- A nonzero byte at `j ≤ n` (with `argv[0][n] = 0`) lies before the NUL. -/
theorem succ_le_of_ne_zero {c : Ctx} {n j : Nat} (hn0 : c.arg[n]! = 0) (hj : j ≤ n)
    (hb : c.arg[j]! ≠ 0) : j + 1 ≤ n := by
  rcases Nat.lt_or_eq_of_le hj with h | h
  · omega
  · subst h; exact absurd hn0 hb

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** The `"lt-"` loop at byte 0 (`'l'`). -/
theorem vc_lt_k0 (c : Ctx) (hc : LaunchFacts c) :
    ∀ (s : XState) {n i : Nat}, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 762 →
      n < c.arg.length → c.arg[n]! = 0 → i + 1 ≤ n →
      s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i → (s.core.read .rax).toNat = 0 →
      s.core.read .rsp = c.sp0 - 240#64 → s.core.read .rdi = c.argv0 → s.core.read .r11 = c.sp0 →
      s.core.read .rsi = 1#64 → s.core.read .r14 = 1#64 →
      Memory.WritesWithin c.m0 s.memory (W1 c.sp0) →
      LtGoal c s := by
  intro s n i hlv hl hrip hn hn0 hin hrcx hraxN hsp hdi hr11 hrsi hr14 hww
  unfold LtGoal
  have hm : ltMeasure s = 3 - 0 := by simp only [ltMeasure, hraxN]
  rw [hm]
  have hrax : s.core.read .rax = 0#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hraxN]; rfl
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hnw := hc.argStr.noWrap
  have hRn : (c.argv0 + BitVec.ofNat 64 i).toNat = c.argv0.toNat + i := toNat_add_ofNat _ _ (by omega)
  generalize hR : c.argv0 + BitVec.ofNat 64 i = R at hrcx hRn
  have hL : loadN s.memory (R + 1#64) 1 = some (c.arg[i+1]!.setWidth 64) :=
    arg_byte hc hww (by omega) _ (by rw [toNat_add_ofNat R 1 (by omega), hRn]; omega)
  have hro : loadN s.memory 4219108#64 1 = some 108#64 := ro_byte hc hww 0xe4 _ (by decide) (by decide +kernel)
  cmp_go [postListing, slashCuts, hrip, hl, hrcx, hrax, hdi, hL, hro]
  all_goals first
  | common_close
  | (simp only [ltMeasure]; seg_read []; decide)
  | (rename_i hb _
     have hne : c.arg[i+1]! ≠ 0 := by intro h0; rw [h0] at hb; simp at hb
     refine ⟨n, i, 1, hn, hn0, by omega, succ_le_of_ne_zero hn0 hin hne, ?_, ?_, ?_⟩
     · subst hR; seg_read [hrcx]
     · seg_read []; decide
     · common_close)

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** The `"lt-"` loop at byte 1 (`'t'`). -/
theorem vc_lt_k1 (c : Ctx) (hc : LaunchFacts c) :
    ∀ (s : XState) {n i : Nat}, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 762 →
      n < c.arg.length → c.arg[n]! = 0 → i + 2 ≤ n →
      s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i → (s.core.read .rax).toNat = 1 →
      s.core.read .rsp = c.sp0 - 240#64 → s.core.read .rdi = c.argv0 → s.core.read .r11 = c.sp0 →
      s.core.read .rsi = 1#64 → s.core.read .r14 = 1#64 →
      Memory.WritesWithin c.m0 s.memory (W1 c.sp0) →
      LtGoal c s := by
  intro s n i hlv hl hrip hn hn0 hin hrcx hraxN hsp hdi hr11 hrsi hr14 hww
  unfold LtGoal
  have hm : ltMeasure s = 3 - 1 := by simp only [ltMeasure, hraxN]
  rw [hm]
  have hrax : s.core.read .rax = 1#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hraxN]; rfl
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hnw := hc.argStr.noWrap
  have hRn : (c.argv0 + BitVec.ofNat 64 i).toNat = c.argv0.toNat + i := toNat_add_ofNat _ _ (by omega)
  generalize hR : c.argv0 + BitVec.ofNat 64 i = R at hrcx hRn
  have hL : loadN s.memory (R + 2#64) 1 = some (c.arg[i+2]!.setWidth 64) :=
    arg_byte hc hww (by omega) _ (by rw [toNat_add_ofNat R 2 (by omega), hRn]; omega)
  have hro : loadN s.memory 4219109#64 1 = some 116#64 := ro_byte hc hww 0xe5 _ (by decide) (by decide +kernel)
  cmp_go [postListing, slashCuts, hrip, hl, hrcx, hrax, hdi, hL, hro]
  all_goals first
  | common_close
  | (simp only [ltMeasure]; seg_read []; decide)
  | (rename_i hb _
     have hne : c.arg[i+2]! ≠ 0 := by intro h0; rw [h0] at hb; simp at hb
     refine ⟨n, i, 2, hn, hn0, by omega, succ_le_of_ne_zero hn0 hin hne, ?_, ?_, ?_⟩
     · subst hR; seg_read [hrcx]
     · seg_read []; decide
     · common_close)

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** The `"lt-"` loop at byte 2 (`'-'`): a match strips the prefix. `rax` stays a
variable `A` (`A = 2`): with the literal, the `cmp rax, 3` of the full match leaves a proof the
kernel rejects with deep recursion. -/
theorem vc_lt_k2 (c : Ctx) (hc : LaunchFacts c) :
    ∀ (s : XState) {n i : Nat}, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 762 →
      n < c.arg.length → c.arg[n]! = 0 → i + 3 ≤ n →
      s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i → (s.core.read .rax).toNat = 2 →
      s.core.read .rsp = c.sp0 - 240#64 → s.core.read .rdi = c.argv0 → s.core.read .r11 = c.sp0 →
      s.core.read .rsi = 1#64 → s.core.read .r14 = 1#64 →
      Memory.WritesWithin c.m0 s.memory (W1 c.sp0) →
      LtGoal c s := by
  intro s n i hlv hl hrip hn hn0 hin hrcx hraxN hsp hdi hr11 hrsi hr14 hww
  unfold LtGoal
  have hm : ltMeasure s = 3 - 2 := by simp only [ltMeasure, hraxN]
  rw [hm]
  have hrax : s.core.read .rax = 2#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hraxN]; rfl
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hnw := hc.argStr.noWrap
  have hRn : (c.argv0 + BitVec.ofNat 64 i).toNat = c.argv0.toNat + i := toNat_add_ofNat _ _ (by omega)
  generalize hR : c.argv0 + BitVec.ofNat 64 i = R at hrcx hRn
  generalize hA : s.core.read .rax = A at hrax
  have hL : loadN s.memory (R + (A + 1#64)) 1 = some (c.arg[i+3]!.setWidth 64) := by
    rw [hrax, show (2#64 + 1#64 : Word) = BitVec.ofNat 64 3 from rfl]
    exact arg_byte hc hww (by omega) _ (by rw [toNat_add_ofNat R 3 (by omega), hRn]; omega)
  have hro : loadN s.memory (A + 4219108#64) 1 = some 45#64 := by
    rw [hrax, show (2#64 + 4219108#64 : Word) = BitVec.ofNat 64 (0x406000 + 0xe6) from rfl]
    exact ro_byte hc hww 0xe6 _ (by decide) (by decide +kernel)
  cmp_go [postListing, slashCuts, hrip, hl, hrcx, hA, hdi, hL, hro]
  all_goals first
  | common_close
  | (exfalso; rename_i hb; revert hb; rw [hrax]; decide)

/-- **VERIFIED. The `"lt-"` loop VC** (cut `762`): one iteration, a mismatch or a full match
to the join, a match to the next byte. -/
theorem vc_lt (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 762 → ltInv c s →
      LtGoal c s := by
  intro s hlv hl hrip ⟨n, i, k, hn, hn0, hk, hin, hrcx, hrax, hsp, hdi, hr11, hrsi, hr14, hww⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
  · exact vc_lt_k0 c hc s hlv hl hrip hn hn0 (by omega) hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_lt_k1 c hc s hlv hl hrip hn hn0 (by omega) hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww
  · exact vc_lt_k2 c hc s hlv hl hrip hn hn0 (by omega) hrcx (hrax.trans h) hsp hdi hr11 hrsi hr14 hww

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
