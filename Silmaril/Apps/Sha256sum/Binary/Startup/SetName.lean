module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts

/-! # `set_program_name` in `cmain` (`sha256sum-min`), by the segment VC generator

`cmain` (`0x4033f0`) saves its callee-saved registers, reads `argc` and `argv[0]` and scans
`argv[0]` for its last `/` (the loop at `0x403430`, measure the bytes left), then compares the
seven bytes before the base name with `"/.libs/"` and the base name with `"lt-"`, stores
`program_name` and `getopt_argv0`, and reaches `AtOptParse` (`0x4034a6`).

* `vc_entry` (VERIFIED): from the entry to the scan loop, or (empty `argv[0]`) to `0x4034a6`;
* `vc_scan` (VERIFIED): one iteration of the scan, back to the loop or to its exit `0x403444`.

The loads of the string go through `cstring_load` (the footprint `W1` misses the strings,
which lie above the vectors).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN Mem)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup

set_option maxRecDepth 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

def common (c : Ctx) (s : XState) : Prop :=
  s.core.read .rsp = c.sp0 - 240#64 ∧ s.core.read .rdi = c.argv0 ∧ s.core.read .r11 = c.sp0 ∧
  s.core.read .rsi = 1#64 ∧ s.core.read .r14 = 1#64 ∧ Memory.WritesWithin c.m0 s.memory (W1 c.sp0)

def scanInv (c : Ctx) (s : XState) : Prop :=
  ∃ j, j + 1 < c.arg.length ∧ (∀ q, q ≤ j → c.arg[q]! ≠ 0) ∧
    s.core.read .rax = c.argv0 + BitVec.ofNat 64 j ∧ s.core.read .rdx = (c.arg[j]!).setWidth 64 ∧
    (s.core.read .rcx = 0#64 ∨ ∃ i, i < j ∧ s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i ∧ c.arg[i]! = 0x2f#8) ∧
    common c s

def scanMeasure (c : Ctx) (s : XState) : Nat := c.arg.length - (s.core.read .rax - c.argv0).toNat

def postB (c : Ctx) (t : XState) : Prop :=
  t.core.read .rsp = c.sp0 - 240#64 ∧ t.core.read .rsi = 1#64 ∧ t.core.read .r11 = c.sp0 ∧
  t.core.read .r12 = 0#64 ∧ t.core.read .r14 = 1#64 ∧ t.core.read .r15 = c.sp0 + 8#64 ∧
  t.core.read .rbx = 16#64 ∧ t.core.read .rdi = c.argv0 ∧ Memory.WritesWithin c.m0 t.memory (W1 c.sp0)

def scanDone (c : Ctx) (s : XState) : Prop :=
  ∃ n, n < c.arg.length ∧ c.arg[n]! = 0 ∧ (∀ q, q < n → c.arg[q]! ≠ 0) ∧
    (s.core.read .rcx = 0#64 ∨ ∃ i, i < n ∧ s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i ∧ c.arg[i]! = 0x2f#8) ∧
    common c s

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** From `cmain`'s entry, the scan of `argv[0]` is entered (`0x403430`) or, for
an empty `argv[0]`, `set_program_name` is done (`0x4034a6`). -/
theorem vc_entry (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 0 →
      (s.core.read .rsp = c.sp0 - 8#64 ∧ s.core.read .rdi = c.sp0 ∧ Memory.WritesWithin c.m0 s.memory (W1 c.sp0)) →
      wpN Isa.sys8 Main.code Main.listing [(64, ⟨scanInv c, scanMeasure c⟩)] [(84, scanDone c), (182, postB c)] [] [] Main.base none 60 0 s := by
  intro s hlv hl hrip ⟨hsp, hdi, hww⟩
  have lo := hc.spLo
  have hi : c.sp0.toNat + 16 ≤ 2^64 := by
    have := hc.rw .read (by decide)
    rw [Memory.Permitted, Memory.checkSpan_iff] at this
    simp [Silmaril.Process.addressLimit] at this; omega
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hargc : loadN s.memory c.sp0 8 = some 1#64 := by
    rw [loadN_ww hww (fun i hi => by simp only [W1]; omega)]; exact hc.argc
  have hargv : loadN s.memory (c.sp0 + 8#64) 8 = some c.argv0 := by
    rw [loadN_ww hww (fun i hi => by simp only [W1]; rw [BitVec.toNat_add] at *; simp at *; omega)]; exact hc.argv0
  have hp0 : (c.argv0 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; rw [h] at hab; simp at hab
  have hpos : 0 < c.arg.length := by
    have := hc.argStr.1; cases h : c.arg with
    | nil => rw [h] at this; simp at this
    | cons _ _ => simp
  have hout : ∀ i < c.arg.length, ¬ W1 c.sp0 (c.argv0.toNat + i) := by
    intro i hi; simp only [W1]; omega
  have hL0 : loadN s.memory c.argv0 1 = some (c.arg[0].setWidth 64) :=
    cstring_load hww hc.argStr hout _ 0 hpos (by simp)
  have hro : Ro s.memory := fun a h1 h2 => by rw [hww.permits]; exact hc.ro a h1 h2
  have hpw : s.memory.Permitted .write (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .write (by decide))
  have hpr : s.memory.Permitted .read (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .read (by decide))
  have hdw : s.memory.Permitted .write 0x409010 0xa140 :=
    (hww.permitted_iff _ _ _).mpr (data_perm hc.mapped .write (by decide))
  sv_go [Main.listing, hrip, hl, hsp, hdi, hargc, hargv, hp0, hL0, Mem.ofReg, Mem.ofRip, Mem.ofIndex, Silmaril.X86.Lift.ix]
  · simp only [postB]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try (seg_read [hsp, hdi]))
    all_goals (try sv_mem)
    all_goals sv_within
  · rename_i hb
    have hnz : c.arg[0] ≠ 0 := by simpa using hb
    refine ⟨0, hc.argStr.lt hpos hnz, fun q hq => ?_, ?_, ?_, .inl ?_, ?_⟩
    · obtain rfl : q = 0 := by omega
      rw [getElem!_pos c.arg 0 hpos]; exact hnz
    · seg_read [hsp, hdi]; simp
    · seg_read [hsp, hdi]; rw [getElem!_pos c.arg 0 hpos]
    · seg_read [hsp, hdi]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try (seg_read [hsp, hdi]; done))
      all_goals (try sv_mem)
      all_goals (try sv_within)

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** One iteration of the scan of `argv[0]` for its last `/`: back to the loop head
with one more byte, or the terminating NUL found (`0x403444`). -/
theorem vc_scan (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 64 → scanInv c s →
      wpN Isa.sys8 Main.code Main.listing [(64, ⟨scanInv c, scanMeasure c⟩)] [(84, scanDone c), (182, postB c)] [] [] Main.base (some (scanMeasure c s)) 80 64 s := by
  intro s hlv hl hrip ⟨j, hj, hnz, hrax, hrdx, hrcx, hsp, hdi, hr11, hrsi, hr14, hww⟩
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  have hnw := hc.argStr.noWrap
  have hout : ∀ i < c.arg.length, ¬ W1 c.sp0 (c.argv0.toNat + i) := by
    intro i hi; simp only [W1]; omega
  have hro : Ro s.memory := fun a h1 h2 => by rw [hww.permits]; exact hc.ro a h1 h2
  have hpw : s.memory.Permitted .write (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .write (by decide))
  have hpr : s.memory.Permitted .read (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .read (by decide))
  have hdw : s.memory.Permitted .write 0x409010 0xa140 :=
    (hww.permitted_iff _ _ _).mpr (data_perm hc.mapped .write (by decide))
  generalize hR : c.argv0 + BitVec.ofNat 64 j = R at hrax
  have hnext : loadN s.memory (R + 1#64) 1 = some (c.arg[j+1]!.setWidth 64) := by
    subst hR; rw [add_ofNat_succ, getElem!_pos c.arg (j+1) hj]
    exact cstring_load hww hc.argStr hout _ (j+1) hj (toNat_add_ofNat _ _ (by omega))
  have hjl : j + 1 < c.arg.length := hj
  -- the common registers and the footprint
  have common_t : ∀ t : XState, t.memory = s.memory → t.core.read .rsp = s.core.read .rsp →
      t.core.read .rdi = s.core.read .rdi → t.core.read .r11 = s.core.read .r11 →
      t.core.read .rsi = s.core.read .rsi → t.core.read .r14 = s.core.read .r14 → common c t := by
    intro t hm e1 e2 e3 e4 e5
    exact ⟨e1.trans hsp, e2.trans hdi, e3.trans hr11, e4.trans hrsi, e5.trans hr14, hm ▸ hww⟩
  have hmeas : ∀ t : XState, t.core.read .rax = R + 1#64 → scanMeasure c t < scanMeasure c s := by
    intro t ht
    simp only [scanMeasure, ht, hrax]
    subst hR
    rw [add_ofNat_succ, add_ofNat_sub, add_ofNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hnz' : ∀ q, q ≤ j + 1 → c.arg[q]! ≠ 0 → c.arg[q]! ≠ 0 := fun _ _ h => h
  sv_go [Main.listing, hrip, hl, hsp, hdi, hrax, hrdx, hr11, hrsi, hr14, hnext]
  all_goals rename_i h1 h2
  all_goals (try simp only [beq_eq_false_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false] at h1 h2)
  · refine ⟨j + 1, hc.argStr.lt! hj h2, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge q (j + 1) with h | h
      · exact hnz q (by omega)
      · obtain rfl : q = j + 1 := by omega
        exact h2
    · seg_read []; subst hR; exact add_ofNat_succ _ _
    · seg_read []
    · seg_read []
      rcases hrcx with h | ⟨i, hi, h, hs⟩
      · exact .inl h
      · exact .inr ⟨i, by omega, h, hs⟩
    · exact common_t _ rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read [])
  · exact hmeas _ (by seg_read [])
  · refine ⟨j + 1, hj, h2, fun q hq => hnz q (by omega), ?_, ?_⟩
    · seg_read []
      rcases hrcx with h | ⟨i, hi, h, hs⟩
      · exact .inl h
      · exact .inr ⟨i, by omega, h, hs⟩
    · exact common_t _ rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read [])
  · refine ⟨j + 1, hc.argStr.lt! hj h2, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge q (j + 1) with h | h
      · exact hnz q (by omega)
      · obtain rfl : q = j + 1 := by omega
        exact h2
    · seg_read []; subst hR; exact add_ofNat_succ _ _
    · seg_read []
    · seg_read []; exact .inr ⟨j, by omega, hR.symm, h1⟩
    · exact common_t _ rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read [])
  · exact hmeas _ (by seg_read [])
  · refine ⟨j + 1, hj, h2, fun q hq => hnz q (by omega), ?_, ?_⟩
    · seg_read []; exact .inr ⟨j, by omega, hR.symm, h1⟩
    · exact common_t _ rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read [])

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
