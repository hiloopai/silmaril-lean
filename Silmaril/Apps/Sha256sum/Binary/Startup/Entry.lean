module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts

/-! # `_start` of `sha256sum-min`, to `cmain`'s entry, by the segment VC generator

`_start` (`0x401000`) runs `xor %ebp,%ebp; mov %rsp,%rdi; and $-16,%rsp; call cmain`. From the
launch stack pointer `sp0` (aligned, so `and` keeps it), the `call` pushes the return address
`0x40100e` at `sp0 - 8` and enters `cmain` (`0x4033f0`) with `rdi = sp0` and `rbp = 0`.

* `vc_start` (VERIFIED): the VC of the `Start` region, from `_start` to `cmain`'s entry;
* `start_runs` (VERIFIED): retiring steps reach `AtCmainEntry`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN Mem)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys

namespace Entry

set_option maxRecDepth 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

/-- The launch at `_start`, relative to the context. -/
def pre (c : Ctx) (s : XState) : Prop :=
  s.core.read .rsp = c.sp0 ∧ Memory.WritesWithin c.m0 s.memory (W1 c.sp0)

/-- The stop: `cmain`'s entry is offset `0x23f0` of the `Start` region. -/
def stops (c : Ctx) : List (Nat × (XState → Prop)) := [(0x23f0, AtCmainEntry c)]

set_option maxHeartbeats 4000000 in
/-- **VERIFIED.** From `_start`, the four instructions reach `cmain`'s entry. -/
theorem vc_start (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Start.base Start.code →
      s.core.rip = Start.base + BitVec.ofNat 64 0 → pre c s →
      wpN Isa.sys8 Start.code Start.listing [] (stops c) [] [] Start.base none 8 0 s := by
  intro s hlv hl hrip ⟨hsp, hww⟩
  have lo := hc.spLo
  have hi := hc.spHi
  have hal : c.sp0 &&& 18446744073709551600#64 = c.sp0 := and16 _ hc.aligned
  have hro : Ro s.memory := fun a h1 h2 => by rw [hww.permits]; exact hc.ro a h1 h2
  have hpw : s.memory.Permitted .write (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .write (by decide))
  have hpr : s.memory.Permitted .read (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (hc.rw .read (by decide))
  sv_go [Start.listing, stops, hrip, hl, hsp, hal]
  refine ⟨hlv, rfl, ?_, ?_, ?_⟩
  all_goals (try (seg_read [hsp]; done))
  · sv_mem
    sv_within

/-- **VERIFIED.** From the launch at `_start`, retiring steps of the `Ext8` machine reach
`cmain`'s entry (`AtCmainEntry`, the pre-state of `SetName.vc_entry`). -/
theorem start_runs (c : Ctx) (hc : LaunchFacts c) (s : XState) (hlv : s.faulted = false)
    (hrip : s.core.rip = 0x401000#64) (hsp : s.core.read .rsp = c.sp0)
    (hm : s.memory = c.m0) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep8 s t ∧ AtCmainEntry c t := by
  have hww : Memory.WritesWithin c.m0 s.memory (W1 c.sp0) := hm ▸ Memory.WritesWithin.refl _ _
  have hvc : vc Isa.sys8 Start.code Start.listing [] (stops c) [] [] Start.base 0 (pre c) 8 :=
    ⟨vc_start c hc, fun oc hoc => by simp at hoc⟩
  obtain ⟨t, hr, ht, -, -, -⟩ := sound_one (I := Isa.sys8) Start.listing_valid hvc s hlv
    (Start.loaded (by show Image.image.Mapped s.memory; rw [hm]; exact hc.mapped)) hrip ⟨hsp, hww⟩
  exact ⟨t, reaches_sys8 hr, ht⟩

end Entry

end Silmaril.Apps.Sha256sum.Binary.Startup
