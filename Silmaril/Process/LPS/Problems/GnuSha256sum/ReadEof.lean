module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysTotal

/-! # A zero-length `read` goes to the padding (`EofStep`, VERIFIED)

At `0x402f06`, after `read(0, iobuf, 32768)` returned `0`, `digest_file` runs
`test %rax,%rax; js; mov 0x88(%rsp),%rdx; je 0x403034` and reaches the padding with the
`struct sha` unchanged. `Digest.update_absorbs` (the `sha_update` VC) only says that *some*
stop is reached; with no cut point and the single stop `0x403034`, the same VC machinery
shows that the stop is the padding (`eof_runs`). This discharges `EofStep` of `SysTotal`.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Update

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys

/-- The only stop of the zero-length segment: the padding. -/
def eofStops (c : Ctx) : List (Nat × (XState → Prop)) := [(324, postEof c)]

set_option maxRecDepth 20000 in
theorem vc_eof_entry (r11 : Core → Word) (c : Ctx) (hc : c.chunk = []) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 22 → pre c s →
      wpN (Isa.sys r11) code listing [] (eofStops c) (calls r11) (subs r11) base none 16 22 s := by
  intro s hlv hl hrip hpre
  obtain ⟨hF, hax, hB⟩ := hpre
  have htot := hB.hTotal
  rw [← hF.rsp] at htot
  rw [hc, List.length_nil] at hax
  seg_vc [listing, eofStops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hax, htot]
  simp only [BitVec.and_self]
  refine ⟨fun hm => by simp at hm, fun _ => ⟨fun _ => ?_, fun hnz => by simp at hnz⟩⟩
  exact ⟨hF.congr rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []),
    hc, hB, by seg_read []⟩

/-- **VERIFIED.** After `read` returned `0` at `0x402f06`, retiring steps reach the padding
`0x403034` with the struct unchanged. -/
theorem eof_runs (r11 : Core → Word) (c : Ctx) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 22)
    (hpre : pre c s) (hc : c.chunk = []) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep s t ∧ t.faulted = false ∧
      Loaded t.memory base code ∧ t.core.rip = base + BitVec.ofNat 64 324 ∧ postEof c t := by
  have hvc : vc (Isa.sys r11) code listing [] (eofStops c) (calls r11) (subs r11) base 22
      (pre c) 16 := ⟨vc_eof_entry r11 c hc, fun oc hoc => by simp at hoc⟩
  obtain ⟨t, hr, ht, hrip', hl', hlv'⟩ := sound_one (I := Isa.sys r11) listing_valid hvc s hlv
    hl hrip hpre
  exact ⟨t, hr, hlv', hl', hrip', ht⟩

end Silmaril.Apps.Sha256sum.Binary.Digest.Update

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Digest

/-- **VERIFIED. `EofStep`.** -/
theorem eofStep : EofStep := by
  intro e consumed s hlv hl h
  obtain ⟨hrip, hF, hchunk, hlen, hax, blocks, tail, hr, hb⟩ := h
  have hpre : Update.pre (ctxOf e consumed [] blocks tail s) s :=
    ⟨⟨hF.rsp, hF.rbx, rfl, rfl, hchunk, hlen, hF.spAlign, hF.spLow, hF.spHigh, hF.stackW,
      hF.stackR, hF.code, hF.kTable, .refl _ _⟩, hax, hb⟩
  obtain ⟨t, hrun, hlv', hl', hrip', hF', _, hb', hrdx⟩ :=
    Update.eof_runs (fun _ => 0) _ s hlv hl hrip hpre rfl
  exact ⟨t, hrun, hlv', hl', hrip', LoopFrame.of_frame rfl hF rfl rfl hF', hrdx, blocks, tail,
    hr, hb'⟩

/-- The read loop with `EofStep` discharged (VERIFIED from `ReadCall` and `KeepsJ`). -/
theorem readLoop' {domain : List Byte → Prop} {J : Loop → Cut} (readCall : ReadCall domain J)
    (keep : KeepsJ J) :
    Seg domain (fun w message g h => ∃ e, HeadJ J e w message g h) (PadJ J) :=
  readLoop readCall keep eofStep

end Silmaril.Process.LPS.Problems.GnuSha256sum
