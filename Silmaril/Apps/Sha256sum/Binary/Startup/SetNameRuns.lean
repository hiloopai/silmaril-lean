module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetName
public import Silmaril.X86.SegVC.Mono

/-! # `set_program_name` (`sha256sum-min`): from `cmain`'s entry to `AtOptParse`

After the scan of `argv[0]` (`SetName.vc_entry`, `vc_scan`), `set_program_name` checks the
base name: no `/` (`rcx = 0`) goes straight to the join `0x403486` (`vc_post0`); a last `/`
at `i` is followed by the `"/.libs/"` check (a loop at `0x403476`, guarded by `i + 1 > 6`) and
the `"lt-"` check (`0x4036d9`), which also end at the join. From the join, `program_name` and
`getopt_argv0` are stored and `AtOptParse` (`0x4034a6`) is reached (`vc_join`).

`runs` composes the segments, with the `/` case as the hypothesis `SlashCase` (proved
separately: `JoinPost` there implies `common`).

Status: everything proved here is VERIFIED (no `sorry`); `SlashCase` is a hypothesis.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup
open Silmaril.Machine.Execution (Reaches)

set_option maxRecDepth 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86.Lift (ix)
open Silmaril.X86.Ext (Mem)

set_option maxRecDepth 100000 in
/-- The entries of `Main.listing` on the checks of the base name. -/
def postListing : List (Nat × Silmaril.X86.Ext8.Instr × Nat) := [
  (84, .base (.test (.q) (.reg (.rcx)) (.rcx)), 3), -- 0x403444
  (87, .base (.jcc8 (.e) 0x3a#8), 2), -- 0x403447
  (89, .base (.lea (.q) (.r8) (Mem.ofReg .rcx none 0x00000001#32)), 4), -- 0x403449
  (93, .base (.mov (.q) (.reg (.rax)) (.r8)), 3), -- 0x40344d
  (96, .base (.alu (.q) (.sub) (.reg (.rax)) (.rdi)), 3), -- 0x403450
  (99, .base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x06#8), 4), -- 0x403453
  (103, .base (.jcc8 (.le) 0x2a#8), 2), -- 0x403457
  (105, .base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2), -- 0x403459
  (107, .base (.jmp8 0x19#8), 2), -- 0x40345b
  (112, .base (.test8 (.reg (.rdx)) (.rdx)), 2), -- 0x403460
  (114, .base (.jcc (.e) 0x00000271#32), 6), -- 0x403462
  (120, .base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4), -- 0x403468
  (124, .base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x07#8), 4), -- 0x40346c
  (128, .base (.jcc (.e) 0x00000263#32), 6), -- 0x403470
  (134, .base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rcx (some (ix .rax 0x0#2)) 0xfffffffa#32))), 5), -- 0x403476
  (139, .new (.aluR (.cmp) (.low (.rdx)) (.mem (Mem.ofReg .rax none 0x004060dc#32))), 6), -- 0x40347b
  (145, .base (.jcc8 (.e) 0xdd#8), 2), -- 0x403481
  (147, .base (.mov (.q) (.reg (.r8)) (.rdi)), 3), -- 0x403483
  (150, .base (.movsxd (.rsi) (.reg (.rsi))), 3), -- 0x403486
  (153, .base (.lea (.q) (.r15) (Mem.ofReg .r11 none 0x00000008#32)), 4), -- 0x403489
  (157, .base (.alu (.d) (.xor) (.reg (.r12)) (.r12)), 3), -- 0x40348d
  (160, .base (.mov (.q) (.mem (Mem.ofRip 0x0000ec89#32)) (.r8)), 7), -- 0x403490
  (167, .base (.lea (.q) (.rbx) (Mem.ofIndex (some (ix .rsi 0x3#2)) 0x00000008#32)), 8), -- 0x403497
  (175, .base (.mov (.q) (.mem (Mem.ofRip 0x0000ec72#32)) (.rdi)), 7), -- 0x40349f
  (745, .base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2), -- 0x4036d9
  (747, .base (.jmp8 0x0d#8), 2), -- 0x4036db
  (752, .base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4), -- 0x4036e0
  (756, .base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x03#8), 4), -- 0x4036e4
  (760, .base (.jcc8 (.e) 0x15#8), 2), -- 0x4036e8
  (762, .base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rcx (some (ix .rax 0x0#2)) 0x00000001#32))), 5), -- 0x4036ea
  (767, .new (.aluR (.cmp) (.low (.rdx)) (.mem (Mem.ofReg .rax none 0x004060e4#32))), 6), -- 0x4036ef
  (773, .base (.jcc (.ne) 0xfffffd8b#32), 6), -- 0x4036f5
  (779, .base (.test8 (.reg (.rdx)) (.rdx)), 2), -- 0x4036fb
  (781, .base (.jcc8 (.ne) 0xe1#8), 2), -- 0x4036fd
  (783, .base (.lea (.q) (.r8) (Mem.ofReg .rcx none 0x00000004#32)), 4), -- 0x4036ff
  (787, .base (.jmp 0xfffffd7e#32), 5) -- 0x403703
  ]

set_option maxRecDepth 100000 in
theorem postListing_valid : Listing.valid Isa.sys8 Main.code postListing = true := by decide

macro "cmn_close" : tactic => `(tactic| (simp only [common]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (seg_read [‹State.read _ Reg.rsp = _›, ‹State.read _ Reg.rdi = _›, ‹State.read _ Reg.r11 = _›, ‹State.read _ Reg.rsi = _›, ‹State.read _ Reg.r14 = _›]; done) | (with_reducible assumption) | (sv_mem; done)))

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** From the join `0x403486` (`program_name` in `r8`): `program_name` and
`getopt_argv0` stored, `0x4034a6` reached. -/
theorem vc_join (c : Ctx) (hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 150 → common c s →
      wpN Isa.sys8 Main.code postListing [] [(182, postB c)] [] [] Main.base none 20 150 s := by
  intro s hlv hl hrip ⟨hsp, hdi, hr11, hrsi, hr14, hww⟩
  have lo := hc.spLo
  have hro : Ro s.memory := fun a h1 h2 => by rw [hww.permits]; exact hc.ro a h1 h2
  have hdw : s.memory.Permitted .write 0x409010 0xa140 :=
    (hww.permitted_iff _ _ _).mpr (data_perm hc.mapped .write (by decide))
  sv_go [postListing, hrip, hl, hsp, hdi, hr11, hrsi, hr14]
  simp only [postB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (seg_read [hsp, hdi, hr11, hrsi, hr14]))
  all_goals (try sv_mem)
  all_goals (try sv_within)


/-- The scan exit without a `/`. -/
def scanDone0 (c : Ctx) (s : XState) : Prop := scanDone c s ∧ s.core.read .rcx = 0#64

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** The scan exit without a `/` goes to the join. -/
theorem vc_post0 (c : Ctx) (_hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 84 → scanDone0 c s →
      wpN Isa.sys8 Main.code postListing [] [(150, common c)] [] [] Main.base none 20 84 s := by
  intro s hlv hl hrip ⟨⟨n, hn, hn0, hnz, _, hsp, hdi, hr11, hrsi, hr14, hww⟩, h0⟩
  sv_go [postListing, hrip, hl, hsp, hdi, hr11, hrsi, hr14, h0]
  all_goals cmn_close

/-! ## Composition -/

/-- **The `/` case** (hypothesis): from the scan exit with a last `/`, retiring steps reach
the join `0x403486` with the base registers. -/
def SlashCase (c : Ctx) : Prop :=
  ∀ s : XState, s.faulted = false → s.core.rip = 0x403444#64 → scanDone c s →
    s.core.read .rcx ≠ 0#64 →
      ∃ t, Reaches rStep8 s t ∧ t.faulted = false ∧ t.core.rip = 0x403486#64 ∧ common c t

theorem main_loaded {c : Ctx} (hc : LaunchFacts c) {m : Memory}
    (hww : Memory.WritesWithin c.m0 m (W1 c.sp0)) : Loaded m Main.base Main.code := by
  have := Main.loaded hc.mapped
  unfold Loaded at this ⊢
  rw [hww.fetchBytes (fun o ho hin => by
    simp only [W1] at hin; have := hc.spLo; rw [Main.base_toNat] at hin
    rw [Main.code_length] at ho; omega)]
  exact this

theorem postB_atOptParse {c : Ctx} {t : XState} (h : postB c t) (hlv : t.faulted = false)
    (hrip : t.core.rip = Main.base + BitVec.ofNat 64 182) : AtOptParse c t :=
  ⟨hlv, hrip.trans rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- From the join to `AtOptParse`. -/
theorem join_runs (c : Ctx) (hc : LaunchFacts c) (s : XState) (hlv : s.faulted = false)
    (hrip : s.core.rip = Main.base + BitVec.ofNat 64 150) (h : common c s) :
    ∃ t, Reaches rStep8 s t ∧ AtOptParse c t := by
  have hvc : vc Isa.sys8 Main.code postListing [] [(182, postB c)] [] [] Main.base 150
      (common c) 20 := ⟨vc_join c hc, fun oc hoc => by simp at hoc⟩
  obtain ⟨u, hr, hu, hrip', -, hlv'⟩ := sound_one postListing_valid hvc s hlv
    (main_loaded hc h.2.2.2.2.2) hrip h
  exact ⟨u, hr, postB_atOptParse hu hlv' hrip'⟩

/-- **VERIFIED from `SlashCase`. `set_program_name`**: from `cmain`'s entry, retiring steps
(no system call) reach `AtOptParse`. -/
theorem runs (c : Ctx) (hc : LaunchFacts c) (hslash : SlashCase c) (s : XState)
    (h : AtCmainEntry c s) : ∃ t, Reaches rStep8 s t ∧ AtOptParse c t := by
  have hrip : s.core.rip = Main.base + BitVec.ofNat 64 0 := h.rip.trans rfl
  have hvc : vc Isa.sys8 Main.code Main.listing [(64, ⟨scanInv c, scanMeasure c⟩)]
      [(84, scanDone c), (182, postB c)] [] [] Main.base 0
      (fun s => s.core.read .rsp = c.sp0 - 8#64 ∧ s.core.read .rdi = c.sp0 ∧
        Memory.WritesWithin c.m0 s.memory (W1 c.sp0)) 80 := by
    refine ⟨fun s hlv hl hrip hpre => wpN_mono (by omega) (vc_entry c hc s hlv hl hrip hpre), ?_⟩
    intro oc hoc s hlv hl hrip hinv
    simp only [List.mem_singleton] at hoc
    subst hoc
    exact vc_scan c hc s hlv hl hrip hinv
  obtain ⟨o, q, t, hq, ht, hr, hrip', hl', hlv'⟩ :=
    sound Main.listing_valid hvc s h.faulted (main_loaded hc h.mem) hrip ⟨h.rsp, h.rdi, h.mem⟩
  simp only [List.lookup_cons, List.lookup_nil] at hq
  split at hq
  · rename_i ho
    have ho : o = 84 := by simpa using ho
    subst ho
    cases hq
    -- the scan's exit: to the join
    obtain ⟨u, hr2, hlv2, hrip2, hu⟩ : ∃ u, Reaches rStep8 t u ∧ u.faulted = false ∧
        u.core.rip = Main.base + BitVec.ofNat 64 150 ∧ common c u := by
      by_cases h0 : t.core.read .rcx = 0#64
      · have hvc2 : vc Isa.sys8 Main.code postListing [] [(150, common c)] [] [] Main.base 84
            (scanDone0 c) 20 := ⟨vc_post0 c hc, fun oc hoc => by simp at hoc⟩
        obtain ⟨u, hr2, hu, hrip2, -, hlv2⟩ :=
          sound_one postListing_valid hvc2 t hlv' hl' hrip' ⟨ht, h0⟩
        exact ⟨u, hr2, hlv2, hrip2, hu⟩
      · obtain ⟨u, hr2, hlv2, hrip2, hu⟩ := hslash t hlv' (hrip'.trans rfl) ht h0
        exact ⟨u, hr2, hlv2, hrip2.trans rfl, hu⟩
    obtain ⟨v, hr3, hv⟩ := join_runs c hc u hlv2 hrip2 hu
    exact ⟨v, hr.trans (hr2.trans hr3), hv⟩
  · split at hq
    · rename_i ho
      have ho : o = 182 := by simpa using ho
      subst ho
      cases hq
      exact ⟨t, hr, postB_atOptParse ht hlv' hrip'⟩
    · cases hq

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
