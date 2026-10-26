module

public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainLoop
public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainTail
public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainCut

/-! # `cmain` from `AtOptParse` to `AtDigestEntry` (argv = [prog], any environment)

From `0x4034a6` (after `set_program_name`), `cmain` scans the environment for
`POSIXLY_CORRECT=` (`CmainLoop`), finds no option (`argc = 1`), passes the option checks on
the image's globals, stores the default operand `"-"`, takes `je 0x40418f` (`do_check = 0`)
and calls `digest_file("-", bin, &missing)` from `0x40419a` (`CmainTail`), with no system
call. `cmain_runs` composes the segments into a run of `rStep8` (the silent steps of
`GStep`) ending at `AtDigestEntryW`, which is `AtDigestEntry` with what `cmain`'s own frame
holds at the call (`rbx = do_check = 0`, `r12 = "-"`, `r14 = &missing`, the locals `ok = 1`, `optind - 1 = 0`,
`argc' = 1`, and `binary = 0`).

Everything here is VERIFIED (no `sorry`, no new axiom; `#print axioms cmain_runs` lists only
`propext`, `Classical.choice`, `Quot.sound`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Machine.Execution (Reaches)

theorem readWith_of_loadN {m : Memory} {a : Word} {k : Nat} {v : Word} (h : loadN m a k = some v)
    (hk : k ≤ 8) : m.readWith .read a.toNat k = some (leBytes v k) := by
  unfold loadN at h
  cases hr : m.readBytes a.toNat k with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact holdsLE_of_readBytes hr hk

/-! ## The launch memory -/

theorem above_bound {c : Ctx} (hc : LaunchFacts c) :
    c.sp0.toNat + 8 * (c.envs.length + 4) < 18446744073709551616 := by
  have := hc.above c.argv0 (by simp)
  have := c.argv0.isLt
  omega

/-- The globals and permissions the tail needs, from the launch. -/
theorem g0 {c : Ctx} (hc : LaunchFacts c) : G0 c.sp0 c.m0 where
  lo := hc.spLo
  hi := by have := above_bound hc; omega
  pw := hc.rw .write (by decide)
  pr := hc.rw .read (by decide)
  gw := seg3_write hc.mapped
  gr := Memory.readWith_permitted (readWith_segment hc.mapped seg3_mem Image.image_wf
    (acc := .read) (by decide) 0 4 (by decide) (by decide))
  g1 := g_zero hc.mapped 0x10 (by omega)
  g2 := g_delim hc.mapped
  g3 := g_binary hc.mapped
  g4 := g_zero hc.mapped 0x1094 (by omega)
  g5 := g_zero hc.mapped 0x10a4 (by omega)
  g6 := g_zero hc.mapped 0x10a0 (by omega)
  g7 := g_zero hc.mapped 0x109c (by omega)
  g8 := g_zero hc.mapped 0x1098 (by omega)
  g9 := g_zero hc.mapped 0x14 (by omega)
  ro := hc.ro

/-- The environment of the scan, from the launch context and the memory at `AtOptParse`. -/
def envOf (c : Ctx) (m : Memory) : Env where
  sp0 := c.sp0
  m1 := m
  N := c.envs.length
  ev k := c.envs.getD k 0
  B k j := (c.envStrs.getD k []).getD j 0

theorem getD_lt {α : Type} {l : List α} {k : Nat} {d : α} (h : k < l.length) :
    l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_len {α : Type} {l : List α} {d : α} : l.getD l.length d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_refl _), Option.getD_none]

theorem w1_lt {sp0 : Word} {a : Nat} (lo : 0x423150 ≤ sp0.toNat) (h : W1 sp0 a) : a < sp0.toNat := by
  unfold W1 at h; omega

theorem envFacts {c : Ctx} (hc : LaunchFacts c) {m : Memory}
    (hww : Memory.WritesWithin c.m0 m (W1 c.sp0)) : EnvFacts (envOf c m) := by
  have hab := above_bound hc
  have lo := hc.spLo
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj hne => ?_, fun j hj => ?_, ?_⟩
  · simp only [envOf] at hk ⊢
    have hq : (c.sp0 + BitVec.ofNat 64 (24 + 8 * k)).toNat = c.sp0.toNat + (24 + 8 * k) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + 8 * k) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [loadN_ww hww (fun i hi hw => by have := w1_lt lo hw; omega)]
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · rw [getD_lt hk]; exact hc.envw k hk
    · rw [getD_len]; exact hc.envEnd
  · simp only [envOf] at hk ⊢
    rw [getD_lt hk]
    intro h0
    have := hc.above _ (List.mem_cons_of_mem _ (List.getElem_mem hk))
    rw [h0] at this
    simp at this
  · simp only [envOf]; exact getD_len
  · simp only [envOf] at hk hne ⊢
    have hk' : k < c.envStrs.length := hc.envLen ▸ hk
    rw [getD_lt hk'] at hne ⊢
    rw [getD_lt hk]
    have hs := hc.envStr k hk hk'
    have hjl := cstr_len hs.1 hne
    have hpa := hc.above _ (List.mem_cons_of_mem _ (List.getElem_mem hk))
    exact str_load hww hs (fun i hi hw => by have := w1_lt lo hw; omega) hjl
  · simp only [envOf]
    rw [loadN_ww hww (fun i hi hw => by
      have := w1_lt lo hw
      have hq : (BitVec.ofNat 64 j + 1#64 + 0x4060e8#64).toNat = 0x4060e8 + (j + 1) := by
        rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
        omega
      unfold W1 at hw
      omega)]
    exact pat_load hc.mapped hj
  · simp only [envOf]; omega

/-! ## The composition -/

theorem main_out_w1 {sp0 : Word} (lo : 0x423150 ≤ sp0.toNat) :
    ∀ i < Main.code.length, ¬ W1 sp0 (Main.base.toNat + i) := by
  intro i hi hw
  rw [Main.code_length] at hi
  rw [Main.base_toNat] at hw
  unfold W1 at hw
  omega

theorem call_out_w2 {sp0 : Word} (lo : 0x423150 ≤ sp0.toNat) :
    ∀ i < Call.code.length, ¬ W2 sp0 (Call.base.toNat + i) := by
  intro i hi hw
  rw [Call.code_length] at hi
  rw [Call.base_toNat] at hw
  unfold W2 W1 at hw
  omega

set_option maxRecDepth 100000 in
/-- **VERIFIED. `cmain` from `AtOptParse` to `digest_file`'s entry.** Retiring steps (no
system call) lead from `AtOptParse` to `AtDigestEntryW`. -/
theorem cmain_runs {c : Ctx} (hc : LaunchFacts c) {s : XState} (hs : AtOptParse c s) :
    ∃ t, Reaches rStep8 s t ∧ AtDigestEntryW c t := by
  have hG := g0 hc
  have lo := hc.spLo
  -- the environment scan
  have hlM : Loaded s.memory Main.base Main.code :=
    loaded_ww hs.mem (Main.loaded hc.mapped) (main_out_w1 lo)
  have hF : Frame (envOf c s.memory) s := ⟨hs.rsp, hs.r11, hs.r14, hs.r15, hs.rbx, rfl⟩
  have hrip : s.core.rip = Main.base + BitVec.ofNat 64 182 := by rw [hs.rip]; rfl
  obtain ⟨t1, r1, hF1, hrip1, hl1, hlv1⟩ :=
    loop_runs _ (envFacts hc hs.mem) s hs.faulted hlM hrip hF
  have hww1 : Memory.WritesWithin c.m0 t1.memory (W1 c.sp0) := by
    rw [hF1.mem]; exact hs.mem
  -- chunk A
  obtain ⟨t2, r2, ⟨a1, a2, a3, ⟨a4⟩⟩, hrip2, hl2, hlv2⟩ := A_runs c.sp0 c.m0 hG t1 hlv1 hl1 hrip1
    hF1.rsp hF1.r11 hF1.r14 hF1.r15 hF1.rbx hww1
  have hww2 : Memory.WritesWithin c.m0 t2.memory (W1 c.sp0) := a4 ()
  -- chunk B
  obtain ⟨t3, r3, ⟨b1, b2, b3, b4, b5⟩, hrip3, hl3, hlv3⟩ := B_runs c.sp0 c.m0 hG t2 hlv2 hl2 hrip2
    a1 a2 a3 hww2
  have hww3 : Memory.WritesWithin c.m0 t3.memory (W1 c.sp0) := by rw [b5]; exact hww2
  -- chunk C
  obtain ⟨t4, r4, hC, hrip4, hl4, hlv4⟩ := C_runs c.sp0 c.m0 hG t3 hlv3 hl3 hrip3 b1 b2 b3 b4 hww3
  have hww4 : Memory.WritesWithin c.m0 t4.memory (W2 c.sp0) := hC.2.2.2.2.1.ww ()
  -- chunk D
  have hlC : Loaded t4.memory Call.base Call.code :=
    loaded_ww hww4 (Call.loaded hc.mapped) (call_out_w2 lo)
  have hrip4' : t4.core.rip = Call.base + BitVec.ofNat 64 0 := by rw [hrip4]; rfl
  obtain ⟨t5, r5, ⟨d1, d2, d3, d4, d5, d6, d7, d14, ⟨d8⟩, d9, d10, d11, d12⟩, hrip5, -, hlv5⟩ :=
    D_runs c.sp0 c.m0 hG t4 hlv4 hlC hrip4' hC
  refine ⟨t5, ((((r1.trans r2).trans r3).trans r4).trans r5), ⟨⟨hlv5, ?_, d1, d2, d3, d4, d5, ?_⟩,
    d7, d6, d14, readWith_of_loadN d9 (by decide), readWith_of_loadN d10 (by decide),
    readWith_of_loadN d11 (by decide), ?_⟩⟩
  · rw [hrip5]; rfl
  · unfold W2 W1; exact d8 ()
  · have hb : (Main.base + 23584#64).toNat = 0x409010 := by
      rw [BitVec.toNat_add, Main.base_toNat]; rfl
    rw [← hb]; exact readWith_of_loadN d12 (by decide)

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
