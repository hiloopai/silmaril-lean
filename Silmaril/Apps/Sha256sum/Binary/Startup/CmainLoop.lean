module

public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainBase

/-! # `cmain`'s scan of the environment for `POSIXLY_CORRECT=`

From `AtOptParse` (`0x4034a6`) the scan runs over the `envp` words; for each string it
compares at most 16 bytes with `"POSIXLY_CORRECT="` (`0x4060e8`) and sets `r12` on a match. It
ends at `0x4034f7` with the frame registers unchanged and memory untouched.

Cut points: the outer loop head `0x4034b8` (measure `17 * envs left`), the inner compare
`0x4034e5` (measure `17 * envs left - 1 - index`); the stop `0x4034f7`.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup.Main
open Silmaril.Machine.Execution (Reaches)


/-- The environment of the scan. -/
structure Env where
  sp0 : Word
  m1 : Memory
  N : Nat
  ev : Nat → Word
  B : Nat → Nat → Byte

structure EnvFacts (e : Env) : Prop where
  words : ∀ k ≤ e.N, loadN e.m1 (e.sp0 + BitVec.ofNat 64 (24 + 8 * k)) 8 = some (e.ev k)
  nz : ∀ k < e.N, e.ev k ≠ 0#64
  last : e.ev e.N = 0#64
  bytes : ∀ k < e.N, ∀ j < 16, (∀ i < j, e.B k i ≠ 0) →
    loadN e.m1 (e.ev k + BitVec.ofNat 64 j) 1 = some ((e.B k j).setWidth 64)
  pats : ∀ j < 16, loadN e.m1 (BitVec.ofNat 64 j + 1#64 + 0x4060e8#64) 1 =
    some ((pat.getD (j + 1) 0).setWidth 64)
  small : 24 + 8 * (e.N + 1) < 18446744073709551616

/-- The registers the scan keeps. -/
structure Frame (e : Env) (s : XState) : Prop where
  rsp : s.core.read .rsp = e.sp0 - 240#64
  r11 : s.core.read .r11 = e.sp0
  r14 : s.core.read .r14 = 1#64
  r15 : s.core.read .r15 = e.sp0 + 8#64
  rbx : s.core.read .rbx = 16#64
  mem : s.memory = e.m1

theorem frame_of {e : Env} {s : XState} (hF : Frame e s) (t : XState)
    (h1 : t.core.read .rsp = s.core.read .rsp) (h2 : t.core.read .r11 = s.core.read .r11)
    (h3 : t.core.read .r14 = s.core.read .r14) (h4 : t.core.read .r15 = s.core.read .r15)
    (h5 : t.core.read .rbx = s.core.read .rbx) (hm : t.memory = e.m1) : Frame e t :=
  ⟨h1.trans hF.rsp, h2.trans hF.r11, h3.trans hF.r14, h4.trans hF.r15, h5.trans hF.rbx, hm⟩

theorem sw8 (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  have h1 : x.toNat % 2 ^ 32 = x.toNat := Nat.mod_eq_of_lt (by omega)
  have h2 : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [h1, h2]

theorem j16 {j : Nat} (hj : j < 16) (h : (BitVec.ofNat 64 (j + 1) == 16#64) = false) :
    j + 1 < 16 := by
  rcases Nat.lt_or_ge (j + 1) 16 with h' | h'
  · exact h'
  · have : j + 1 = 16 := by omega
    rw [this] at h; simp at h

theorem pre_succ {e : Env} {k j : Nat} (hpre : ∀ i < j, e.B k i = pat.getD i 0)
    (h : (e.B k j == pat.getD j 0) = true) : ∀ i < j + 1, e.B k i = pat.getD i 0 := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
  · exact hpre i hi
  · simpa using h

theorem next_lt {e : Env} (hE : EnvFacts e) {k : Nat} (hk : k ≤ e.N)
    (h : (!e.ev k == 0#64) = true) : k < e.N := by
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · exact hk
  · rw [hE.last] at h; simp at h

theorem first_lt {e : Env} (hE : EnvFacts e) (h : (e.ev 0 == 0#64) = false) : 0 < e.N := by
  rcases Nat.eq_zero_or_pos e.N with h0 | h0
  · have := hE.last; rw [h0] at this; rw [this] at h; simp at h
  · exact h0

macro "fr " h:ident : tactic => `(tactic| exact frame_of $h _ (by seg_read []) (by seg_read [])
  (by seg_read []) (by seg_read []) (by seg_read []) rfl)

def kOf (e : Env) (s : XState) : Nat := ((s.core.read .rsi - e.sp0).toNat - 24) / 8

def inv200 (e : Env) (s : XState) : Prop :=
  Frame e s ∧ ∃ k, k < e.N ∧ s.core.read .rsi = e.sp0 + BitVec.ofNat 64 (24 + 8 * k) ∧
    s.core.read .rcx = e.ev k

def inv245 (e : Env) (s : XState) : Prop :=
  Frame e s ∧ ∃ k, k < e.N ∧ s.core.read .rsi = e.sp0 + BitVec.ofNat 64 (24 + 8 * k) ∧
    s.core.read .rcx = e.ev k ∧ ∃ j, j < 16 ∧ s.core.read .rax = BitVec.ofNat 64 j ∧
      s.core.read .rdx = (pat.getD j 0).setWidth 64 ∧ ∀ i < j, e.B k i = pat.getD i 0

def loopCuts (e : Env) : List (Nat × Cut (σ := XState)) :=
  [(200, { inv := inv200 e, measure := fun s => 17 * (e.N - kOf e s) }),
   (245, { inv := inv245 e, measure := fun s => 17 * (e.N - kOf e s) - 1 - (s.core.read .rax).toNat })]

def loopStops (e : Env) : List (Nat × (XState → Prop)) := [(263, Frame e)]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem vc_entry (e : Env) (hE : EnvFacts e) (s : XState) (_hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 182)
    (hF : Frame e s) :
    wpN Isa.sys8 code listing (loopCuts e) (loopStops e) [] [] base none 14 182 s := by
  have h0 := hE.words 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  rw [hF.mem] at hl
  sv [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, execNew_cmp_mem, loopCuts, loopStops, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl,
    hF.rsp, hF.r11, hF.r14, hF.r15, hF.rbx, hF.mem, h0, inv200, kOf]
  repeat' (first | (intro _) | (apply And.intro))
  all_goals first
    | fr hF
    | exact ⟨0, first_lt hE (by assumption), rfl, rfl⟩

theorem words_succ (k : Nat) :
    BitVec.ofNat 64 (24 + 8 * k) + 8#64 = BitVec.ofNat 64 (24 + 8 * (k + 1)) := by
  rw [BitVec.ofNat_add_ofNat]; congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem vc_200 (e : Env) (hE : EnvFacts e) (s : XState) (_hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 200)
    (hinv : inv200 e s) :
    wpN Isa.sys8 code listing (loopCuts e) (loopStops e) [] [] base
      (some (17 * (e.N - kOf e s))) 14 200 s := by
  obtain ⟨hF, k, hk, hrsi, hrcx⟩ := hinv
  rw [hF.mem] at hl
  sv [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, execNew_cmp_mem, loopCuts, loopStops, inv245, kOf, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl,
    hF.rsp, hF.r11, hF.r14, hF.r15, hF.rbx, hF.mem, hrsi, hrcx]
  have hsm := hE.small
  have ht1 : (24 + 8 * k) % 18446744073709551616 = 24 + 8 * k := Nat.mod_eq_of_lt (by omega)
  rw [ht1]
  refine ⟨⟨?_, k, hk, rfl, rfl, 0, by omega, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, by omega⟩
  fr hF

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem vc_245 (e : Env) (hE : EnvFacts e) (s : XState) (_hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 245)
    (hinv : inv245 e s) :
    wpN Isa.sys8 code listing (loopCuts e) (loopStops e) [] [] base
      (some (17 * (e.N - kOf e s) - 1 - (s.core.read .rax).toNat)) 14 245 s := by
  obtain ⟨hF, k, hk, hrsi, hrcx, j, hj, hrax, hrdx, hpre⟩ := hinv
  have hb := hE.bytes k hk j hj (fun i hi => by rw [hpre i hi]; exact pat_ne (by omega))
  have hp := hE.pats j hj
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp
  have hw := hE.words (k + 1) (by omega)
  rw [← words_succ k] at hw
  rw [hF.mem] at hl
  sv [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, execNew_cmp_mem, loopCuts, loopStops, inv200, inv245, kOf, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl,
    hF.rsp, hF.r11, hF.r14, hF.r15, hF.rbx, hF.mem, hrsi, hrcx, hrax, hrdx, hb, hp, hw]
  have hsm := hE.small
  have ht1 : (24 + 8 * k) % 18446744073709551616 = 24 + 8 * k := Nat.mod_eq_of_lt (by omega)
  have ht2 : (BitVec.ofNat 64 (24 + 8 * (k + 1))).toNat = 24 + 8 * (k + 1) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ht3 : j % 18446744073709551616 = j := Nat.mod_eq_of_lt (by omega)
  have hj1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by rw [BitVec.ofNat_add_ofNat]
  have ht4 : (BitVec.ofNat 64 (j + 1)).toNat = j + 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [words_succ k, ht1, ht2, ht3, hj1, ht4]
  repeat' (first | (intro _) | (apply And.intro))
  all_goals first
    | fr hF
    | omega
    | exact ⟨k + 1, next_lt hE (by omega) (by assumption), rfl, rfl⟩
    | exact ⟨k, hk, rfl, rfl, j + 1, j16 hj (by assumption), rfl, rfl, pre_succ hpre (by assumption)⟩

theorem vc_loop (e : Env) (hE : EnvFacts e) :
    vc Isa.sys8 code listing (loopCuts e) (loopStops e) [] [] base 182 (Frame e) 14 := by
  refine ⟨fun s hlv hl hrip hF => vc_entry e hE s hlv hl hrip hF, ?_⟩
  intro oc hoc s hlv hl hrip hinv
  simp only [loopCuts, List.mem_cons, List.mem_nil_iff, or_false] at hoc
  rcases hoc with rfl | rfl
  · exact vc_200 e hE s hlv hl hrip hinv
  · exact vc_245 e hE s hlv hl hrip hinv

/-- **VERIFIED. The environment scan.** From `0x4034a6` with the frame registers, retiring
steps reach `0x4034f7` with the frame registers and the memory unchanged. -/
theorem loop_runs (e : Env) (hE : EnvFacts e) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 182)
    (hF : Frame e s) :
    ∃ t, Reaches Isa.sys8.step s t ∧ Frame e t ∧ t.core.rip = base + BitVec.ofNat 64 263 ∧
      Loaded t.memory base code ∧ t.faulted = false :=
  sound_one listing_valid (vc_loop e hE) s hlv hl hrip hF

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
