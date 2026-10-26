module

public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainBase

/-! # `cmain` from the end of the environment scan to `digest_file`'s entry

Four chunks of straight-line code (no loop), each a `SegVC` segment with one stop:

* A, `0x4034f7` to `0x403572`: `optind = 1`, no option (`argc = 1`), no operand;
* B, `0x403572` to `0x403955`: the option-consistency checks on the image's globals;
* C, `0x403955` to `0x40418f`: `binary = 0`, the default operand `"-"` into `argv[0]`'s slot,
  `cmain`'s locals, `do_check = 0` (`je 0x40418f`);
* D, `0x40418f` to `0x402de0`: `mov %r14,%rdx; lea 0x70(%rsp),%rsi; mov %r12,%rdi; call`.

C is run as C1 (the stores, to `0x403992`), C2 (the reloads, to `0x4039b5`) and C3
(`test %ebx,%ebx; je 0x40418f`): short chunks keep the symbolic states small (one long chunk
exhausts memory, and the kernel check of the full C overflows its stack).

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
open Silmaril.Machine.Execution (Reaches)

/-- What the launch memory gives the tail: the stack room and `.data`'s `binary` writable,
the globals `cmain` reads, `.text` and `.rodata` read-only. -/
structure G0 (sp0 : Word) (m0 : Memory) : Prop where
  lo : 0x423150 ≤ sp0.toNat
  hi : sp0.toNat + 16 < 18446744073709551616
  pw : m0.Permitted .write (sp0.toNat - 0x10000) (0x10000 + 16)
  pr : m0.Permitted .read (sp0.toNat - 0x10000) (0x10000 + 16)
  gw : m0.Permitted .write 0x409010 4
  gr : m0.Permitted .read 0x409010 4
  g1 : loadN m0 0x409020#64 4 = some 0#64
  g2 : loadN m0 0x409014#64 1 = some 0x0a#64
  g3 : loadN m0 0x409010#64 4 = some 0xffffffff#64
  g4 : loadN m0 0x40a0a4#64 4 = some 0#64
  g5 : loadN m0 0x40a0b4#64 4 = some 0#64
  g6 : loadN m0 0x40a0b0#64 4 = some 0#64
  g7 : loadN m0 0x40a0ac#64 4 = some 0#64
  g8 : loadN m0 0x40a0a8#64 4 = some 0#64
  g9 : loadN m0 0x409024#64 4 = some 0#64
  ro : Ro m0

/-- A footprint fact kept opaque to `cm_split` (which would split `WritesWithin`). -/
structure WW (m0 m : Memory) (W : Nat → Prop) : Prop where
  ww : Unit → Memory.WritesWithin m0 m W

theorem call_ret : Call.base + 16#64 = 0x40419f#64 := rfl

theorem ofNat_toNat_modl (x : Word) : BitVec.ofNat 64 (x.toNat % 18446744073709551616) = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]
theorem zero_shl3 : (0#64 <<< 3) = 0#64 := by decide

theorem msb_ff : (4294967295#32).msb = true := by decide
theorem shl_one3 : (1#64 <<< 3) = 8#64 := by decide
theorem add16_comm (x : Word) : 16#64 + x = x + 16#64 := BitVec.add_comm _ _
theorem ult_self' (x : Word) : x.ult x = false := by simp [BitVec.ult]

theorem ro_ww {m0 m : Memory} {W : Nat → Prop} (h : Memory.WritesWithin m0 m W) (hr : Ro m0) :
    Ro m := fun a lo hi => by rw [h.permits]; exact hr a lo hi

/-- A global outside `W1` reads as at launch. -/
theorem g_ww {sp0 : Word} {m0 m : Memory} (h : Memory.WritesWithin m0 m (W1 sp0))
    (lo : 0x423150 ≤ sp0.toNat) {a : Word} {k : Nat} (ha : a.toNat + k ≤ 0x412118) :
    loadN m a k = loadN m0 a k :=
  loadN_ww h (fun i hi hw => by simp only [W1] at hw; omega)

def postA (sp0 : Word) (m0 : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 240#64 ∧ s.core.read .r11 = sp0 ∧ s.core.read .rax = 0#64 ∧
    WW m0 s.memory (fun a =>
      (sp0.toNat - 0x10000 ≤ a ∧ a < sp0.toNat) ∨ (0x412118 ≤ a ∧ a < 0x412128))

def postB (sp0 : Word) (m : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 240#64 ∧ s.core.read .r11 = sp0 ∧ s.core.read .rax = 0#64 ∧
    s.core.read .rdx = 0xffffffff#64 ∧ s.memory = m

def postC (sp0 : Word) (m0 : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 240#64 ∧ s.core.read .r14 = sp0 - 240#64 + 144#64 ∧
    s.core.read .r12 = 0x406052#64 ∧ s.core.read .rbx = 0#64 ∧
    WW m0 s.memory (fun a =>
      ((sp0.toNat - 0x10000 ≤ a ∧ a < sp0.toNat) ∨ (0x412118 ≤ a ∧ a < 0x412128)) ∨
        (0x409010 ≤ a ∧ a < 0x409014) ∨ (sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 16)) ∧
    loadN s.memory (sp0 - 240#64 + 44#64) 4 = some 1#64 ∧
    loadN s.memory (sp0 - 240#64 + 8#64) 8 = some 0#64 ∧
    loadN s.memory (sp0 - 240#64 + 80#64) 4 = some 1#64 ∧
    loadN s.memory (Main.base + 23584#64) 4 = some 0#64

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_A (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 263)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hr14 : s.core.read .r14 = 1#64) (hr15 : s.core.read .r15 = sp0 + 8#64)
    (hrbx : s.core.read .rbx = 16#64) (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    wpN Isa.sys8 Main.code Main.listing [] [(386, postA sp0 m0)] [] [] Main.base none 20 263 s := by
  have hro := ro_ww hww hG.ro
  have hpw := (hww.permitted_iff _ _ _).mpr hG.pw
  have hpr := (hww.permitted_iff _ _ _).mpr hG.pr
  have hlo := hG.lo
  have hhi := hG.hi
  unfold W1 at hww
  cm_go [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, postA, ofNat_toNat_mod8, call_ret, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr11, hr14, hr15, hrbx, BitVec.reduceSLE,
    BitVec.reduceSLT]
  all_goals (try (refine ⟨fun _ => ?_⟩; cm_mem))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_B (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 386)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hrax : s.core.read .rax = 0#64) (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    wpN Isa.sys8 Main.code Main.listing [] [(1381, postB sp0 s.memory)] [] [] Main.base none 20 386 s := by
  have g1 : loadN s.memory (Main.base + 23600#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g1
  have g2 : loadN s.memory (Main.base + 23588#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g2
  have g3 : loadN s.memory (Main.base + 23584#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g3
  have g4 : loadN s.memory (Main.base + 27828#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g4
  have g5 : loadN s.memory (Main.base + 27844#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g5
  have g6 : loadN s.memory (Main.base + 27840#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g6
  have g7 : loadN s.memory (Main.base + 27836#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g7
  have g8 : loadN s.memory (Main.base + 27832#64) _ = _ := (g_ww hww hG.lo (by decide)).trans hG.g8
  sv [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, postB, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr11, hrax, g1, g2, g3, g4, g5, g6, g7, g8,
    BitVec.reduceSLE, BitVec.reduceSLT]

/-- The stop of chunk C1 (`0x403992`): the stores done. -/
def postC1 (sp0 : Word) (m0 : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 240#64 ∧ s.core.read .r14 = sp0 - 240#64 + 144#64 ∧
    WW m0 s.memory (fun a =>
      ((sp0.toNat - 0x10000 ≤ a ∧ a < sp0.toNat) ∨ (0x412118 ≤ a ∧ a < 0x412128)) ∨
        (0x409010 ≤ a ∧ a < 0x409014) ∨ (sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 16)) ∧
    loadN s.memory (sp0 - 240#64 + 44#64) 4 = some 1#64 ∧
    loadN s.memory (sp0 - 240#64 + 8#64) 8 = some 0#64 ∧
    loadN s.memory (sp0 - 240#64 + 8#64) 4 = some 0#64 ∧
    loadN s.memory (sp0 - 240#64 + 80#64) 4 = some 1#64 ∧
    loadN s.memory (sp0 - 240#64 + 56#64) 8 = some sp0 ∧
    loadN s.memory (sp0 + 8#64) 8 = some 0x406052#64 ∧
    loadN s.memory (Main.base + 23584#64) 4 = some 0#64

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_C1 (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 1381)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hrax : s.core.read .rax = 0#64) (hrdx : s.core.read .rdx = 0xffffffff#64)
    (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    wpN Isa.sys8 Main.code Main.listing [] [(1442, postC1 sp0 m0)] [] [] Main.base none 20 1381 s := by
  have hro := ro_ww hww hG.ro
  have hpw := (hww.permitted_iff _ _ _).mpr hG.pw
  have hpr := (hww.permitted_iff _ _ _).mpr hG.pr
  have hgw : s.memory.Permitted .write (Main.base + 23584#64).toNat 4 :=
    (hww.permitted_iff _ _ _).mpr hG.gw
  have hgr : s.memory.Permitted .read (Main.base + 23584#64).toNat 4 :=
    (hww.permitted_iff _ _ _).mpr hG.gr
  have hb0 : Main.base.toNat = 4207600 := rfl
  have hlo := hG.lo
  have hhi := hG.hi
  have hww2 : Memory.WritesWithin m0 s.memory (W2 sp0) := hww.mono fun a h => Or.inl h
  unfold W2 W1 at hww2
  cm_go [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, postC1, ofNat_toNat_mod8, call_ret, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr11, hrax, hrdx, BitVec.reduceSLE,
    BitVec.reduceSLT]
  all_goals (try (refine ⟨fun _ => ?_⟩; cm_mem))
  all_goals (try rfl)
  all_goals (try (simp only [ofNat_toNat_mod8]))

/-- The stop of chunk C2 (`0x4039b5`): `do_check` in `rbx`, the operand in `r12`. -/
def postC2 (sp0 : Word) (m : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 240#64 ∧ s.core.read .r14 = sp0 - 240#64 + 144#64 ∧
    s.core.read .r12 = 0x406052#64 ∧ s.core.read .rbx = 0#64 ∧ s.memory = m

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_C2 (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 1442)
    (hC : postC1 sp0 m0 s) :
    wpN Isa.sys8 Main.code Main.listing [] [(1477, postC2 sp0 s.memory)] [] [] Main.base none 20 1442 s := by
  obtain ⟨hrsp, hr14, ⟨hww'⟩, L1, L2, L2', L3, L4, L5, L6⟩ := hC
  have hww := hww' ()
  have g9 : loadN s.memory (Main.base + 23604#64) 4 = some 0#64 := by
    rw [loadN_ww hww (fun i hi hw => by
      have hb : (Main.base + 23604#64).toNat = 0x409024 := rfl
      rw [hb] at hw; have := hG.lo; omega)]
    exact hG.g9
  sv [main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, postC2, ofNat_toNat_mod8, call_ret, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr14, g9, BitVec.reduceSLE,
    BitVec.reduceSLT, L1, L2, L2', L3, L4, L5, L6]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_C3 (sp0 : Word) (m0 : Memory) (s : XState)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 1477)
    (hC : postC1 sp0 m0 s) (hrsp : s.core.read .rsp = sp0 - 240#64)
    (hr14 : s.core.read .r14 = sp0 - 240#64 + 144#64) (hr12 : s.core.read .r12 = 0x406052#64)
    (hrbx : s.core.read .rbx = 0#64) :
    wpN Isa.sys8 Main.code Main.listing [] [(3487, postC sp0 m0)] [] [] Main.base none 4 1477 s := by
  obtain ⟨-, -, hww, L1, L2, -, L3, -, -, L6⟩ := hC
  sv [hrsp, hr14, hr12, main_lk_0, main_lk_2, main_lk_4, main_lk_6, main_lk_8, main_lk_9, main_lk_10, main_lk_17, main_lk_20, main_lk_22, main_lk_28, main_lk_31, main_lk_35, main_lk_38, main_lk_44, main_lk_47, main_lk_50, main_lk_52, main_lk_54, main_lk_57, main_lk_59, main_lk_64, main_lk_67, main_lk_69, main_lk_72, main_lk_76, main_lk_80, main_lk_82, main_lk_84, main_lk_87, main_lk_89, main_lk_93, main_lk_96, main_lk_99, main_lk_103, main_lk_105, main_lk_107, main_lk_112, main_lk_114, main_lk_120, main_lk_124, main_lk_128, main_lk_134, main_lk_139, main_lk_145, main_lk_147, main_lk_150, main_lk_153, main_lk_157, main_lk_160, main_lk_167, main_lk_175, main_lk_182, main_lk_186, main_lk_189, main_lk_192, main_lk_194, main_lk_200, main_lk_205, main_lk_207, main_lk_216, main_lk_218, main_lk_224, main_lk_228, main_lk_232, main_lk_238, main_lk_245, main_lk_248, main_lk_250, main_lk_254, main_lk_258, main_lk_261, main_lk_263, main_lk_265, main_lk_270, main_lk_276, main_lk_279, main_lk_282, main_lk_285, main_lk_288, main_lk_313, main_lk_316, main_lk_319, main_lk_324, main_lk_327, main_lk_330, main_lk_334, main_lk_337, main_lk_386, main_lk_393, main_lk_399, main_lk_406, main_lk_544, main_lk_548, main_lk_552, main_lk_558, main_lk_561, main_lk_567, main_lk_745, main_lk_747, main_lk_752, main_lk_756, main_lk_760, main_lk_762, main_lk_767, main_lk_773, main_lk_779, main_lk_781, main_lk_783, main_lk_787, main_lk_792, main_lk_798, main_lk_800, main_lk_806, main_lk_813, main_lk_834, main_lk_841, main_lk_856, main_lk_863, main_lk_895, main_lk_902, main_lk_1239, main_lk_1246, main_lk_1381, main_lk_1383, main_lk_1385, main_lk_1387, main_lk_1393, main_lk_1395, main_lk_1397, main_lk_1405, main_lk_1410, main_lk_1412, main_lk_1420, main_lk_1428, main_lk_1433, main_lk_1437, main_lk_1442, main_lk_1446, main_lk_1450, main_lk_1456, main_lk_1461, main_lk_1466, main_lk_1472, main_lk_1477, main_lk_1479, postC, ofNat_toNat_mod8, call_ret, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr14, BitVec.reduceSLE,
    BitVec.reduceSLT, hrbx, L1, L2, L3, L6]
  all_goals (try (exact hww))

/-- The stop of chunk D, in `loadN` form. -/
def postD (sp0 : Word) (m0 : Memory) (s : XState) : Prop :=
  s.core.read .rsp = sp0 - 248#64 ∧ loadN s.memory (sp0 - 248#64) 8 = some 0x40419f#64 ∧
    s.core.read .rdi = 0x406052#64 ∧ s.core.read .rsi = sp0 - 240#64 + 112#64 ∧
    s.core.read .rdx = sp0 - 240#64 + 144#64 ∧
    s.core.read .r12 = 0x406052#64 ∧ s.core.read .rbx = 0#64 ∧
    s.core.read .r14 = sp0 - 240#64 + 144#64 ∧
    WW m0 s.memory (fun a =>
      ((sp0.toNat - 0x10000 ≤ a ∧ a < sp0.toNat) ∨ (0x412118 ≤ a ∧ a < 0x412128)) ∨
        (0x409010 ≤ a ∧ a < 0x409014) ∨ (sp0.toNat + 8 ≤ a ∧ a < sp0.toNat + 16)) ∧
    loadN s.memory (sp0 - 240#64 + 44#64) 4 = some 1#64 ∧
    loadN s.memory (sp0 - 240#64 + 8#64) 8 = some 0#64 ∧
    loadN s.memory (sp0 - 240#64 + 80#64) 4 = some 1#64 ∧
    loadN s.memory (Main.base + 23584#64) 4 = some 0#64

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem vc_D (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState)
    (hl : Loaded s.memory Call.base Call.code) (hrip : s.core.rip = Call.base + BitVec.ofNat 64 0)
    (hC : postC sp0 m0 s) :
    wpN Isa.sys8 Call.code Call.listing [] [(18446744073709546577, postD sp0 m0)] [] [] Call.base
      none 6 0 s := by
  obtain ⟨hrsp, hr14, hr12, hrbx, ⟨hww'⟩, l1, l2, l3, l4⟩ := hC
  have hww := hww' ()
  have hb0 : Main.base.toNat = 4207600 := rfl
  have hro := ro_ww hww hG.ro
  have hpw := (hww.permitted_iff _ _ _).mpr hG.pw
  have hpr := (hww.permitted_iff _ _ _).mpr hG.pr
  have hlo := hG.lo
  have hhi := hG.hi
  cm_go [call_lk_0, call_lk_3, call_lk_8, call_lk_11, postD, ofNat_toNat_mod8, call_ret, Mem.ofReg, Nat.reduceMul, Mem.ofRip, Silmaril.X86.Ext.Base.value, false_implies, Bool.not_true, Bool.not_false, msb_ff, shl_one3, zero_shl3, ofNat_toNat_modl, add16_comm, ult_self',
    Silmaril.X86.Lift.ix, hrip, hl, hrsp, hr14, hr12, hrbx, l1, l2, l3, l4]
  all_goals (try (seg_read [hrsp, hr14, hr12, hrbx, Silmaril.Apps.Sha256sum.Binary.Startup.sub_sub_lit]))
  all_goals (try (with_reducible assumption))
  all_goals (try (refine ⟨fun _ => ?_⟩; exact Silmaril.Apps.Sha256sum.Binary.Startup.ww_wb (by assumption) hww (fun i hi => by simp only [Silmaril.X86.length_encodeWords_singleton] at hi; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)))

/-! ## The chunks as runs -/

set_option maxRecDepth 100000 in
/-- **VERIFIED. Chunk A.** -/
theorem A_runs (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 263)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hr14 : s.core.read .r14 = 1#64) (hr15 : s.core.read .r15 = sp0 + 8#64)
    (hrbx : s.core.read .rbx = 16#64) (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    ∃ t, Reaches Isa.sys8.step s t ∧ postA sp0 m0 t ∧
      t.core.rip = Main.base + BitVec.ofNat 64 386 ∧ Loaded t.memory Main.base Main.code ∧
      t.faulted = false :=
  sound_one (I := Isa.sys8) (pre := fun t => t = s) Main.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_A sp0 m0 hG t hl hr hrsp hr11 hr14 hr15 hrbx hww,
     fun oc hoc => by simp at hoc⟩ s hlv hl hrip rfl

set_option maxRecDepth 100000 in
/-- **VERIFIED. Chunk B.** -/
theorem B_runs (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 386)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hrax : s.core.read .rax = 0#64) (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    ∃ t, Reaches Isa.sys8.step s t ∧ postB sp0 s.memory t ∧
      t.core.rip = Main.base + BitVec.ofNat 64 1381 ∧ Loaded t.memory Main.base Main.code ∧
      t.faulted = false :=
  sound_one (I := Isa.sys8) (pre := fun t => t = s) Main.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_B sp0 m0 hG t hl hr hrsp hr11 hrax hww,
     fun oc hoc => by simp at hoc⟩ s hlv hl hrip rfl

set_option maxRecDepth 100000 in
/-- **VERIFIED. Chunk C** (C1: the stores; C2: the loads and `je 0x40418f`). -/
theorem C_runs (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory Main.base Main.code) (hrip : s.core.rip = Main.base + BitVec.ofNat 64 1381)
    (hrsp : s.core.read .rsp = sp0 - 240#64) (hr11 : s.core.read .r11 = sp0)
    (hrax : s.core.read .rax = 0#64) (hrdx : s.core.read .rdx = 0xffffffff#64)
    (hww : Memory.WritesWithin m0 s.memory (W1 sp0)) :
    ∃ t, Reaches Isa.sys8.step s t ∧ postC sp0 m0 t ∧
      t.core.rip = Main.base + BitVec.ofNat 64 3487 ∧ Loaded t.memory Main.base Main.code ∧
      t.faulted = false := by
  obtain ⟨u, r1, hu, hripu, hlu, hlvu⟩ := sound_one (I := Isa.sys8) (pre := fun t => t = s)
    Main.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_C1 sp0 m0 hG t hl hr hrsp hr11 hrax hrdx hww,
     fun oc hoc => by simp at hoc⟩ s hlv hl hrip rfl
  obtain ⟨v, r2, ⟨v1, v2, v3, v4, v5⟩, hripv, hlv', hlvv⟩ := sound_one (I := Isa.sys8)
    (pre := fun t => t = u) Main.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_C2 sp0 m0 hG t hl hr hu,
     fun oc hoc => by simp at hoc⟩ u hlvu hlu hripu rfl
  have hv : postC1 sp0 m0 v := by
    obtain ⟨a1, a2, a3, a4⟩ := hu
    unfold postC1; rw [v5]; exact ⟨v1, v2, a3, a4⟩
  obtain ⟨t, r3, ht, hript, hlt, hlvt⟩ := sound_one (I := Isa.sys8) (pre := fun t => t = v)
    Main.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_C3 sp0 m0 t hl hr hv v1 v2 v3 v4,
     fun oc hoc => by simp at hoc⟩ v hlvv hlv' hripv rfl
  exact ⟨t, (r1.trans r2).trans r3, ht, hript, hlt, hlvt⟩

set_option maxRecDepth 100000 in
/-- **VERIFIED. Chunk D** (the call). -/
theorem D_runs (sp0 : Word) (m0 : Memory) (hG : G0 sp0 m0) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory Call.base Call.code) (hrip : s.core.rip = Call.base + BitVec.ofNat 64 0)
    (hC : postC sp0 m0 s) :
    ∃ t, Reaches Isa.sys8.step s t ∧ postD sp0 m0 t ∧
      t.core.rip = Call.base + BitVec.ofNat 64 18446744073709546577 ∧
      Loaded t.memory Call.base Call.code ∧ t.faulted = false :=
  sound_one (I := Isa.sys8) (pre := fun t => t = s) Call.listing_valid
    ⟨fun t _ hl hr he => by
      subst he; exact vc_D sp0 m0 hG t hl hr hC,
     fun oc hoc => by simp at hoc⟩ s hlv hl hrip rfl

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
