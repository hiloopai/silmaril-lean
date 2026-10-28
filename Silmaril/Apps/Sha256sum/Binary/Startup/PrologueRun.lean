module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

/-! # The prologue of `digest_file` reaches the read loop's head

From `Startup.AtDigestEntry` (with the launch facts) the prologue (`Prologue.vc_entry`) runs by
retiring steps of the `Ext8` machine to `0x402ef0`. There the read loop's cut point holds:

* `prologue_reaches` (VERIFIED): the run, and the postcondition `Prologue.post`;
* `atHead_of_post` (VERIFIED): `Digest.AtHead (loopOf c t) [] t` for the loop context
  `loopOf c t` (`digest_file`'s `rsp = sp0 - 448`, `rbp = r13 = 0`, descriptor `0`, entry memory
  the memory at the head). The struct holds nothing yet (`absorbed_nil`: the SHA-256 initial
  value, `blen = total = 0`). The read loop's code region is loaded.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys

/-! ## Memory facts -/

theorem readBytes_of_loadN {m : Memory} {a v : Word} {k : Nat} (hk : k ≤ 8)
    (h : loadN m a k = some v) : m.readBytes a.toNat k = some (leBytes v k) := by
  unfold loadN at h
  cases hr : m.readBytes a.toNat k with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hl : bs.length = k := Memory.readWith_length hr
    subst h
    have := leBytes_leValue bs (by omega)
    rw [hl] at this
    rw [this]

theorem readBytes_of_loadN8 {m : Memory} {a v : Word} (h : loadN m a 8 = some v) :
    m.readBytes a.toNat 8 = some (leBytes v 8) := readBytes_of_loadN (le_refl _) h

theorem iv_bytes : Silmaril.Crypto.X86.Sha256O2.stateOf
    (leBytes 0xbb67ae856a09e667#64 8 ++ leBytes 0xa54ff53a3c6ef372#64 8 ++
      leBytes 0x9b05688c510e527f#64 8 ++ leBytes 0x5be0cd191f83d9ab#64 8) = Digest.IV := by
  decide

theorem toNat_add_lit {x : Word} (h : x.toNat + 0x1000 < 2 ^ 64) {n : Nat} (hn : n ≤ 0x1000) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The four quadwords of `sha_init` are the SHA-256 initial value. -/
theorem stateHolds_iv {m : Memory} {sp : Word} (hi : sp.toNat + 0x1000 < 2 ^ 64)
    (h0 : loadN m (sp + 0x20#64) 8 = some 0xbb67ae856a09e667#64)
    (h1 : loadN m (sp + 0x28#64) 8 = some 0xa54ff53a3c6ef372#64)
    (h2 : loadN m (sp + 0x30#64) 8 = some 0x9b05688c510e527f#64)
    (h3 : loadN m (sp + 0x38#64) 8 = some 0x5be0cd191f83d9ab#64) :
    Silmaril.Crypto.X86.Sha256O2.StateHolds m (sp + 0x20#64) Digest.IV := by
  have r0 := readBytes_of_loadN8 h0
  have r1 := readBytes_of_loadN8 h1
  have r2 := readBytes_of_loadN8 h2
  have r3 := readBytes_of_loadN8 h3
  rw [toNat_add_lit (n := 0x20) hi (by decide)] at r0
  rw [toNat_add_lit (n := 0x28) hi (by decide)] at r1
  rw [toNat_add_lit (n := 0x30) hi (by decide)] at r2
  rw [toNat_add_lit (n := 0x38) hi (by decide)] at r3
  have r01 := Memory.readBytes_append r0 (by rw [show sp.toNat + 0x20 + 8 = sp.toNat + 0x28 by omega]; exact r1)
  have r012 := Memory.readBytes_append r01 (by rw [show sp.toNat + 0x20 + (8 + 8) = sp.toNat + 0x30 by omega]; exact r2)
  have r0123 := Memory.readBytes_append r012 (by rw [show sp.toNat + 0x20 + (8 + 8 + 8) = sp.toNat + 0x38 by omega]; exact r3)
  refine ⟨_, ?_, iv_bytes⟩
  rw [toNat_add_lit (n := 0x20) hi (by decide)]
  exact r0123

theorem loaded_ww {m0 m : Memory} {W : Nat → Prop} (hw : Memory.WritesWithin m0 m W) {b : Word}
    {code : List Byte} (hl : Loaded m0 b code) (hout : ∀ o < code.length, ¬ W (b.toNat + o)) :
    Loaded m b code := by
  unfold Loaded at hl ⊢; rw [hw.fetchBytes hout]; exact hl

theorem ro_ww {m0 m : Memory} {W : Nat → Prop} (hw : Memory.WritesWithin m0 m W) (h : Ro m0) :
    Ro m := by
  intro a h1 h2; rw [hw.permits]; exact h a h1 h2

/-! ## The run -/

/-- The entry facts `vc_entry` needs, from the launch facts and the entry cut. -/
structure EntryOk (c : Ctx) (s : XState) : Prop where
  launch : LaunchFacts c
  entry : AtDigestEntry c s

theorem rodata_2d {m0 m : Memory} (hm : Image.image.Mapped m0) {W : Nat → Prop}
    (hww : Memory.WritesWithin m0 m W) (hout : ¬ W 0x406052) :
    loadN m 0x406052#64 1 = some 0x2d#64 := by
  have := rodata_load hm hww 0x52 (by decide) hout
  rw [this]; decide +kernel

theorem rodata_00 {m0 m : Memory} (hm : Image.image.Mapped m0) {W : Nat → Prop}
    (hww : Memory.WritesWithin m0 m W) (hout : ¬ W 0x406053) :
    loadN m 0x406053#64 1 = some 0#64 := by
  have := rodata_load hm hww 0x53 (by decide) hout
  rw [this]; decide +kernel

set_option maxRecDepth 200000 in
/-- **VERIFIED. The prologue runs.** From `digest_file`'s entry on the stdin path, by retiring
steps of the `Ext8` machine, to `0x402ef0` with `post`. -/
theorem prologue_reaches {c : Ctx} {s : XState} (lf : LaunchFacts c) (en : AtDigestEntry c s) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep8 s t ∧ t.faulted = false ∧
      t.core.rip = 0x402ef0#64 ∧ post c s t := by
  have hlo := lf.spLo
  have hhi := lf.spHi
  have hww := en.mem
  have hl : Loaded s.memory Digest.base Digest.code :=
    loaded_ww hww (Digest.loaded lf.mapped) (fun o ho hin => by
      simp only [Digest.code_length] at ho
      simp only [W2, W1, Digest.base_toNat] at hin; omega)
  have hrip : s.core.rip = Digest.base + BitVec.ofNat 64 0 := by rw [en.rip]; rfl
  have hpw : s.memory.Permitted .write (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (lf.rw .write (by decide))
  have hpr : s.memory.Permitted .read (c.sp0.toNat - 0x10000) (0x10000 + 16) :=
    (hww.permitted_iff _ _ _).mpr (lf.rw .read (by decide))
  have hgw : s.memory.Permitted .write 0x40a0a0 4 :=
    (hww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (data_perm lf.mapped .write (by decide))
      (by decide) (by decide) (by decide))
  have hgr : s.memory.Permitted .read 0x40a0a0 4 :=
    (hww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (data_perm lf.mapped .read (by decide))
      (by decide) (by decide) (by decide))
  have g0 := rodata_2d lf.mapped hww (by simp only [W2, W1]; omega)
  have g1 := rodata_00 lf.mapped hww (by simp only [W2, W1]; omega)
  have hvc : vc Isa.sys8 Digest.code Digest.listing [] (stops c s) [] [] Digest.base 0
      (fun s' => s' = s) 60 :=
    ⟨fun s' hlv' hl' hrip' hs' => by
      subst hs'
      exact vc_entry c s' hlv' hl' hrip' en.rsp en.rdi en.rdx en.ret (ro_ww hww lf.ro) hlo
        (by omega) hpw hpr hgw hgr g0 g1,
     fun oc hoc => by simp at hoc⟩
  obtain ⟨t, hr, hq, hrip', _, hlv'⟩ :=
    sound_one (I := Isa.sys8) Digest.listing_valid hvc s en.faulted hl hrip rfl
  exact ⟨t, reaches_sys8 hr, hlv', by rw [hrip']; rfl, hq⟩

/-! ## The read loop's cut point -/

/-- The read loop's context after the prologue: `digest_file`'s `rsp = sp0 - 448`,
`rbp = r13 = 0` (the comparison with `"-"` ran to the NUL), descriptor `0` (standard input),
and the memory at the head as the loop's entry memory. -/
def loopOf (c : Ctx) (t : XState) : Binary.Digest.Loop := ⟨c.sp0 - 448#64, 0#64, 0#64, 0#64, t.memory⟩

/-- The footprint since the launch: the startup's `W2` and the prologue's `PW`. -/
def WP (sp0 : Word) (a : Nat) : Prop := W2 sp0 a ∨ PW sp0 a

theorem ww_launch {c : Ctx} {s t : XState} (en : AtDigestEntry c s) (hp : post c s t) :
    Memory.WritesWithin c.m0 t.memory (WP c.sp0) :=
  (en.mem.mono fun _ h => .inl h).trans (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.ww.mono
    fun _ h => .inr h)

theorem e448 {c : Ctx} (lf : LaunchFacts c) : (c.sp0 - 448#64).toNat = c.sp0.toNat - 448 :=
  Binary.Digest.toNat_sp_sub (by have := lf.spLo; omega) (by decide)

set_option maxRecDepth 200000 in
/-- **VERIFIED. The read loop's head after the prologue**: `Digest.AtHead (loopOf c t) [] t`
(nothing absorbed: `sha_init`'s state), and the read loop's code region loaded. -/
theorem atHead_of_post {c : Ctx} {s t : XState} (lf : LaunchFacts c) (en : AtDigestEntry c s)
    (hp : post c s t) (hrip : t.core.rip = 0x402ef0#64) :
    Binary.Digest.AtHead (loopOf c t) [] t ∧
      Loaded t.memory Binary.Digest.base Binary.Digest.code := by
  have ww := ww_launch en hp
  have hlo := lf.spLo
  have hhi := lf.spHi
  have hal := lf.aligned
  have e : (loopOf c t).sp.toNat = c.sp0.toNat - 448 := e448 lf
  obtain ⟨hsp, hbx, hbp, h13, hfd, -, q0, q1, q2, q3, hbl, htot, -⟩ := hp
  have hi : (c.sp0 - 448#64).toNat + 0x1000 < 2 ^ 64 := by rw [e448 lf]; omega
  have out : ∀ (b n : Nat), b + n ≤ 0x409010 → ∀ o < n, ¬ WP c.sp0 (b + o) := by
    intro b n hb o ho hin
    simp only [WP, W2, W1, PW] at hin; omega
  refine ⟨⟨by rw [hrip]; rfl, ⟨hsp, hbx, hbp, h13, by rw [e]; omega, by rw [e]; omega,
    by rw [e]; omega, ?_, ?_, ?_, ?_, hfd, ?_, ?_, ?_, .refl _ _⟩, ?_⟩, ?_⟩
  · rw [e]
    exact (ww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (lf.rw .write (by decide))
      (by decide) (by omega) (by omega))
  · rw [e]
    exact (ww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (lf.rw .read (by decide))
      (by decide) (by omega) (by omega))
  · rw [ww.fetchBytes]
    · exact loaded_code lf.mapped
    · exact out _ _ (by decide)
  · rw [ww.readBytes]
    · exact loaded_kTable lf.mapped
    · exact out _ _ (by decide)
  · rw [Binary.Digest.iobuf_toNat]
    exact (ww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (data_perm lf.mapped .write
      (by decide)) (by decide) (by decide) (by decide))
  · rw [Binary.Digest.iobuf_toNat]
    exact (ww.permitted_iff _ _ _).mpr (Memory.Permitted.sub (data_perm lf.mapped .read
      (by decide)) (by decide) (by decide) (by decide))
  · exact loaded_ww ww (Sc3.loaded lf.mapped) (out _ _ (by decide))
  · exact Binary.Digest.absorbed_nil (stateHolds_iv hi q0 q1 q2 q3) hbl htot (BitVec.isLt _)
  · exact loaded_ww ww (Binary.Digest.loaded lf.mapped) (out _ _ (by decide))

end Silmaril.Apps.Sha256sum.Binary.Startup.Prologue
