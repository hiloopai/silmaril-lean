module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameSlash
public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameLt
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Startup

/-! # `set_program_name` (`sha256sum-min`): the `/` case composed

`slashCase_of` composes the entry VC `vc_slash_entry` with the loop-cut VCs of the
`"/.libs/"` loop (cut `134`) and the `"lt-"` loop (cut `762`), taken as hypotheses in the
exact shape of `vc_libs` and `vc_lt`, by `SegVC.sound_one` (stop: the join `150`,
`0x403486`, with `common`). `setProgNameSeg'` is the resulting `set_program_name` segment.

Status: VERIFIED from the two loop-cut VCs (hypotheses); no `sorry`, no new axiom.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup
open Silmaril.Machine.Execution (Reaches)

set_option maxRecDepth 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option linter.constructorNameAsVariable false in
/-- A `vc_lt` stated with the bare `wpN` conclusion gives `LtGoal`. -/
theorem ltGoal_of {c : Ctx} {s : XState}
    (h : wpN Isa.sys8 Main.code postListing (slashCuts c) [(150, common c)] [] [] Main.base
      (some (ltMeasure s)) 20 762 s) : LtGoal c s := by
  unfold LtGoal; assumption

/-- The statement of `vc_libs`. -/
def VcLibs : Prop :=
  ∀ c, LaunchFacts c → ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
    s.core.rip = Main.base + BitVec.ofNat 64 134 → libsInv c s → LibsGoal c s

/-- The statement of `vc_lt`. -/
def VcLt : Prop :=
  ∀ c, LaunchFacts c → ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
    s.core.rip = Main.base + BitVec.ofNat 64 762 → ltInv c s → LtGoal c s

/-- **VERIFIED from `vc_libs`, `vc_lt`. The `/` case**: from the scan exit with a last `/`,
retiring steps reach the join `0x403486` with `common`. -/
theorem slashCase_of (hlibs : VcLibs) (hlt : VcLt) : ∀ c, LaunchFacts c → SlashCase c := by
  intro c hc s hlv hrip hscan h0
  have hvc : vc Isa.sys8 Main.code postListing (slashCuts c) [(150, common c)] [] [] Main.base 84
      (slashPre c) 20 := by
    refine ⟨vc_slash_entry c hc, ?_⟩
    intro oc hoc
    simp only [slashCuts, List.mem_cons, List.mem_nil_iff, or_false] at hoc
    rcases hoc with rfl | rfl
    · intro s hlv hl hrip hinv
      have h := hlibs c hc s hlv hl hrip hinv
      unfold LibsGoal at h
      -- `assumption`, not `exact h`: elaborating `h` would `whnf` (run) the `wpN` type
      dsimp only
      assumption
    · intro s hlv hl hrip hinv
      have h := hlt c hc s hlv hl hrip hinv
      unfold LtGoal at h
      -- `assumption`, not `exact h`: elaborating `h` would `whnf` (run) the `wpN` type
      dsimp only
      assumption
  have ⟨_, _, _, _, _, _, _, _, _, _, hww⟩ := hscan
  obtain ⟨t, hr, ht, hrip', -, hlv'⟩ := sound_one postListing_valid hvc s hlv
    (main_loaded hc hww) (hrip.trans rfl) ⟨hscan, h0⟩
  exact ⟨t, hr, hlv', hrip'.trans rfl, ht⟩

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Startup.SetName (VcLibs VcLt slashCase_of)

/-- **`set_program_name` as a segment**, VERIFIED from the loop-cut VCs `vc_libs`, `vc_lt`. -/
theorem setProgNameSeg' (hlibs : VcLibs) (hlt : VcLt) :
    Seg (fun _ => True) CmainEntryCut OptParseCut :=
  setProgNameSeg (slashCase_of hlibs hlt)

end Silmaril.Process.LPS.Problems.GnuSha256sum
