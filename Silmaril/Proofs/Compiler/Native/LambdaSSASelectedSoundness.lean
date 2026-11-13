module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.OptimizerAdmission.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.PureSoundness.Thms
/-! Actual successful optimizer selection discharges checker fragment premises.
The real block caller retains validated local-SSA or identity fallback. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness
open Silmaril.Compile Silmaril.Machine
open Validation.PureSoundness

/-- Actual successful selection discharges both fragment premises and the
actual checker result; only the real source-execution premise remains inside
Preserves. Original incoming frames may be partial. -/
theorem optimize_preserves {base : Nat} {source candidate : Mir.Block} {count : Nat}
    (selected : optimize? base source = some (candidate, count)) : Preserves base source candidate := by
  obtain ⟨sourceAdmitted, candidateAdmitted, checked⟩ := OptimizerAdmission.optimize_admitted selected
  exact check_sound base source candidate sourceAdmitted candidateAdmitted checked

/-- Actual selected optimization derives candidate execution and both ordered
source-output reads from actual source execution, without admission premises. -/
theorem optimize_block_refines {base : Nat} {source candidate : Mir.Block} {count : Nat}
    (selected : optimize? base source = some (candidate, count))
    (calls : OpenCalls) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory) :
    ∃ candidateFrame values,
      BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Validation.Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Validation.Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨sourceAdmitted, candidateAdmitted, checked⟩ := OptimizerAdmission.optimize_admitted selected
  exact accepted_block_refines calls base source candidate frame sourceFrame memory sourceMemory exit
    sourceExecuted sourceAdmitted candidateAdmitted checked

theorem preserves_refl (base : Nat) (source : Mir.Block) : Preserves base source source := by
  intro calls frame final memory after exit executed
  exact ⟨final, executed, rfl, fun _ _ => rfl⟩

/-- Actual leave appends real move commits to the real renamed instruction
array; source fragment admission therefore suffices for fallback admission. -/
theorem leave_enter_admitted (base : Nat) (source : Mir.Block)
    (admitted : Validation.Lists.Admitted source.instrs.toList) :
    Validation.Lists.Admitted (leave (enter base source)).instrs.toList := by
  have renamed : Validation.Lists.Admitted (enter base source).body.instrs.toList :=
    (OptimizerAdmission.enter_admitted_iff base source).mpr admitted
  intro instruction member
  change instruction ∈ ((enter base source).body.instrs ++
    (enter base source).outputs.toArray.map (fun (original, version) => Mir.Instr.op (.move original version))).toList at member
  rw [Array.toList_append] at member
  rcases List.mem_append.mp member with original | commit
  · exact renamed instruction original
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp (by simpa only [Array.toList_map, List.toList_toArray] using commit)
    subst instruction
    trivial

/-- The exact existing fallback either passes its actual retained checker or
returns the original source. The extra isSSA test is retained verbatim. -/
theorem fallback_preserves (base : Nat) (source : Mir.Block)
    (admitted : Validation.Lists.Admitted source.instrs.toList) :
    Preserves base source (if (enter base source).isSSA && Validation.check base source (leave (enter base source))
      then leave (enter base source) else source) := by
  by_cases accepted : ((enter base source).isSSA && Validation.check base source (leave (enter base source))) = true
  · simp only [accepted, ↓reduceIte]
    have both : (enter base source).isSSA = true ∧ Validation.check base source (leave (enter base source)) = true := by
      simpa only [Bool.and_eq_true] using accepted
    exact check_sound base source (leave (enter base source)) admitted (leave_enter_admitted base source admitted) both.2
  · simp only [accepted]
    exact preserves_refl base source

/-- The real caller uses the actual selected candidate whenever LambdaSSA is
enabled and selection succeeds. No fallback behavior is assumed. -/
theorem roundTripBlock_selected (cfg : Config) (base : Nat) (source candidate : Mir.Block) (count : Nat)
    (enabled : cfg.lambdaSSA = true) (selected : optimize? base source = some (candidate, count)) :
    roundTripBlock cfg base source = candidate := by
  simp only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_some, Option.getD_some]

/-- The real block caller preserves finite successful admitted source runs
for every configuration, including enabled/disabled and actual fallback paths. -/
theorem roundTripBlock_preserves (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Validation.Lists.Admitted source.instrs.toList) :
    Preserves base source (roundTripBlock cfg base source) := by
  cases enabled : cfg.lambdaSSA with
  | false =>
    simpa only [roundTripBlock, enabled, Bool.false_eq_true, ↓reduceIte] using fallback_preserves base source admitted
  | true =>
    show Preserves base source (roundTripBlock cfg base source)
    cases selected : optimize? base source with
    | none =>
      simpa only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_none, Option.getD_none] using
        fallback_preserves base source admitted
    | some result =>
      obtain ⟨candidate, count⟩ := result
      rw [roundTripBlock_selected cfg base source candidate count enabled selected]
      exact optimize_preserves selected

end Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness
