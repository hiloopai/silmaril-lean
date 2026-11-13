module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Determinism.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution
open Silmaril.Machine Silmaril.Compile CategoryTheory

/-- The proved partial-frame agreement is exactly equality of these complete
boundary observations. -/
theorem observe_agrees {base : Nat} {source candidate : Lir.Frame Nat}
    (exit : BlockExit) (memory : Lir.Memory)
    (agrees : Validation.PureSoundness.FrameAgrees base source candidate) :
    observe base exit candidate memory = observe base exit source memory := by
  unfold observe
  congr 1
  · funext reg
    exact agrees.registers reg.val reg.isLt
  · exact agrees.slots

/-- Actual finite-success preservation gives the forward behavior inclusion. -/
theorem behaviors_forward (context : Context) {source candidate : Mir.Block}
    (preserves : Validation.PureSoundness.Preserves context.base source candidate) :
    behaviors context source ⊆ behaviors context candidate := by
  intro observation sourceBehavior
  obtain ⟨exit, final, memory, executed, observed⟩ := sourceBehavior
  obtain ⟨candidateFrame, candidateExec, agrees⟩ :=
    preserves context.calls context.frame final context.memory memory exit executed
  exact ⟨exit, candidateFrame, memory, candidateExec, (observe_agrees exit memory agrees).trans observed⟩

/-- Independent actual source definedness and actual target determinism supply
the reverse inclusion required by the category-of-compilers pass interface. -/
theorem behaviors_equal (context : Context) {source candidate : Mir.Block}
    (defined : Defined context source)
    (candidateAdmitted : Validation.Lists.Admitted candidate.instrs.toList)
    (preserves : Validation.PureSoundness.Preserves context.base source candidate) :
    behaviors context source = behaviors context candidate := by
  apply Set.Subset.antisymm (behaviors_forward context preserves)
  obtain ⟨exit, final, memory, executed⟩ := defined
  obtain ⟨candidateFrame, candidateExec, agrees⟩ :=
    preserves context.calls context.frame final context.memory memory exit executed
  intro observation candidateBehavior
  obtain ⟨otherExit, otherFrame, otherMemory, otherExec, observed⟩ := candidateBehavior
  obtain ⟨sameExit, sameFrame, sameMemory⟩ :=
    Validation.Determinism.block candidateAdmitted candidateExec otherExec
  subst otherExit
  subst otherFrame
  subst otherMemory
  exact ⟨exit, final, memory, executed, (observe_agrees exit memory agrees).symm.trans observed⟩

/-- Actual successful optimizer selection derives membership of the candidate
in the independent execution domain. -/
theorem selected_domain (context : Context) (source : Program context)
    {candidate : Mir.Block} {count : Nat}
    (selected : optimize? context.base source.val = some (candidate, count)) :
    Validation.Lists.Admitted candidate.instrs.toList ∧ Defined context candidate := by
  obtain ⟨_, admitted, _⟩ := OptimizerAdmission.optimize_admitted selected
  refine ⟨admitted, ?_⟩
  obtain ⟨exit, final, memory, executed⟩ := source.property.2
  obtain ⟨candidateFrame, candidateExec, _⟩ :=
    SelectedSoundness.optimize_preserves selected context.calls context.frame final context.memory memory exit executed
  exact ⟨exit, candidateFrame, memory, candidateExec⟩

/-- The actual optimizer, retaining failure. Only proof fields are added to the
selected block; no fallback, new acceptance test or runtime witness is used. -/
def run (context : Context) (source : Program context) : Option (Program context) :=
  match selected : optimize? context.base source.val with
  | none => none
  | some (candidate, _count) => some ⟨candidate, selected_domain context source selected⟩

/-- Erasing the domain proofs yields exactly the real optimizer's candidate
projection. -/
theorem run_value (context : Context) (source : Program context) :
    (run context source).map (fun program : Program context => program.val) = (optimize? context.base source.val).map Prod.fst := by
  unfold run
  split
  · rename_i optimized
    exact (congrArg (Option.map Prod.fst) optimized).symm
  · rename_i candidate count optimized
    change some candidate = (optimize? context.base source.val).map Prod.fst
    exact (congrArg (Option.map Prod.fst) optimized).symm

/-- Proof erasure retains the actual optimizer success/failure test. -/
theorem run_isSome (context : Context) (source : Program context) :
    (run context source).isSome = (optimize? context.base source.val).isSome := by
  have same := congrArg Option.isSome (run_value context source)
  simpa only [Option.isSome_map] using same

theorem run_none (context : Context) (source : Program context) :
    run context source = none ↔ optimize? context.base source.val = none := by
  have same := run_value context source
  constructor
  · intro failed
    rw [failed, Option.map_none] at same
    exact Option.map_eq_none_iff.mp same.symm
  · intro failed
    rw [failed, Option.map_none] at same
    exact Option.map_eq_none_iff.mp same

theorem run_selected (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) :
    ∃ count, optimize? context.base source.val = some (candidate.val, count) := by
  have values := congrArg (Option.map (fun program : Program context => program.val)) selected
  rw [run_value] at values
  change (optimize? context.base source.val).map Prod.fst = some candidate.val at values
  cases optimized : optimize? context.base source.val with
  | none => rw [optimized] at values; cases values
  | some result =>
    obtain ⟨block, count⟩ := result
    rw [optimized] at values
    have same : block = candidate.val := Option.some.inj values
    subst block
    exact ⟨count, rfl⟩

/-- Every successful selected run has equal sets of actual finite observations. -/
theorem run_behaviors (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) :
    (language context).beh source = (language context).beh candidate := by
  obtain ⟨count, optimized⟩ := run_selected context selected
  exact behaviors_equal context source.property.2 candidate.property.1
    (SelectedSoundness.optimize_preserves optimized)

/-- The real successful optimizer is a pass at the actual identity convention. -/
def pass (context : Context) : Category.Pass (𝟙 (language context)) where
  run := run context
  sound source candidate selected :=
    (Category.valid_id_iff source candidate).mpr ⟨rfl, (run_behaviors context selected).symm.subset⟩

/-- The existing category compiler carries the same executable run function. -/
def compiler (context : Context) := (pass context).toCompiler

/-- The standard original-input fallback is composable as an actual endopass. -/
def endoPass (context : Context) : Category.EndoPass (language context) :=
  Category.EndoPass.ofPass (pass context)

/-- The behavioral institution's actual room satisfaction is preserved and
reflected by successful optimizer selection. -/
theorem run_room_sat (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) (specification : Set (Observation context.base)) :
    ((language context).room ()).Sat ((language context).beh source) specification ↔
      ((language context).room ()).Sat ((language context).beh candidate) specification := by
  change (language context).beh source ⊆ specification ↔ (language context).beh candidate ⊆ specification
  rw [run_behaviors context selected]

theorem run_sat (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) (specification : Set (Observation context.base)) :
    (language context).Sat source specification ↔ (language context).Sat candidate specification :=
  run_room_sat context selected specification

namespace Hets
open Silmaril.Logic.Institution

/-- The graph edge's actual model read-back of the selected candidate is the
whole actual source behavior model, proved from execution preservation and
determinism rather than supplied as a compiler contract. -/
theorem run_readback_models (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) :
    (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).mod.obj
        ((language context).beh candidate) = (language context).beh source := by
  change _root_.id '' (language context).beh candidate = (language context).beh source
  rw [Set.image_id]
  exact (run_behaviors context selected).symm

/-- Actual selected optimizer success preserves and reflects specifications
translated along the Hets edge, with its real model and sentence maps. -/
theorem run_graph_sat (context : Context) {source candidate : Program context}
    (selected : run context source = some candidate) (specification : Set (Observation context.base)) :
    (((graph context).inst Node.source).I.obj (Discrete.mk ())).Sat
        ((language context).beh source) specification ↔
      (((graph context).inst Node.optimized).I.obj (Discrete.mk ())).Sat
        ((language context).beh candidate)
        ((((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sen specification) := by
  have condition := (((graph context).comor Translation.optimize).ρ.app (Discrete.mk ())).sat
    ((language context).beh candidate) specification
  rw [run_readback_models context selected] at condition
  exact condition.symm

/-- The existing indexed path interpretation uses the same local optimizer
comorphism, so this connection is available through Hets paths. -/
theorem optimizerPath_comorphism (context : Context) :
    IndexedCoInst.coHom (graph context).indexed ((graph context).pathHom (optimizerPath context)) =
      (graph context).comor Translation.optimize :=
  (graph context).coHom_toPath Translation.optimize

end Hets

end Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution
