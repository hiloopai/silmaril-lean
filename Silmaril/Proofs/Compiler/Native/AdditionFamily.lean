module

public import Silmaril.Compiler.Native.Correctness.AdditionFamily.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionMain.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralFamily.Thms
public import Silmaril.Compiler.Native.Emit.AdditionFeatures.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionText.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionFamily

open Silmaril.Cerberus

def program (left right : Int) (bounded : AdditionSource.Bounds left right) : Program domain :=
  ⟨source left right, ⟨left, right, bounded, rfl⟩, by
    refine ⟨Literal42.sym 1 "main", {
      loc := .unknown, marker := 7, attrs := .mk [], params := [],
      body := AdditionSource.body left right}, rfl, ?_⟩
    exact List.mem_singleton_self _, LiteralFamily.arguments_ok⟩

/-- Actual Functions elaboration is derived for every domain member,
independently of whether the native compilation succeeds. -/
theorem sourceCoverage : Task.elaborationCoversAccepted domain := by
  intro candidate assembly compiled
  obtain ⟨left, right, bounded, same⟩ := candidate.property.1
  exact ⟨AdditionSource.bindings left right, same ▸ AdditionMain.actual_elaborates left right⟩

/-- The actual elaborated Core model satisfies the independent sum sentence. -/
theorem source_model (left right : Int) (bounded : AdditionSource.Bounds left right) :
    ∃ model : Silmaril.Cerberus.Institution.Model,
      Elaborates (source left right) model ∧
      Silmaril.Cerberus.Institution.Satisfies model
        (Silmaril.Compiler.Core.ElaborationTotal.returnsInteger (left + right)) :=
  AdditionMain.source_model left right bounded

/-- The no-output process specification is about every actual source behavior. -/
theorem source_satisfies (left right : Int) (bounded : AdditionSource.Bounds left right) :
    (sourceLanguage domain).Sat (program left right bounded) (AdditionMain.specification left right) := by
  intro observation behavior
  exact (AdditionMain.source_behaviors_exact left right bounded observation).1 behavior

/-- Every complete native observation from independently stated physical entry
has the actual Cerberus source process result. The later loader must derive
this entry from installed code, rather than supplying a successful execution. -/
theorem machine_observes (left right : Int) (bounded : AdditionSource.Bounds left right)
    (initial : Silmaril.X86.Features.MState) (exit : Silmaril.X86.Word)
    (entry : Silmaril.Compiler.Native.Emit.AdditionFeatures.Entry initial
      (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit)
    (observation : Observation) (realised : Realises exit initial observation) :
    observation ∈ AdditionMain.specification left right := by
  obtain ⟨final, ready, all⟩ := Silmaril.Compiler.Native.Emit.AdditionFeatures.behavior initial
    (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit entry
  have same : observation =
      .returned (Silmaril.Machine.X86.Decompile.Features.lift initial.state final) :=
    (all observation).mp realised
  subst observation
  change Silmaril.Compile.Core.Spec.Obs.exit ((final.core.read .rax).toNat % 256) [] =
    .exit ((left + right) % 256).toNat []
  rw [ready.result, AdditionLower.body_value left right bounded, LiteralEmission.word_status]

/-- The real O0 native driver produces the full independently stated unit text. -/
theorem source_compiles (left right : Int) (bounded : AdditionSource.Bounds left right) :
    compile (source left right) =
      .ok (AdditionText.assembly (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) := by
  change Silmaril.Compiler.Native.Driver.compile {opt := some .O0} "literal-linkage"
    (AdditionSource.program left right) true = _
  exact AdditionText.compile_O0 left right bounded "literal-linkage" true

theorem program_runs (left right : Int) (bounded : AdditionSource.Bounds left right) :
    run (program left right bounded) = some (target left right) := by
  change (match compile (source left right) with
    | .ok text => some (⟨text, (source left right).arguments⟩ : Target)
    | .error _ => none) = some (target left right)
  rw [source_compiles left right bounded]
  rfl

/-- Every admitted load has proved concrete memory shape, and every compiled
member has a genuinely parsed/assembled/installed load. -/
def toolchain : Toolchain domain where
  loads := Loads
  loaded := fun _ _ _ accepted => AdditionText.loads_loaded accepted
  produces := by
    intro candidate text member main compiled argumentsOk
    obtain ⟨left, right, bounded, rfl⟩ := member
    have sameText : text = AdditionText.assembly (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) :=
      Except.ok.inj (compiled.symm.trans (source_compiles left right bounded))
    subst text
    exact ⟨_, AdditionText.loads_actual _ _⟩

/-- Every complete observation from every admitted formal load refines the
actual elaborated Core semantics of the same independently fixed source. -/
theorem machineRefinement : Task.machineRefinement domain toolchain := by
  intro accepted compiledTarget compiled observation behavior
  obtain ⟨left, right, bounded, sourceEq⟩ := accepted.property.1
  have targetEq : compiledTarget = target left right := by
    change (match compile accepted.val with
      | .ok text => some (⟨text, accepted.val.arguments⟩ : Target)
      | .error _ => none) = some compiledTarget at compiled
    rw [sourceEq, source_compiles left right bounded] at compiled
    exact (Option.some.inj compiled).symm
  subst compiledTarget
  obtain ⟨image, loaded, realised⟩ := behavior
  have imageEq : image = AdditionText.image (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) :=
    (AdditionText.loads_words loaded).2
  rw [imageEq] at realised
  rw [sourceEq]
  apply (AdditionMain.source_behaviors_exact left right bounded observation).2
  exact machine_observes left right bounded _ _ (AdditionText.entry _ _) observation realised

theorem example_bounds : AdditionSource.Bounds 17 (-29) := by
  unfold AdditionSource.Bounds LiteralEmission.IsInt32
  decide +kernel

/-- A genuine nonempty native certificate for the complete bounded addition
family and the explicit formal assembler/loader. GNU as, ELF, OS startup and
arbitrary C remain separate implementation/adequacy obligations. -/
theorem certificate : Certificate domain toolchain where
  acceptedProgram := ⟨program 17 (-29) example_bounds, _, source_compiles 17 (-29) example_bounds⟩
  sourceCoverage := sourceCoverage
  machineRefinement := machineRefinement

def compilerPass := certificate.toPass

def compiler := compilerPass.toCompiler

/-- Category packaging retains the actual native driver run, without an extra
checker, acceptance guard or executable fallback. -/
theorem pass_run (left right : Int) (bounded : AdditionSource.Bounds left right) :
    compilerPass.run (program left right bounded) = some (target left right) :=
  program_runs left right bounded

theorem compiler_run (left right : Int) (bounded : AdditionSource.Bounds left right) :
    compiler.run (program left right bounded) = some (target left right) :=
  program_runs left right bounded

/-- Arbitrary native-observation specifications transport through the actual
compiler only after source coverage and machine refinement are proved above. -/
theorem preserves_specification (left right : Int) (bounded : AdditionSource.Bounds left right)
    (specification : Set Observation)
    (satisfied : (sourceLanguage domain).Sat (program left right bounded) specification) :
    (targetLanguage toolchain).Sat (target left right) specification :=
  Institution.preserves_projected_specification domain toolchain machineRefinement
    (program_runs left right bounded) satisfied

theorem target_satisfies (left right : Int) (bounded : AdditionSource.Bounds left right) :
    (targetLanguage toolchain).Sat (target left right) (AdditionMain.specification left right) :=
  preserves_specification left right bounded _ (source_satisfies left right bounded)

theorem target_satisfies_hets (left right : Int) (bounded : AdditionSource.Bounds left right) :
    ((((Hets.graph domain toolchain).inst Hets.Node.nativeMachine).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
      (targetBehaviors toolchain (target left right)) (AdditionMain.specification left right) :=
  target_satisfies left right bounded

/-- Model readback along the real Hets compiler edge refines the actual
same-source model; no equality of full-state Core/native models is asserted. -/
theorem native_readback_refinement (left right : Int) (bounded : AdditionSource.Bounds left right) :
    (show Set Observation from
      (((Hets.graph domain toolchain).comor Hets.Translation.compile).ρ.app
        (CategoryTheory.Discrete.mk PUnit.unit)).mod.obj
        (targetBehaviors toolchain (target left right))) ⊆ sourceBehaviors (source left right) := by
  change _root_.id '' targetBehaviors toolchain (target left right) ⊆ sourceBehaviors (source left right)
  rw [Set.image_id]
  exact machineRefinement (program left right bounded) _ (program_runs left right bounded)

/-- The actual graph edge translates arbitrary proved source specifications. -/
theorem target_graph_specification (left right : Int) (bounded : AdditionSource.Bounds left right)
    (specification : Set Observation)
    (satisfied : (sourceLanguage domain).Sat (program left right bounded) specification) :
    ((((Hets.graph domain toolchain).inst Hets.Node.nativeMachine).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
      (targetBehaviors toolchain (target left right))
      ((((Hets.graph domain toolchain).comor Hets.Translation.compile).ρ.app
        (CategoryTheory.Discrete.mk PUnit.unit)).sen specification) := by
  apply ((((Hets.graph domain toolchain).comor Hets.Translation.compile).ρ.app
    (CategoryTheory.Discrete.mk PUnit.unit)).sat
      (targetBehaviors toolchain (target left right)) specification).mpr
  intro observation member
  exact satisfied (native_readback_refinement left right bounded member)

theorem native_path_comorphism :
    Silmaril.Logic.Institution.IndexedCoInst.coHom (Hets.graph domain toolchain).indexed
      ((Hets.graph domain toolchain).pathHom (Hets.nativePath domain toolchain)) =
      (Hets.graph domain toolchain).comor Hets.Translation.compile :=
  (Hets.graph domain toolchain).coHom_toPath Hets.Translation.compile

/-- Complete raw target meaning is one actual returned state. Every formal
load is included; stopped outcomes and divergence are excluded by execution,
rather than removed from the observation model. -/
theorem target_behaviors_exact (left right : Int) :
    ∃ final : NativeState, ∀ observation,
      observation ∈ targetBehaviors toolchain (target left right) ↔ observation = .returned final := by
  obtain ⟨final, ready, all⟩ := Silmaril.Compiler.Native.Emit.AdditionFeatures.behavior
    (AdditionText.image (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)).initial
    (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) 0x4000 (AdditionText.entry _ _)
  refine ⟨Silmaril.Machine.X86.Decompile.Features.lift
    (AdditionText.image (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)).initial.state final, ?_⟩
  intro observation
  constructor
  · rintro ⟨image, loaded, realised⟩
    have imageEq : image = AdditionText.image (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) :=
      (AdditionText.loads_words loaded).2
    rw [imageEq] at realised
    exact (all observation).mp realised
  · intro same
    exact ⟨_, AdditionText.loads_actual _ _, (all observation).mpr same⟩

/-- Target meaning is nonempty for every emitted word pair, in particular
for every bounded source, rather than only the certificate's one witness. -/
theorem target_nonempty (left right : Int) :
    ∃ observation, observation ∈ targetBehaviors toolchain (target left right) := by
  obtain ⟨final, exactBehavior⟩ := target_behaviors_exact left right
  exact ⟨.returned final, (exactBehavior _).mpr rfl⟩

end Silmaril.Compiler.Native.Correctness.AdditionFamily
