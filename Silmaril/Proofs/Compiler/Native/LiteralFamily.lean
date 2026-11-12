module

public import Silmaril.Compiler.Native.Correctness.LiteralFamily.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralEmission.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralInteger.Thms
public import Silmaril.Compiler.Native.Correctness.Hets.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralLoader.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralText.Thms
/-! The independently selected canonical literal family has actual elaborated
Core models and actual compiler outputs. Closed-main assembly, loading and
fetched-byte semantics are proved separately below. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralFamily
open Silmaril Silmaril.X86
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core.ElaborationProcess
open Literal42
open Construction
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local cbv_eval] String.toUTF8_eq_toByteArray
attribute [local cbv_eval] Std.ExtDHashMap.Const.get?_insert Std.ExtDHashMap.Const.get?_empty

theorem admitted (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    LiteralTotal.domain number (source number) := by
  refine ⟨LiteralEmission.literal number, rfl, rfl, ?_, ?_, conversion, .loaded .integer,
    [(typeParameter, .ctype), (valueParameter, .loaded .integer)], conversionBody, ?_, ?_⟩
  · cbv
  · unfold Silmaril.Compile.Core.Verified.ConvInt.IsInt
    change -(2147483648 : Int) ≤ number ∧ number ≤ 2147483647
    have lower : -(2147483648 : Int) ≤ number := bounded.1
    have upper : number < (2147483648 : Int) := bounded.2
    omega
  all_goals cbv

theorem source_compiles (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    compile (source number) = .ok (LiteralEmission.assembly (BitVec.ofInt 64 number)) :=
  LiteralEmission.compile_O0 number bounded

theorem domain_literal {candidate : Source} (member : domain candidate) :
    ∃ number, LiteralEmission.IsInt32 number ∧ LiteralTotal.domain number candidate := by
  obtain ⟨number, bounded, rfl⟩ := member
  exact ⟨number, bounded, admitted number bounded⟩

theorem arguments_ok : Silmaril.Compile.Core.Spec.ArgsOk ["a.out"] := by
  unfold Silmaril.Compile.Core.Spec.ArgsOk
  cbv
  decide +kernel

def program (number : Int) (bounded : LiteralEmission.IsInt32 number) : Program domain :=
  ⟨source number, ⟨number, bounded, rfl⟩, by
    refine ⟨(LiteralEmission.literal number).symbol,
      {loc := (LiteralEmission.literal number).location,
        marker := (LiteralEmission.literal number).marker,
        attrs := (LiteralEmission.literal number).attributes, params := [],
        body := (LiteralEmission.literal number).body}, rfl, ?_⟩
    exact List.mem_singleton_self _, arguments_ok⟩

theorem source_model (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    ∃ model : Silmaril.Cerberus.Institution.Model,
      Elaborates (source number) model ∧
      Silmaril.Cerberus.Institution.Satisfies model
        (Silmaril.Compiler.Core.ElaborationTotal.returnsInteger number) ∧
      Silmaril.Cerberus.Institution.Satisfies model
        (Institution.sentence (LiteralTotal.specification number)) :=
  LiteralTotal.projected_model (admitted number bounded)

theorem source_satisfies (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    (sourceLanguage domain).Sat (program number bounded) (LiteralTotal.specification number) := by
  intro observation behavior
  exact (LiteralTotal.sourceBehaviors_iff_exit (admitted number bounded) observation).1 behavior

theorem program_runs (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    run (program number bounded) = some (target number) := by
  change (match compile (source number) with
    | .ok text => some (⟨text, (source number).arguments⟩ : Target)
    | .error _ => none) = some (target number)
  rw [source_compiles number bounded]
  rfl

theorem sourceCoverage : Task.elaborationCoversAccepted domain :=
  Literal.coverage_on domain (fun _ member => by
    obtain ⟨number, bounded, domain⟩ := domain_literal member
    exact LiteralTotal.domain_elaborationDomain domain)

/-- Actual installed code and the explicit caller stack supply the independent
entry conditions for every encoded word. Successful execution is a conclusion
of LiteralInteger, never a loader premise. -/
theorem image_entry (value : Word) : LiteralInteger.Entry value 0x1000 0x4000
    (LiteralLoader.image (LiteralInteger.code value)).initial.toBase := by
  constructor
  · rfl
  · exact LiteralLoader.code_fetch _ (LiteralInteger.code_length value)
  · change (128 : Nat) ≤ 0x2ff8
    decide +kernel
  · change (0x2ff8 : Nat) + 8 < 2 ^ 64
    decide +kernel
  · change ((0x2ff8 : Nat) + 8) % 16 = 0
    decide +kernel
  · exact LiteralLoader.stack_read _
  · exact LiteralLoader.stack_write _
  · exact LiteralLoader.return_read _
  · left
    change 0x1000 + (LiteralInteger.code value).length ≤ 0x2ff8 - 48
    rw [LiteralInteger.code_length]
    decide +kernel

/-- The actual emitter text has a checked independent syntax/layout derivation
and a directly installed actual image for every word. -/
theorem loads_actual (value : Word) :
    Loads (LiteralEmission.assembly value) ["a.out"]
      (LiteralLoader.image (LiteralInteger.code value)) := by
  refine ⟨value, LiteralText.bytes value, ?_, LiteralText.local_labels value,
    LiteralText.assembles value, rfl, rfl⟩
  rw [← LiteralText.actual_emission]
  exact LiteralText.main_syntax value

/-- Every admitted load has actual installed template bytes. Grammar is not
needed for this shape fact; encoding uniqueness is proved from the derivation. -/
theorem loads_shape {text : String} {arguments : List String} {image : Image}
    (loaded : Loads text arguments image) :
    ∃ value, arguments = ["a.out"] ∧
      image = LiteralLoader.image (LiteralInteger.code value) := by
  obtain ⟨value, code, parsed, localLabels, assembled, argumentsEq, imageEq⟩ := loaded
  rw [LiteralText.assembly_unique assembled] at imageEq
  exact ⟨value, argumentsEq, imageEq⟩

/-- Actual parsing fixes the immediate word, then checked encoding fixes all
bytes. Text equality by itself never supplies a loading derivation. -/
theorem loads_word {value : Word} {arguments : List String} {image : Image}
    (loaded : Loads (LiteralEmission.assembly value) arguments image) :
    arguments = ["a.out"] ∧
      image = LiteralLoader.image (LiteralInteger.code value) := by
  obtain ⟨parsedValue, code, parsed, localLabels, assembled, argumentsEq, imageEq⟩ := loaded
  rw [← LiteralText.actual_emission] at parsed
  have valueEq : parsedValue = value := LiteralText.parsed_value_unique parsed
  subst parsedValue
  rw [LiteralText.assembly_unique assembled] at imageEq
  exact ⟨argumentsEq, imageEq⟩

def toolchain : Toolchain domain where
  loads := Loads
  loaded := by
    intro text arguments image loaded
    obtain ⟨value, rfl, rfl⟩ := loads_shape loaded
    exact LiteralLoader.loaded _ (LiteralInteger.code_length value)
  produces := by
    intro candidate text member main compiled argumentsOk
    obtain ⟨number, bounded, rfl⟩ := member
    have sameText : text = LiteralEmission.assembly (BitVec.ofInt 64 number) :=
      Except.ok.inj (compiled.symm.trans (source_compiles number bounded))
    subst text
    exact ⟨_, loads_actual (BitVec.ofInt 64 number)⟩

/-- Every observation from every independently admitted load of the actual
compiler output refines the actual same-source elaborated Core behavior. -/
theorem machineRefinement : Task.machineRefinement domain toolchain := by
  intro accepted compiledTarget compiled observation behavior
  obtain ⟨number, bounded, sourceEq⟩ := accepted.property.1
  have targetEq : compiledTarget = target number := by
    change (match compile accepted.val with
      | .ok text => some (⟨text, accepted.val.arguments⟩ : Target)
      | .error _ => none) = some compiledTarget at compiled
    rw [sourceEq, source_compiles number bounded] at compiled
    exact (Option.some.inj compiled).symm
  subst compiledTarget
  obtain ⟨image, loaded, realised⟩ := behavior
  have imageEq : image = LiteralLoader.image (LiteralInteger.code (BitVec.ofInt 64 number)) :=
    (loads_word loaded).2
  rw [imageEq] at realised
  rw [sourceEq]
  apply (LiteralTotal.sourceBehaviors_iff_exit (admitted number bounded) observation).2
  exact LiteralInteger.observes number bounded _ (image_entry _) observation realised

/-- A nonempty certificate for the full independently bounded signed32 literal
family and the explicit formal assembler/loader. External assembly, linking,
startup and richer C programs remain separate correctness obligations. -/
theorem certificate : Certificate domain toolchain where
  acceptedProgram := ⟨program 0 (by unfold LiteralEmission.IsInt32; decide +kernel), _,
    source_compiles 0 (by unfold LiteralEmission.IsInt32; decide +kernel)⟩
  sourceCoverage := sourceCoverage
  machineRefinement := machineRefinement

def compilerPass := certificate.toPass

theorem target_satisfies (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    (targetLanguage toolchain).Sat (target number) (LiteralTotal.specification number) :=
  Institution.preserves_projected_specification domain toolchain machineRefinement
    (program_runs number bounded) (source_satisfies number bounded)

theorem target_satisfies_hets (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    ((((Hets.graph domain toolchain).inst Hets.Node.nativeMachine).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
        (targetBehaviors toolchain (target number)) (LiteralTotal.specification number) :=
  target_satisfies number bounded

/-- Every bounded source's target meaning contains an actual native return. -/
theorem target_nonempty (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    ∃ observation, observation ∈ targetBehaviors toolchain (target number) := by
  obtain ⟨final, result, all⟩ := LiteralInteger.total number bounded _
    (image_entry (BitVec.ofInt 64 number))
  exact ⟨.returned final, _, loads_actual _, (all _).mpr rfl⟩

end Silmaril.Compiler.Native.Correctness.LiteralFamily
