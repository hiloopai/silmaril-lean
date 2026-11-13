module

public import Silmaril.Compiler.Native.Correctness.Literal42.Defs
public import Silmaril.Compiler.Native.Assembly.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralImage.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Thms
/-! A nonempty closed-main singleton compiler certificate. Actual compilation,
independent assembly syntax/layout/encoding and explicit loading compose with
unbounded actual Core and Features semantics. This does not certify GNU as,
ELF, external linking, generic native passes or a richer process contract. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Literal42
open Silmaril Silmaril.X86
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core.ElaborationProcess
open Silmaril.Compiler.Native.Assembly
open Construction
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
private theorem decimalDigits (n : Nat) :
    Nat.toDigits 10 n = if n < 10 then [n.digitChar]
      else Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] :=
  Nat.toDigits_eq_ite (by decide)
attribute [local cbv_eval] decimalDigits Nat.repr_eq_ofList_toDigits Nat.toString_eq_ofList_toDigits Int.repr_eq_ite
private theorem decimalDigit0 : Nat.digitChar 0 = '0' :=
  Nat.digitChar_eq_zero.mpr rfl
attribute [local cbv_eval] decimalDigit0
private theorem decimalDigit1 : Nat.digitChar 1 = '1' :=
  Nat.digitChar_eq_one.mpr rfl
attribute [local cbv_eval] decimalDigit1
private theorem decimalDigit2 : Nat.digitChar 2 = '2' :=
  Nat.digitChar_eq_two.mpr rfl
attribute [local cbv_eval] decimalDigit2
private theorem decimalDigit3 : Nat.digitChar 3 = '3' :=
  Nat.digitChar_eq_three.mpr rfl
attribute [local cbv_eval] decimalDigit3
private theorem decimalDigit4 : Nat.digitChar 4 = '4' :=
  Nat.digitChar_eq_four.mpr rfl
attribute [local cbv_eval] decimalDigit4
private theorem decimalDigit5 : Nat.digitChar 5 = '5' :=
  Nat.digitChar_eq_five.mpr rfl
attribute [local cbv_eval] decimalDigit5
private theorem decimalDigit6 : Nat.digitChar 6 = '6' :=
  Nat.digitChar_eq_six.mpr rfl
attribute [local cbv_eval] decimalDigit6
private theorem decimalDigit7 : Nat.digitChar 7 = '7' :=
  Nat.digitChar_eq_seven.mpr rfl
attribute [local cbv_eval] decimalDigit7
private theorem decimalDigit8 : Nat.digitChar 8 = '8' :=
  Nat.digitChar_eq_eight.mpr rfl
attribute [local cbv_eval] decimalDigit8
private theorem decimalDigit9 : Nat.digitChar 9 = '9' :=
  Nat.digitChar_eq_nine.mpr rfl
attribute [local cbv_eval] decimalDigit9


namespace Text
attribute [local cbv_opaque] frame

theorem actual_body_syntax : Parses body statements := by
  unfold Parses
  cbv
  refine Lines.cons (Spells.push (by cbv)) ?_
  refine Lines.cons (Spells.mov (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.aluI8 (n := 48) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)) ?_
  refine Lines.cons (Spells.aluI8 (n := -64) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.0") (by decide +kernel)) ?_
  refine Lines.cons (Spells.mov (by cbv) (by cbv)) ?_
  show Lines _ (statements.drop 6)
  refine Lines.cons (Spells.store (n := 8) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.jump (by decide +kernel)) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.1") (by decide +kernel)) ?_
  refine Lines.cons (Spells.movabs (n := 42) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.store (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ (statements.drop 12)
  refine Lines.cons (Spells.movsxd (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.store (n := 32) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 32) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.movsxd (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.store (n := 40) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 40) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ (statements.drop 18)
  refine Lines.cons (Spells.leave) ?_
  refine Lines.cons (Spells.ret) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.2") (by decide +kernel)) ?_
  refine Lines.cons (Spells.movabs (n := 0) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.store (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ (statements.drop 24)
  refine Lines.cons (Spells.leave) ?_
  refine Lines.cons (Spells.ret) ?_
  exact Lines.blank Lines.nil

theorem actual_body_labels : Local statements := by
  simp [Local, statements]

theorem actual_body_assembly : Assembles labels 0 statements bytes 83 := by
  unfold statements bytes
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.label (by cbv) ?_
  refine Assembles.plain ?_
  show Assembles labels 15 (statements.drop 6) (bytes.drop 15) 83
  refine Assembles.plain ?_
  refine Assembles.jump8 (target := 21) (by cbv) (by constructor <;> decide +kernel) ?_
  refine Assembles.label (by cbv) ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 39 (statements.drop 12) (bytes.drop 39) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 61 (statements.drop 18) (bytes.drop 61) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.label (by cbv) ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 81 (statements.drop 24) (bytes.drop 81) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  exact Assembles.nil

end Text

theorem admitted42 : LiteralTotal.domain 42 source42 := by
  refine ⟨literal 42, rfl, rfl, ?_, ?_, conversion, .loaded .integer,
    [(typeParameter, .ctype), (valueParameter, .loaded .integer)], conversionBody, ?_, ?_⟩
  · cbv
  · unfold Silmaril.Compile.Core.Verified.ConvInt.IsInt
    decide +kernel
  all_goals cbv

theorem source_compiles : compile source42 = .ok Text.assembly := by cbv

/-- The actual fixture's single jump is forced short by the following declared
label at offset21. This proves uniqueness for this syntax/table, not for the
nondeterministic short/near relation on arbitrary programs. -/
theorem assembly_unique {code : List Byte} {endPc : Nat}
    (assembled : Text.Assembles Text.labels 0 Text.statements code endPc) : code = Text.bytes := by
  let output := code
  change output = Text.bytes
  unfold Text.statements at assembled
  cases assembled with
  | plain assembled =>
    show output = Text.bytes
    cases assembled with
    | plain assembled =>
      show output = Text.bytes
      cases assembled with
      | plain assembled =>
        show output = Text.bytes
        cases assembled with
        | plain assembled =>
          show output = Text.bytes
          cases assembled with
          | label found assembled =>
            show output = Text.bytes
            cases assembled with
            | plain assembled =>
              show output = Text.bytes
              cases assembled with
              | plain assembled =>
                show output = Text.bytes
                cases assembled with
                | jump8 found fits assembled =>
                  show output = Text.bytes
                  cases found
                  cases assembled with
                  | label found assembled =>
                    show output = Text.bytes
                    cases assembled with
                    | plain assembled =>
                      show output = Text.bytes
                      cases assembled with
                      | plain assembled =>
                        show output = Text.bytes
                        cases assembled with
                        | plain assembled =>
                          show output = Text.bytes
                          cases assembled with
                          | plain assembled =>
                            show output = Text.bytes
                            cases assembled with
                            | plain assembled =>
                              show output = Text.bytes
                              cases assembled with
                              | plain assembled =>
                                show output = Text.bytes
                                cases assembled with
                                | plain assembled =>
                                  show output = Text.bytes
                                  cases assembled with
                                  | plain assembled =>
                                    show output = Text.bytes
                                    cases assembled with
                                    | plain assembled =>
                                      show output = Text.bytes
                                      cases assembled with
                                      | plain assembled =>
                                        show output = Text.bytes
                                        cases assembled with
                                        | plain assembled =>
                                          show output = Text.bytes
                                          cases assembled with
                                          | label found assembled =>
                                            show output = Text.bytes
                                            cases assembled with
                                            | plain assembled =>
                                              show output = Text.bytes
                                              cases assembled with
                                              | plain assembled =>
                                                show output = Text.bytes
                                                cases assembled with
                                                | plain assembled =>
                                                  show output = Text.bytes
                                                  cases assembled with
                                                  | plain assembled =>
                                                    show output = Text.bytes
                                                    cases assembled with
                                                    | plain assembled =>
                                                      show output = Text.bytes
                                                      cases assembled
                                                      rfl
                | jump32 found fits assembled =>
                  show output = Text.bytes
                  cases found
                  cases assembled with
                  | label impossible assembled =>
                    show output = Text.bytes
                    change (some 21 : Option Nat) = some 24 at impossible
                    cases impossible

/-- The same actual elaborated Core model has full integer-return and projected
institution semantics; the frontend target/runtime choices remain explicit. -/
theorem source_model :
    ∃ model : Silmaril.Cerberus.Institution.Model,
      Elaborates source42 model ∧
      Silmaril.Cerberus.Institution.Satisfies model
        (Silmaril.Compiler.Core.ElaborationTotal.returnsInteger 42) ∧
      Silmaril.Cerberus.Institution.Satisfies model
        (Institution.sentence (LiteralTotal.specification 42)) :=
  LiteralTotal.projected_model admitted42

theorem load_actual : loadImage Text.bytes = LiteralImage.image := rfl

theorem loads_image {text : String} {arguments : List String} {image : Image}
    (loaded : Loads text arguments image) : arguments = ["a.out"] ∧ image = LiteralImage.image := by
  obtain ⟨code, parsed, localLabels, assembled, argumentsEq, imageEq⟩ := loaded
  rw [assembly_unique assembled] at imageEq
  exact ⟨argumentsEq, imageEq.trans load_actual⟩

def toolchain : Toolchain domain where
  loads := Loads
  loaded := by
    intro text arguments image loaded
    obtain ⟨rfl, rfl⟩ := loads_image loaded
    exact LiteralImage.loaded
  produces := by
    intro source text admitted main compiled argumentsOk
    have sameSource : source = source42 := admitted
    subst source
    have sameText : text = Text.assembly := Except.ok.inj (compiled.symm.trans source_compiles)
    subst text
    refine ⟨loadImage Text.bytes, Text.bytes, ?_, Text.actual_body_labels, Text.actual_body_assembly, rfl, rfl⟩
    exact Text.MainSyntax.function Text.actual_body_syntax

theorem domain_literal {source : Source} (member : domain source) :
    LiteralTotal.domain 42 source := by
  cases member
  exact admitted42

def program : Program domain := ⟨source42, rfl, by
    refine ⟨(literal 42).symbol,
      {loc := (literal 42).location, marker := (literal 42).marker,
        attrs := (literal 42).attributes, params := [], body := (literal 42).body}, rfl, ?_⟩
    exact List.mem_singleton_self _, LiteralImage.arguments_ok⟩

theorem sourceCoverage : Task.elaborationCoversAccepted domain :=
  Literal.coverage_on domain (fun _ admitted =>
    LiteralTotal.domain_elaborationDomain (domain_literal admitted))

/-- Every load admitted by the concrete formal toolchain is the checked actual
machine image, whose every observation is allowed by the actual elaborated Core. -/
theorem machineRefinement : Task.machineRefinement domain toolchain := by
  intro source target compiled observation behavior
  obtain ⟨image, loaded, realised⟩ := behavior
  have imageEq := (loads_image loaded).2
  rw [imageEq] at realised
  apply (LiteralTotal.sourceBehaviors_iff_exit (domain_literal source.property.1) observation).2
  exact LiteralImage.actual_bytes_all_observations observation realised

/-- A real nonempty certificate for exactly this independently selected Source
and formal assembler/loader. This is not an implementation theorem for GNU as. -/
theorem certificate : Certificate domain toolchain where
  acceptedProgram := ⟨program, Text.assembly, source_compiles⟩
  sourceCoverage := sourceCoverage
  machineRefinement := machineRefinement

/-- Category packaging consumes the proved machine refinement. -/
def compilerPass := certificate.toPass

theorem program_runs : run program = some target := by
  change (match compile source42 with
    | .ok text => some (⟨text, source42.arguments⟩ : Target)
    | .error _ => none) = some target
  rw [source_compiles]
  rfl

theorem source_satisfies :
    (sourceLanguage domain).Sat program (LiteralTotal.specification 42) := by
  intro observation behavior
  exact (LiteralTotal.sourceBehaviors_iff_exit admitted42 observation).1 behavior

/-- The proved actual compiler run preserves the existing projected institution
sentence for every actual target observation in the formal toolchain. -/
theorem target_satisfies :
    (targetLanguage toolchain).Sat target (LiteralTotal.specification 42) :=
  Institution.preserves_projected_specification domain toolchain machineRefinement
    program_runs source_satisfies

theorem target_satisfies_hets :
    ((((Hets.graph domain toolchain).inst Hets.Node.nativeMachine).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
        (targetBehaviors toolchain target) (LiteralTotal.specification 42) :=
  target_satisfies

/-- Target meaning is inhabited as well as universally correct. -/
theorem target_nonempty : ∃ observation, observation ∈ targetBehaviors toolchain target := by
  obtain ⟨final, realised, observed⟩ := LiteralImage.actual_bytes_return
  refine ⟨.returned final, LiteralImage.image, ?_, realised⟩
  refine ⟨Text.bytes, Text.MainSyntax.function Text.actual_body_syntax,
    Text.actual_body_labels, Text.actual_body_assembly, rfl, ?_⟩
  exact load_actual.symm


end Silmaril.Compiler.Native.Correctness.Literal42
