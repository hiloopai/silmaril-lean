module

public import Silmaril.Compiler.Native.Correctness.AdditionMain.Defs
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Correctness.AdditionMain
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core
open Silmaril.Compiler.Native.Correctness.AdditionSource
open Silmaril.Cerberus.Core
open Construction
attribute [local cbv_eval] String.toUTF8_eq_toByteArray
attribute [local cbv_eval] Std.ExtDHashMap.Const.get?_insert Std.ExtDHashMap.Const.get?_empty

theorem main_entry (left right : Int) :
    (semanticFile left right).funs.lookup (Literal42.sym 1 "main") =
      some (.procedure .unknown (some 7) (.loaded .integer) [] (procedureBody left right)) := by
  cbv

/-- Recognition inspects the actual independently fixed runtime function syntax
and its actual conversion callees in this elaborated file. -/
theorem conversion_recognized (left right : Int) :
    ConvInt.isConvLoadedInt (semanticFile left right) Literal42.conversion = true := by
  cbv

theorem body_save_free (left right : Int) : ReturnLit.saveFree (coreBody left right) = true := by
  cbv

/-- The actual saved-label map contains the procedure's real return label. -/
theorem return_label (left right : Int) :
    ReturnLit.ReturnLabel (Map.ofList (saves (procedureBody left right)).reverse) returnLabel := by
  exact ReturnLit.returnLabel_body rfl (body_save_free left right)

/-- The actual block return consumes the independently proved expression path
under its real strong-bind continuation, then evaluates the real conversion
runtime call and transfers through the real saved return label. -/
theorem core_body_forced (left right : Int) (bounded : Bounds left right) (labels : Labels)
    (saved : ReturnLit.ReturnLabel labels returnLabel) (environment : Env) {frames : List Frame}
    (boundary : ReturnLit.NoBoundary frames) (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches (semanticFile left right) labels
        ⟨.effectExpr (coreBody left right) environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer (left + right))))), [], finish⟩ := by
  let statementFrames := Frame.strongBind (wildcard .unit) skip environment :: frames
  let transfer := ReturnControl.convertedReturn returnLabel Literal42.conversion (fresh 106)
  let resultPattern := symbolPattern (fresh 106) (.loaded .integer)
  let resultFrames := Frame.strongBind resultPattern transfer environment :: statementFrames
  let extended := extendEnv [(fresh 106, .loaded (.specified (.integer (left + right))))] environment
  have enterBody : Forced.Reaches (semanticFile left right) labels
      ⟨.effectExpr (coreBody left right) environment, frames, memory⟩
      ⟨.effectExpr (coreReturn left right) environment, statementFrames, memory⟩ :=
    ReturnControl.sequence_forced [.loc .unknown, .stmt] (wildcard .unit) _ _ _ _ _
  have enterReturn : Forced.Reaches (semanticFile left right) labels
      ⟨.effectExpr (coreReturn left right) environment, statementFrames, memory⟩
      ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, resultFrames, memory⟩ :=
    ReturnControl.sequence_forced [.loc .unknown, .stmt] resultPattern _ transfer _ _ _
  have expression := AdditionFocused.wrapped_expression_forced (semanticFile left right) labels environment
    resultFrames memory left right bounded
  have bindResult : Forced.Reaches (semanticFile left right) labels
      ⟨.value (.loaded (.specified (.integer (left + right)))), resultFrames,
        Silmaril.Cerberus.Core.DiagnosticOperands.focused memory⟩
      ⟨.effectExpr transfer extended, statementFrames, Silmaril.Cerberus.Core.DiagnosticOperands.focused memory⟩ := by
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, resultFrames, resultPattern, matchPattern,
      symbolPattern, symbolPatternWith, extended]
  have observed : extended.lookup (fresh 106) = some (.loaded (.specified (.integer (left + right)))) :=
    ConvInt.lookup_one rfl
  have sumBound : ConvInt.IsInt (left + right) := by
    change (-2147483648 : Int) ≤ left + right ∧ left + right ≤ 2147483647
    have lower : (-2147483648 : Int) ≤ left + right := bounded.2.2.1
    have upper : left + right < (2147483648 : Int) := bounded.2.2.2
    omega
  have statementBoundary : ReturnLit.NoBoundary statementFrames :=
    ReturnLit.noBoundary_cons boundary trivial
  obtain ⟨finish, stdout, returned⟩ := ReturnControl.converted_return_forced returnLabel returnLabel
    Literal42.conversion (fresh 106) rfl saved (conversion_recognized left right) (left + right) sumBound
    extended observed statementBoundary (Silmaril.Cerberus.Core.DiagnosticOperands.focused memory)
  refine ⟨finish, stdout.trans (Silmaril.Cerberus.Core.DiagnosticOperands.focused_stdout memory), ?_⟩
  exact enterBody.trans (enterReturn.trans (expression.trans (bindResult.trans returned)))

/-- Actual C startup allocates/stores errno and enters the real elaborated
procedure; its diagnostic memory is then handled by the expression theorem.
No successful startup, return execution or expected-result model is a premise. -/
theorem whole_main_forced (left right : Int) (bounded : Bounds left right)
    (enums : Map Sym IntegerType) (arguments : List String) :
    ∃ start labels finish, initial (semanticFile left right) enums arguments = .ok (start, labels) ∧
      Forced.Reaches (semanticFile left right) labels start
        ⟨.halt (.defined (.loaded (.specified (.integer (left + right))))), [], finish⟩ ∧ finish.stdout = "" := by
  have main : (semanticFile left right).main = some (Literal42.sym 1 "main") := rfl
  have noDefinitions : ∀ entry ∈ (semanticFile left right).globs, ∀ base expression,
      entry.2 ≠ .definition base expression := by
    intro entry member
    change entry ∈ [] at member
    cases member
  obtain ⟨start, labels, memory, accesses, started, stdout, entered⟩ := ElaborationTotal.initial_forced_body
    (semanticFile left right) enums arguments noDefinitions main (main_entry left right)
  have labelDefinitions : labels = Map.ofList (saves (procedureBody left right)).reverse := by
    have projected : (initial (semanticFile left right) enums arguments).toOption.map Prod.snd =
        some (Map.ofList (saves (procedureBody left right)).reverse) := by
      simp [initial, main, main_entry, Except.toOption]
    simpa [started, Except.toOption] using projected
  have saved : ReturnLit.ReturnLabel labels returnLabel := by
    rw [labelDefinitions]
    exact return_label left right
  let frames := [Frame.strongBind (wildcard .unit) savedReturn ∅, .annotations accesses]
  have boundary : ReturnLit.NoBoundary frames := by
    simp [frames, ReturnLit.NoBoundary, hasBoundary]
  have enterProcedure : Forced.Reaches (semanticFile left right) labels
      ⟨.effectExpr (procedureBody left right) ∅, [.annotations accesses], memory⟩
      ⟨.effectExpr (coreBody left right) ∅, frames, memory⟩ :=
    ReturnControl.sequence_forced [] (wildcard .unit) _ savedReturn ∅ _ _
  obtain ⟨finish, output, returned⟩ := core_body_forced left right bounded labels saved ∅ boundary memory
  exact ⟨start, labels, finish, started, entered.trans (enterProcedure.trans returned), output.trans stdout⟩

/-- All actual finite prefixes and infinite executions of the real startup
model satisfy the integer return specification. This is unbounded whole-main
Core semantics for the fixed constructed runtime, not a local-model shortcut. -/
theorem whole_main_satisfies (left right : Int) (bounded : Bounds left right)
    (enums : Map Sym IntegerType) (arguments : List String) :
    ∃ start labels, initial (semanticFile left right) enums arguments = .ok (start, labels) ∧
      Silmaril.Cerberus.Institution.Satisfies ⟨semanticFile left right, labels, start⟩
        (ElaborationTotal.returnsInteger (left + right)) := by
  obtain ⟨start, labels, finish, started, forced, stdout⟩ := whole_main_forced left right bounded enums arguments
  refine ⟨start, labels, started, ?_⟩
  intro behavior realized
  cases behavior with
  | finite actions state =>
    intro outcome halted
    have reachable := (Silmaril.Compiler.Category.Cerberus.Process.finite_iff_reaches
      (⟨semanticFile left right, labels, start⟩ : Silmaril.Cerberus.Institution.Model) state).mp ⟨actions, realized⟩
    have same := Forced.terminal_unique forced rfl reachable halted
    cases same
    exact ⟨Control.halt.inj halted.symm, stdout⟩
  | infinite states actions =>
    exact Forced.no_infinite forced rfl states actions realized.1 realized.2

/-- The exact independently fixed Source record uses the actual successful
Functions output proved for arbitrary source operands. -/
theorem actual_elaborates (left right : Int) : elaborate (source left right) = .ok (bindings left right) := by
  change (Functions.elaborate config Silmaril.Cerberus.Target.emptyEnvironment runtime
    (program left right) ⟨⟨[]⟩, 100, 1000⟩).1 = .ok (bindings left right)
  exact congrArg Prod.fst (functions_elaborate left right)

/-- The independently selected same Source has an actual startup model with
universal integer-return semantics; no source adequacy is a supplied premise. -/
theorem source_model (left right : Int) (bounded : Bounds left right) :
    ∃ model : Silmaril.Cerberus.Institution.Model, Elaborates (source left right) model ∧
      Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger (left + right)) := by
  obtain ⟨start, labels, started, correct⟩ := whole_main_satisfies left right bounded
    (Map.ofList (source left right).enumBindings) (source left right).arguments
  exact ⟨⟨semanticFile left right, labels, start⟩,
    ⟨bindings left right, actual_elaborates left right, rfl, started⟩, correct⟩

/-- Every model admitted by the existing actual Source elaboration relation
has the proved whole-main behavior; deterministic elaboration/startup fixes the
model rather than selecting a favorable model. -/
theorem every_source_model (left right : Int) (bounded : Bounds left right)
    (model : Silmaril.Cerberus.Institution.Model) (elaborated : Elaborates (source left right) model) :
    Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger (left + right)) := by
  obtain ⟨otherBindings, accepted, file, actualStart⟩ := elaborated
  have sameBindings : otherBindings = bindings left right :=
    Except.ok.inj (accepted.symm.trans (actual_elaborates left right))
  subst otherBindings
  obtain ⟨start, labels, started, correct⟩ := whole_main_satisfies left right bounded
    (Map.ofList (source left right).enumBindings) (source left right).arguments
  rw [file] at actualStart
  have pairEquality : (model.initialState, model.labels) = (start, labels) :=
    Except.ok.inj (actualStart.symm.trans started)
  have sameState : model.initialState = start := congrArg Prod.fst pairEquality
  have sameLabels : model.labels = labels := congrArg Prod.snd pairEquality
  have modelEquality : model = ⟨semanticFile left right, labels, start⟩ := by
    cases model with
    | mk program labels initialState =>
      cases file
      cases sameState
      cases sameLabels
      rfl
  exact modelEquality.symm ▸ correct

/-- Completed process observations of this actual source document are exactly
the modular C main exit status and empty output. This follows from the universal
whole-Core theorem and an actual completed path, not a bounded runner. -/
theorem source_process_exact (left right : Int) (bounded : Bounds left right)
    (observation : Silmaril.Compiler.Category.Cerberus.Process.Spec.Obs) :
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh (sourceDocument left right)
      (source left right).arguments observation ↔ observation = expectedExit left right := by
  obtain ⟨start, labels, finish, started, forced, stdout⟩ := whole_main_forced left right bounded
    (Map.ofList (source left right).enumBindings) (source left right).arguments
  have startup : Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart (sourceDocument left right)
      (source left right).arguments = .ok (start, labels) := by
    simpa [Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart, sourceDocument, document] using started
  have actual : Elaborates (source left right)
      (Silmaril.Compiler.Category.Cerberus.Process.model (sourceDocument left right) start labels) :=
    ⟨bindings left right, actual_elaborates left right, rfl, started⟩
  have correct := every_source_model left right bounded _ actual
  exact ReturnControl.integer_process_exact (sourceDocument left right) (source left right).arguments
    start labels startup (left + right) correct _ forced.erase rfl stdout observation

/-- Actual source UB is excluded by the all-behavior theorem of the same
source's successful elaboration/startup model. -/
theorem source_no_undefined_behaviour (left right : Int) (bounded : Bounds left right) :
    ¬ Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreUB (sourceDocument left right)
      (source left right).arguments := by
  obtain ⟨model, actual, correct⟩ := source_model left right bounded
  obtain ⟨otherBindings, accepted, file, started⟩ := actual
  have sameBindings : otherBindings = bindings left right :=
    Except.ok.inj (accepted.symm.trans (actual_elaborates left right))
  subst otherBindings
  have startup : Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart (sourceDocument left right)
      (source left right).arguments = .ok (model.initialState, model.labels) := by
    simpa [Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart, sourceDocument, document, file] using started
  have modelEquality : model = Silmaril.Compiler.Category.Cerberus.Process.model
      (sourceDocument left right) model.initialState model.labels := by
    cases model with
    | mk program labels initialState =>
      exact congrArg (fun program => Silmaril.Cerberus.Institution.Model.mk program labels initialState) file
  intro undefined
  obtain ⟨actions, state, location, reason, realized, halted⟩ :=
    (Silmaril.Compiler.Category.Cerberus.Process.coreUB_iff_realises_ub (sourceDocument left right)
      (source left right).arguments model.initialState model.labels startup).1 undefined
  have actualRealized : model.realises (.finite actions state) := modelEquality.symm ▸ realized
  have impossible := (correct (.finite actions state) actualRealized (.ub location reason) halted).1
  cases impossible

/-- Exact meaning in the existing native compiler source contract, retaining
its UB alternative and then excluding it by a derived whole-main theorem. -/
theorem source_behaviors_exact (left right : Int) (bounded : Bounds left right) (observation : Observation) :
    observation ∈ sourceBehaviors (source left right) ↔ observation ∈ specification left right := by
  rw [sourceBehaviors_iff (actual_elaborates left right)]
  change (Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreUB (sourceDocument left right) (source left right).arguments ∨
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh (sourceDocument left right) (source left right).arguments
      (observe observation)) ↔ observe observation = expectedExit left right
  rw [source_process_exact left right bounded]
  exact or_iff_right (source_no_undefined_behaviour left right bounded)

/-- The same actual whole-Core source model satisfies the existing projected
institution sentence, as well as the stronger full-state integer sentence. -/
theorem projected_source_model (left right : Int) (bounded : Bounds left right) :
    ∃ model : Silmaril.Cerberus.Institution.Model, Elaborates (source left right) model ∧
      Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger (left + right)) ∧
      Silmaril.Cerberus.Institution.Satisfies model (Institution.sentence (specification left right)) := by
  obtain ⟨model, elaborated, correct⟩ := source_model left right bounded
  refine ⟨model, elaborated, correct, (Institution.satisfies_sentence_iff _ _).2 ?_⟩
  rw [Institution.project_eq_sourceBehaviors elaborated]
  intro observation behavior
  exact (source_behaviors_exact left right bounded observation).1 behavior

end Silmaril.Compiler.Native.Correctness.AdditionMain
