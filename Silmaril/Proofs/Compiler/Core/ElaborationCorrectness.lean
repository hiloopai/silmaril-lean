module

public import Silmaril.Compiler.Core.ElaborationCorrectness.Defs
public import Silmaril.Cerberus.Elaboration.Scheduling.Thms

/-! Connecting actual typed-Ail literal-return translation to actual Core
reachability. Runtime recognition, target return type, integer bounds, source
fragment and elaboration context requirements remain explicit.
-/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationCorrectness
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

private theorem run_pure {α : Type} (value : α) (before : State.Context) :
    State.run (pure value : State.ElabM α) before = (.ok value, before) := rfl

private theorem run_bind {α β : Type} (action : State.ElabM α) (following : α → State.ElabM β)
    (before : State.Context) :
    State.run (action >>= following) before =
      match State.run action before with
      | (.ok value, after) => State.run (following value) after
      | (.error error, after) => (.error error, after) := by
  cases execution : action before with
  | mk outcome after =>
      cases outcome <;>
        simp [State.run, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
          bind, pure, StateT.bind, StateT.pure, execution]

private theorem run_map {α β : Type} (transform : α → β) (action : State.ElabM α)
    (before : State.Context) :
    State.run (transform <$> action) before =
      let (result, after) := State.run action before
      (result.map transform, after) := by
  cases execution : action before with
  | mk outcome after =>
      cases outcome <;>
        simp [State.run, ExceptT.run, ExceptT.mk, Functor.map, ExceptT.map,
          bind, pure, StateT.bind, StateT.pure, Except.map, execution]

private theorem run_get (before : State.Context) :
    State.run (get : State.ElabM State.Context) before = (.ok before, before) := rfl

private theorem run_set (before after : State.Context) :
    State.run (set after : State.ElabM Unit) before = (.ok (), after) := rfl

private theorem run_modify (update : State.Context → State.Context) (before : State.Context) :
    State.run (modify update : State.ElabM Unit) before = (.ok (), update before) := rfl

private theorem run_getEffects (before : State.Context) :
    State.run State.getEffects before = (.ok before.effects, before) := by
  simp only [State.getEffects, run_bind, run_get, run_pure]

private theorem run_modifyEffects (update : State.Effects → State.Effects) (before : State.Context) :
    State.run (State.modifyEffects update) before = (.ok (), {before with effects := update before.effects}) := by
  simp only [State.modifyEffects, run_modify]

private theorem run_visibleObjects (before : State.Context) :
    State.run State.getVisibleObjects before = (.ok before.effects.visibleObjects.flatten, before) := by
  simp only [State.getVisibleObjects, run_bind, run_getEffects, run_pure]

private theorem temporary_reset (before : State.Context)
    (empty : before.effects.temporaryObjects = []) :
    {before with effects := {before.effects with temporaryObjects := []}} = before := by
  rw [← empty]

private theorem integerLiteral_raw_type (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (location : Loc) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) :
    Silmaril.Cerberus.GeneralizedTypes.expressionType config types
      (.mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] location
        (.const (.integer (.iconstant number basis suffix)))) =
      .ok (.mk [.loc location] (.basic (.integer (.signed .int)))) := rfl

private theorem integerLiteral_type (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (location : Loc) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) :
    Silmaril.Cerberus.GeneralizedTypes.expressionType config types
      (integerLiteral location number basis suffix) =
      .ok (.mk [.loc location] (.basic (.integer (.signed .int)))) := rfl

private def literalEffect (location : Loc) (number : Int) : Effect :=
  .mk [.loc location, .expr, .value (.integer (.signed .int))]
    (.pure (Constants.loadedInteger number))

private theorem integerLiteral_expression (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (location : Loc) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before : State.Context) :
    State.run (Constants.expression config types (integerLiteral location number basis suffix)) before =
      (.ok (literalEffect location number), before) := by
  simp [integerLiteral, Constants.expression, integerLiteral_raw_type, Constants.targetResult,
    Except.mapError, Constants.liftResult, run_pure, Constants.marker, Constants.isPointer,
    Constants.translate_integer, Constants.integer_expression_annotations, literalEffect, Constants.loadedInteger]

private theorem integerLiteral_wrapped (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (location : Loc) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before : State.Context)
    (empty : before.effects.temporaryObjects = []) :
    State.run (Constants.wrappedExpression config types (integerLiteral location number basis suffix)) before =
      (.ok (.mk [.std "§6.5#2"] (.bound (literalEffect location number))), before) := by
  simp only [Constants.wrappedExpression, State.trackTemporaryObjects, run_bind, run_getEffects,
    empty, integerLiteral_expression, run_modifyEffects, temporary_reset before empty, run_pure]

private theorem integerLiteral_dispatch (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : List Runtime.Binding)
    (location : Loc) (number : Int) (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (aliases : Designators.Aliases) :
    Expressions.expression config types runtime (integerLiteral location number basis suffix) aliases =
      Constants.expression config types (integerLiteral location number basis suffix) := by
  rw [Expressions.expression.eq_def]
  rfl

private theorem integerLiteral_dispatch_wrapped (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : List Runtime.Binding)
    (location : Loc) (number : Int) (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix)
    (before : State.Context) (empty : before.effects.temporaryObjects = [])
    (aliases : Designators.Aliases) :
    State.run (Expressions.wrappedExpression config types runtime
      (integerLiteral location number basis suffix) aliases) before =
      (.ok (.mk [.std "§6.5#2"] (.bound (literalEffect location number))), before) := by
  simp only [Expressions.wrappedExpression, integerLiteral_dispatch, State.trackTemporaryObjects,
    run_bind, run_getEffects, empty, integerLiteral_expression, run_modifyEffects,
    temporary_reset before empty, run_pure]

private theorem wrapped_fresh (before : State.Context)
    (available : before.freshness.next ≤ before.freshness.maximum) :
    State.run (State.wrappedFreshSymbol (.loaded .integer)) before =
      (.ok ⟨⟨before.freshness.digest, before.freshness.next, .none⟩,
        symbolPattern ⟨before.freshness.digest, before.freshness.next, .none⟩ (.loaded .integer),
        symbolPure ⟨before.freshness.digest, before.freshness.next, .none⟩⟩,
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) := by
  simp only [State.wrappedFreshSymbol, State.wrappedFreshSymbolWith, State.freshDescription,
    run_bind, run_get, Freshness.description_of_bound before.freshness .none available,
    run_set, run_pure]

private theorem lifetime_run (label : Sym) (arguments : List Pure) (before : State.Context)
    (empty : before.effects.visibleObjects.flatten = []) :
    State.run (Statements.emptyLifetimeRun label arguments) before =
      (.ok (Construction.run label arguments), before) := by
  simp [Statements.emptyLifetimeRun, run_bind, run_visibleObjects, empty, run_pure]

private theorem loadedArithmetic_call (runtime : List Runtime.Binding)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1) runtime =
      some (conversion, .function resultType parameters body))
    (sourceAnnotations returnAnnotations : List Annot) (expression : Pure) :
    Conversion.loadedArithmetic runtime (.mk sourceAnnotations (.basic (.integer (.signed .int))))
      (.mk returnAnnotations (.basic (.integer (.signed .int)))) expression =
      .ok (call (.sym conversion)
        [ctype (.mk returnAnnotations (.basic (.integer (.signed .int)))), expression]) := by
  simp only [Conversion.loadedArithmetic, Runtime.standardCall, found, ailCtype]

private def returnExpressionCore (temporary label conversion : Sym)
    (expressionLocation : Loc) (returnAnnotations : List Annot) (number : Int) : Effect :=
  strongSequence (symbolPattern temporary (.loaded .integer))
    (.mk [.std "§6.5#2"] (.bound (literalEffect expressionLocation number)))
    (Construction.run label [call (.sym conversion)
      [ctype (.mk returnAnnotations (.basic (.integer (.signed .int)))), symbolPure temporary]])

private theorem returnExpression_run (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : List Runtime.Binding)
    (environment : Statements.Environment) (returnAnnotations : List Annot)
    (returnType : environment.returnType = .mk returnAnnotations (.basic (.integer (.signed .int))))
    (ordinary : environment.noreturn = false) (statementLocation location : Loc) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before : State.Context)
    (noObjects : before.effects.visibleObjects.flatten = [])
    (noTemporaries : before.effects.temporaryObjects = [])
    (available : before.freshness.next ≤ before.freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1) runtime =
      some (conversion, .function resultType parameters body)) (aliases : Designators.Aliases) :
    State.run (Statements.returnExpression config types runtime environment
      (integerLiteral location number basis suffix) statementLocation aliases) before =
      (.ok (returnExpressionCore ⟨before.freshness.digest, before.freshness.next, .none⟩
        environment.returnLabel conversion location returnAnnotations number),
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) := by
  simp [Statements.returnExpression, ordinary, Lifetimes.captureVisible,
    run_bind, run_map, Except.map, run_visibleObjects, noObjects,
    integerLiteral_type, Statements.liftError, Except.mapError, returnType, Statements.integerType,
    integerLiteral_dispatch_wrapped, noTemporaries, wrapped_fresh, available,
    loadedArithmetic_call runtime conversion resultType parameters body found, lifetime_run,
    returnExpressionCore]

/-- Exact successful output and state of the real signed-int literal return
translator, through the actual `Expressions` constant branch. The current
digest/history is an input; no AST maximum or fixture index is guessed. -/
theorem returnLiteral_run_withAliases (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : List Runtime.Binding)
    (aliases : Designators.Aliases)
    (environment : Statements.Environment) (returnAnnotations : List Annot)
    (returnType : environment.returnType = .mk returnAnnotations (.basic (.integer (.signed .int))))
    (ordinary : environment.noreturn = false) (statementLocation expressionLocation : Loc)
    (desugaring : Ail.DesugInfo) (attributes : Attributes) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before : State.Context)
    (noObjects : before.effects.visibleObjects.flatten = [])
    (noTemporaries : before.effects.temporaryObjects = [])
    (available : before.freshness.next ≤ before.freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1) runtime =
      some (conversion, .function resultType parameters body)) (sourceFunction : Option Sym := none) :
    State.run (Statements.translate config types runtime environment
      (returnLiteral statementLocation expressionLocation desugaring attributes number basis suffix)
      sourceFunction aliases) before =
      (.ok (returnCore ⟨before.freshness.digest, before.freshness.next, .none⟩
        environment.returnLabel conversion statementLocation expressionLocation attributes returnAnnotations number),
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) := by
  simp only [returnLiteral, Statements.translate, Statements.annotate, Statements.construct.eq_def,
    Scheduling.execute_defer, run_map,
    returnExpression_run config types runtime environment returnAnnotations returnType ordinary
      statementLocation expressionLocation number basis suffix before noObjects noTemporaries available
      conversion resultType parameters body found aliases, Except.map]
  rfl

/-- Compatibility interface using the original empty-alias input. -/
theorem returnLiteral_run (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : List Runtime.Binding)
    (environment : Statements.Environment) (returnAnnotations : List Annot)
    (returnType : environment.returnType = .mk returnAnnotations (.basic (.integer (.signed .int))))
    (ordinary : environment.noreturn = false) (statementLocation expressionLocation : Loc)
    (desugaring : Ail.DesugInfo) (attributes : Attributes) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before : State.Context)
    (noObjects : before.effects.visibleObjects.flatten = [])
    (noTemporaries : before.effects.temporaryObjects = [])
    (available : before.freshness.next ≤ before.freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1) runtime =
      some (conversion, .function resultType parameters body)) (sourceFunction : Option Sym := none) :
    State.run (Statements.translate config types runtime environment
      (returnLiteral statementLocation expressionLocation desugaring attributes number basis suffix)
      sourceFunction) before =
      (.ok (returnCore ⟨before.freshness.digest, before.freshness.next, .none⟩
        environment.returnLabel conversion statementLocation expressionLocation attributes returnAnnotations number),
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) :=
  returnLiteral_run_withAliases config types runtime [] environment returnAnnotations returnType ordinary
    statementLocation expressionLocation desugaring attributes number basis suffix before noObjects
    noTemporaries available conversion resultType parameters body found sourceFunction

private theorem returnCore_reaches {file : Dynamics.Program} {labels : Dynamics.Labels}
    (temporary label conversion parameter occurrence : Sym)
    (statementLocation expressionLocation : Loc) (attributes : Attributes)
    (returnAnnotations bodyAnnotations occurrenceAnnotations : List Annot) (number : Int)
    (same : occurrence.key = parameter.key)
    (recognized : Silmaril.Compile.Core.Verified.ConvInt.isConvLoadedInt file conversion = true)
    (bounds : Silmaril.Compile.Core.Verified.ConvInt.IsInt number)
    (environment : Dynamics.Env) (localFrames caller : List Dynamics.Frame)
    (localLabels : Dynamics.Labels) (memory : Mem.Concrete.State)
    (context : Dynamics.procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup label = some
      ([parameter], .mk bodyAnnotations (.pure (.mk occurrenceAnnotations () (.sym occurrence))))) :
    SeqReach.Reaches file labels
      ⟨.effectExpr (returnCore temporary label conversion statementLocation expressionLocation
        attributes returnAnnotations number) environment,
        localFrames ++ .procedureReturn localLabels :: caller, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), caller,
        SeqReach.focusMemory bodyAnnotations
          (SeqReach.focusMemory [.loc expressionLocation, .expr, .value (.integer (.signed .int))] memory)⟩ := by
  let annotations : List Annot := match attributes with
    | .mk [] => [.loc statementLocation, .stmt]
    | _ => [.loc statementLocation, .stmt, .attrs attributes]
  have shape : returnCore temporary label conversion statementLocation expressionLocation
      attributes returnAnnotations number =
      .mk annotations (.sseq (symbolPattern temporary (.loaded .integer))
        (.mk [.std "§6.5#2"] (.bound (literalEffect expressionLocation number)))
        (Construction.run label [call (.sym conversion)
          [ctype (.mk returnAnnotations (.basic (.integer (.signed .int)))), symbolPure temporary]])) := by
    cases attributes with
    | mk entries => cases entries <;> rfl
  rw [shape]
  exact ElaborationSemantics.constant_return_reaches annotations [] [.std "§6.5#2"]
    [.loc expressionLocation, .expr, .value (.integer (.signed .int))] [] [] [] []
    returnAnnotations [] bodyAnnotations occurrenceAnnotations temporary label conversion parameter occurrence
    same number recognized bounds environment localFrames caller localLabels memory context lookup

/-- Source/output correctness for the actual supported typed-Ail statement.
The premise is success of real translation, not equality to a prebuilt Core
program. It preserves the suspended caller and stdout under the displayed
runtime, integer-range, saved-label and procedure-context obligations. -/
theorem returnLiteral_success_reaches {file : Dynamics.Program} {labels : Dynamics.Labels}
    (config : Silmaril.Cerberus.Target.Config) (types : Silmaril.Cerberus.Target.Environment)
    (runtime : List Runtime.Binding) (elaborationEnvironment : Statements.Environment)
    (returnAnnotations : List Annot)
    (returnType : elaborationEnvironment.returnType =
      .mk returnAnnotations (.basic (.integer (.signed .int))))
    (ordinary : elaborationEnvironment.noreturn = false) (statementLocation expressionLocation : Loc)
    (desugaring : Ail.DesugInfo) (attributes : Attributes) (number : Int)
    (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (before after : State.Context) (core : Effect)
    (sourceFunction : Option Sym := none)
    (success : State.run (Statements.translate config types runtime elaborationEnvironment
      (returnLiteral statementLocation expressionLocation desugaring attributes number basis suffix)
      sourceFunction) before =
      (.ok core, after))
    (noObjects : before.effects.visibleObjects.flatten = [])
    (noTemporaries : before.effects.temporaryObjects = [])
    (available : before.freshness.next ≤ before.freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1) runtime =
      some (conversion, .function resultType parameters body))
    (recognized : Silmaril.Compile.Core.Verified.ConvInt.isConvLoadedInt file conversion = true)
    (bounds : Silmaril.Compile.Core.Verified.ConvInt.IsInt number)
    (parameter occurrence : Sym) (same : occurrence.key = parameter.key)
    (bodyAnnotations occurrenceAnnotations : List Annot) (environment : Dynamics.Env)
    (localFrames caller : List Dynamics.Frame) (localLabels : Dynamics.Labels) (memory : Mem.Concrete.State)
    (context : Dynamics.procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup elaborationEnvironment.returnLabel = some
      ([parameter], .mk bodyAnnotations (.pure (.mk occurrenceAnnotations () (.sym occurrence))))) :
    ∃ finish : Mem.Concrete.State, finish.stdout = memory.stdout ∧
      SeqReach.Reaches file labels
        ⟨.effectExpr core environment, localFrames ++ .procedureReturn localLabels :: caller, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), caller, finish⟩ := by
  have translated := returnLiteral_run config types runtime elaborationEnvironment returnAnnotations
    returnType ordinary statementLocation expressionLocation desugaring attributes number basis suffix
    before noObjects noTemporaries available conversion resultType parameters body found sourceFunction
  have output : core = returnCore ⟨before.freshness.digest, before.freshness.next, .none⟩
      elaborationEnvironment.returnLabel conversion statementLocation expressionLocation
      attributes returnAnnotations number :=
    Except.ok.inj (congrArg Prod.fst (success.symm.trans translated))
  let finish : Mem.Concrete.State := SeqReach.focusMemory bodyAnnotations
    (SeqReach.focusMemory [.loc expressionLocation, .expr, .value (.integer (.signed .int))] memory)
  have stdout : finish.stdout = memory.stdout := by
    simp only [finish, SeqReach.focusMemory_stdout]
  have execution : SeqReach.Reaches file labels
      ⟨.effectExpr core environment, localFrames ++ .procedureReturn localLabels :: caller, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), caller, finish⟩ := by
    rw [output]
    exact returnCore_reaches _ _ _ parameter occurrence statementLocation expressionLocation
      attributes returnAnnotations bodyAnnotations occurrenceAnnotations number same recognized bounds
      environment localFrames caller localLabels memory context lookup
  exact ⟨finish, stdout, execution⟩

end Silmaril.Compiler.Core.ElaborationCorrectness
