module

public import Silmaril.Compiler.Core.SignedArithmetic.Main.Defs
public import Silmaril.Cerberus.Elaboration.Scheduling.Thms
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Core.SignedArithmetic.Main
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Native.Correctness
open Silmaril.Cerberus.Core
open Construction
attribute [local cbv_eval] String.toUTF8_eq_toByteArray
attribute [local cbv_eval] Std.ExtDHashMap.Const.get?_insert Std.ExtDHashMap.Const.get?_empty

private theorem track_run {α : Type} (action : State.ElabM α) (context after : State.Context) (value : α)
    (beforeEmpty : context.effects.temporaryObjects = []) (afterEmpty : after.effects.temporaryObjects = [])
    (ran : State.run action context = (.ok value, after)) :
    State.run (State.trackTemporaryObjects action) context = (.ok ([], value), after) := by
  have getBefore : State.run State.getEffects context = (.ok context.effects, context) := rfl
  rw [State.trackTemporaryObjects, run_bind _ _ _ _ _ getBefore, beforeEmpty]
  rw [run_bind _ _ _ _ _ ran]
  have getAfter : State.run State.getEffects after = (.ok after.effects, after) := rfl
  rw [run_bind _ _ _ _ _ getAfter]
  have reset : ({after with effects := {after.effects with temporaryObjects := []}} : State.Context) = after := by
    conv_lhs => rw [← afterEmpty]
  change (Except.ok (after.effects.temporaryObjects, value), {after with effects := {after.effects with temporaryObjects := []}}) = _
  rw [afterEmpty, reset]

theorem wrapped_elaborates (expression : Expression) (context : State.Context)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum + 1)
    (empty : context.effects.temporaryObjects = []) :
    State.run (Expressions.wrappedExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail) context =
      (.ok (.mk [.std "§6.5#2"] (.bound (expression.core context.freshness.digest context.freshness.next))),
        advance context (5 * expression.operations)) := by
  have tracked : State.run (State.trackTemporaryObjects
      (Expressions.expression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail)) context =
      (.ok ([], expression.core context.freshness.digest context.freshness.next), advance context (5 * expression.operations)) :=
    track_run _ context _ _ empty empty (expression_elaborates expression context room)
  rw [Expressions.wrappedExpression, run_bind _ _ _ _ _ tracked]
  rfl

private theorem capture_visible_run (context : State.Context)
    (empty : context.effects.visibleObjects.flatten = []) :
    State.run Lifetimes.captureVisible context = (.ok [], context) := by
  have visible : State.run State.getVisibleObjects context = (.ok context.effects.visibleObjects.flatten, context) := rfl
  rw [Lifetimes.captureVisible, run_bind _ _ _ _ _ visible, empty]
  rfl

private theorem loaded_conversion (symbol : Sym) :
    Conversion.loadedArithmetic runtime.stdlib intType mainType (symbolPure symbol) =
      .ok (call (.sym Literal42.conversion) [ctype mainType, symbolPure symbol]) := by
  cbv

private theorem empty_run (context : State.Context) (label : Sym) (arguments : List Pure)
    (empty : context.effects.visibleObjects.flatten = []) :
    State.run (Statements.emptyLifetimeRun label arguments) context = (.ok (Construction.run label arguments), context) := by
  have visible : State.run State.getVisibleObjects context = (.ok context.effects.visibleObjects.flatten, context) := rfl
  rw [Statements.emptyLifetimeRun, run_bind _ _ _ _ _ visible, empty]
  rfl

theorem return_elaborates (expression : Expression) (context : State.Context) (label : Sym)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum)
    (temporaries : context.effects.temporaryObjects = []) (visible : context.effects.visibleObjects.flatten = []) :
    State.run (Statements.returnExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
      ⟨mainType, label, false⟩ expression.ail) context =
      (.ok (returnCore expression context.freshness.digest context.freshness.next label),
        advance context (5 * expression.operations + 1)) := by
  have captured : State.run Lifetimes.captureVisible context = (.ok [], context) := capture_visible_run context visible
  unfold Statements.returnExpression
  dsimp only
  simp only [Bool.false_eq_true, ite_false]
  rw [run_bind _ _ _ _ _ captured]
  rw [actual_type expression]
  have bothInteger : (Statements.integerType intType && Statements.integerType mainType) = true := rfl
  simp only [Except.mapError, Statements.liftError, pure_bind, bothInteger, ite_true]
  have wrapped : State.run
      (Expressions.wrappedExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail) context =
      (.ok (.mk [.std "§6.5#2"] (.bound (expression.core context.freshness.digest context.freshness.next))),
        advance context (5 * expression.operations)) :=
    wrapped_elaborates expression context (by omega) temporaries
  rw [run_bind _ _ _ _ _ wrapped]
  have allocated : State.run (State.wrappedFreshSymbol (.loaded .integer)) (advance context (5 * expression.operations)) =
      (.ok ⟨fresh context.freshness.digest (context.freshness.next + 5 * expression.operations),
        symbolPattern (fresh context.freshness.digest (context.freshness.next + 5 * expression.operations)) (.loaded .integer),
        symbolPure (fresh context.freshness.digest (context.freshness.next + 5 * expression.operations))⟩,
        advance (advance context (5 * expression.operations)) 1) :=
    fresh_symbol (advance context (5 * expression.operations)) _ room
  rw [run_bind _ _ _ _ _ allocated]
  rw [loaded_conversion]
  simp only [pure_bind, List.isEmpty_nil, ite_true]
  have transfer : State.run (Statements.emptyLifetimeRun label
      [call (.sym Literal42.conversion) [ctype mainType,
        symbolPure (fresh context.freshness.digest (context.freshness.next + 5 * expression.operations))]])
      (advance (advance context (5 * expression.operations)) 1) =
      (.ok (Construction.run label [call (.sym Literal42.conversion) [ctype mainType,
        symbolPure (fresh context.freshness.digest (context.freshness.next + 5 * expression.operations))]]),
        advance (advance context (5 * expression.operations)) 1) :=
    empty_run _ label _ visible
  rw [run_bind _ _ _ _ _ transfer]
  simp only [advance_add]
  rfl

private def blockContext (context : State.Context) : State.Context :=
  {context with effects := {context.effects with visibleObjects := [] :: context.effects.visibleObjects, compoundLiterals := []}}

private theorem block_run {α : Type} (action : State.ElabM α) (context : State.Context) (count : Nat) (value : α)
    (ran : State.run action (blockContext context) = (.ok value, advance (blockContext context) count)) :
    State.run (State.withBlockObjects [] action) context = (.ok ([], [], value), advance context count) := by
  have before : State.run State.getEffects context = (.ok context.effects, context) := rfl
  rw [State.withBlockObjects, run_bind _ _ _ _ _ before]
  simp only [State.allocateConstAliases, pure_bind, List.foldl_nil, List.map_nil]
  have entered : State.run (State.modifyEffects fun effects => {effects with
      visibleObjectTypes := effects.visibleObjectTypes, visibleObjects := [] :: effects.visibleObjects,
      compoundLiterals := []}) context = (.ok (), blockContext context) := rfl
  rw [run_bind _ _ _ _ _ entered, run_bind _ _ _ _ _ ran]
  have after : State.run State.getEffects (advance (blockContext context) count) =
      (.ok (advance (blockContext context) count).effects, advance (blockContext context) count) := rfl
  rw [run_bind _ _ _ _ _ after]
  rfl

private theorem body_action (expression : Expression) (label : Sym) :
    Statements.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
      ⟨mainType, label, false⟩ (body expression) (some (Literal42.sym 1 "main")) =
      (do
        let (_, compounds, returns) ← State.withBlockObjects [] (do
          let returned ← Statements.returnExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
            ⟨mainType, label, false⟩ expression.ail
          pure [addLocation .unknown (addStatement returned)])
        unless compounds.isEmpty do throw (.message "block compound-literal lifetimes are not ported")
        pure (addLocation .unknown (addStatement (Statements.unitSequence returns skip)))) := by
  have executePure {α : Type} (action : State.ElabM α) : Scheduling.execute (pure action : Scheduling.Build (State.ElabM α)) = action :=
    Scheduling.execute_defer action
  rw [Statements.translate, body, Statements.construct.eq_def]
  dsimp only
  simp only [Scheduling.mapM, Scheduling.buildMapAt, List.attach_cons, List.attach_nil,
    Scheduling.map, Scheduling.bind, Scheduling.returnValue, Scheduling.defer]
  rw [Statements.construct.eq_def]
  dsimp only
  simp only [Nat.zero_lt_succ, ite_true, List.map_nil, Scheduling.buildMapAt, Scheduling.defer,
    bind_pure_comp, map_pure]
  simp only [executePure, Scheduling.sequenceActions, List.isEmpty_nil, ite_true,
    Statements.annotate, addAttributes]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  split <;> simp_all [Statements.annotate, addAttributes]

theorem body_elaborates (expression : Expression) (context : State.Context) (label : Sym)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum)
    (temporaries : context.effects.temporaryObjects = []) (visible : context.effects.visibleObjects.flatten = []) :
    State.run (Statements.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
      ⟨mainType, label, false⟩ (body expression) (some (Literal42.sym 1 "main"))) context =
      (.ok (bodyCore expression context.freshness.digest context.freshness.next label),
        advance context (5 * expression.operations + 1)) := by
  let count := 5 * expression.operations + 1
  let returned := returnCore expression context.freshness.digest context.freshness.next label
  let returnAction : State.ElabM (List Effect) := do
    let result ← Statements.returnExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
      ⟨mainType, label, false⟩ expression.ail
    pure [addLocation .unknown (addStatement result)]
  have actualReturn : State.run
      (Statements.returnExpression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
        ⟨mainType, label, false⟩ expression.ail) (blockContext context) =
      (.ok returned, advance (blockContext context) count) :=
    return_elaborates expression (blockContext context) label room temporaries
      (by simpa only [blockContext, List.flatten_cons, List.nil_append] using visible)
  have translated : State.run returnAction (blockContext context) =
      (.ok [addLocation .unknown (addStatement returned)], advance (blockContext context) count) := by
    dsimp only [returnAction]
    rw [run_bind _ _ _ _ _ actualReturn]
    rfl
  have scopeRun : State.run (State.withBlockObjects [] returnAction) context =
      (.ok ([], [], [addLocation .unknown (addStatement returned)]), advance context count) :=
    block_run returnAction context count _ translated
  rw [body_action, run_bind _ _ _ _ _ scopeRun]
  rfl

private theorem declaration_action (expression : Expression) :
    Functions.declaration config Silmaril.Cerberus.Target.emptyEnvironment runtime (program expression) {}
      (Literal42.sym 1 "main", .unknown, .mk [],
        .function true (⟨false, false, false⟩, mainType) [] false false false) =
      (do
        let label ← Functions.freshReturnLabel
        let translated ← Statements.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
          ⟨mainType, label, false⟩ (body expression) (some (Literal42.sym 1 "main"))
        let temporary ← State.freshDescription .none
        pure (Functions.Declarations.mk []
          [(Literal42.sym 1 "main", .procedure .unknown (some 7) (.loaded .integer) []
            (strongSequence (wildcard .unit) translated
              (Functions.returnSave (some (Literal42.sym 1 "main")) (Literal42.sym 1 "main") label temporary
                .unknown mainType (.loaded .integer))))]
          [(Literal42.sym 1 "main", .unknown, .mk [], mainType, [], false, true)])) := by
  rfl

private theorem label_run (context : State.Context) (room : context.freshness.next ≤ context.freshness.maximum) :
    State.run Functions.freshReturnLabel context =
      (.ok ⟨context.freshness.digest, context.freshness.next, .id s!"ret_{context.freshness.next}"⟩, advance context 1) := by
  have allocated : Freshness.integer context.freshness =
      .ok (context.freshness.next, {context.freshness with next := context.freshness.next + 1}) := by
    simp [Freshness.integer, room]
  dsimp only [State.run, Functions.freshReturnLabel, State.freshInteger,
    ExceptT.run, Bind.bind, Pure.pure, MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw, Functor.map, ExceptT.map, StateT.map,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, StateT.bind, StateT.pure, StateT.get, StateT.set]
  rw [allocated]
  rfl

private theorem description_run (context : State.Context)
    (room : context.freshness.next ≤ context.freshness.maximum) :
    State.run (State.freshDescription .none) context =
      (.ok (fresh context.freshness.digest context.freshness.next), advance context 1) := by
  have allocated : Freshness.description .none context.freshness =
      .ok (fresh context.freshness.digest context.freshness.next,
        {context.freshness with next := context.freshness.next + 1}) := by
    simp [Freshness.description, Freshness.integer, room, fresh]
  dsimp only [State.run, State.freshDescription, ExceptT.run, Bind.bind, Pure.pure,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw, Functor.map, ExceptT.map, StateT.map,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, StateT.bind, StateT.pure, StateT.get, StateT.set]
  rw [allocated]
  rfl

private theorem declaration_run (expression : Expression) :
    State.run (Functions.declaration config Silmaril.Cerberus.Target.emptyEnvironment runtime (program expression) {}
      (Literal42.sym 1 "main", .unknown, .mk [],
        .function true (⟨false, false, false⟩, mainType) [] false false false))
        (State.initial (freshness expression) .normal "Driver") =
      (.ok (Functions.Declarations.mk [] (bindings expression).funs (bindings expression).funInfo),
        State.initial ⟨⟨[]⟩, 103 + 5 * expression.operations, (freshness expression).maximum⟩ .normal "Driver") := by
  let context := State.initial (freshness expression) .normal "Driver"
  have label : State.run Functions.freshReturnLabel context = (.ok returnLabel, advance context 1) :=
    label_run context (by change 100 ≤ 102 + 5 * expression.operations; omega)
  have bodyRun : State.run (Statements.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
      ⟨mainType, returnLabel, false⟩ (body expression) (some (Literal42.sym 1 "main"))) (advance context 1) =
      (.ok (coreBody expression), advance (advance context 1) (5 * expression.operations + 1)) :=
    body_elaborates expression (advance context 1) returnLabel
      (by change 101 + 5 * expression.operations ≤ 102 + 5 * expression.operations; omega) rfl rfl
  have temporary : State.run (State.freshDescription .none)
      (advance (advance context 1) (5 * expression.operations + 1)) =
      (.ok (savedSymbol expression), advance (advance (advance context 1) (5 * expression.operations + 1)) 1) := by
    have raw := description_run (advance (advance context 1) (5 * expression.operations + 1))
      (by change 100 + 1 + (5 * expression.operations + 1) ≤ 102 + 5 * expression.operations; omega)
    have index : (advance (advance context 1) (5 * expression.operations + 1)).freshness.next =
        102 + 5 * expression.operations := by
      change 100 + 1 + (5 * expression.operations + 1) = 102 + 5 * expression.operations
      omega
    have digest : (advance (advance context 1) (5 * expression.operations + 1)).freshness.digest = ⟨[]⟩ := rfl
    simpa only [savedSymbol, index, digest] using raw
  rw [declaration_action, run_bind _ _ _ _ _ label, run_bind _ _ _ _ _ bodyRun,
    run_bind _ _ _ _ _ temporary]
  simp only [advance_add]
  have count : 1 + (5 * expression.operations + 1) + 1 = 3 + 5 * expression.operations := by omega
  rw [count]
  have finalIndex : 100 + (3 + 5 * expression.operations) = 103 + 5 * expression.operations := by omega
  simp only [advance, context, State.initial, freshness, finalIndex]
  rfl

private theorem translation_run (expression : Expression) :
    State.run (Functions.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime (program expression))
      (State.initial (freshness expression) .normal "Driver") =
      (.ok (bindings expression),
        State.initial ⟨⟨[]⟩, 103 + 5 * expression.operations, (freshness expression).maximum⟩ .normal "Driver") := by
  let context := State.initial (freshness expression) .normal "Driver"
  let final := State.initial ⟨⟨[]⟩, 103 + 5 * expression.operations, (freshness expression).maximum⟩ .normal "Driver"
  have convention : State.run State.getCallingConvention context = (.ok .normal, context) := rfl
  unfold Functions.translate
  rw [run_bind _ _ _ _ _ convention]
  simp only [decide_true, ite_true]
  have declarations : (program expression).2.declarations.reverse =
      [(Literal42.sym 1 "main", .unknown, .mk [],
        .function true (⟨false, false, false⟩, mainType) [] false false false)] := rfl
  rw [declarations]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [run_bind _ _ _ _ _ (declaration_run expression)]
  have effects : State.run State.getEffects final = (.ok (State.initialEffects .normal), final) := rfl
  rw [run_bind _ _ _ _ _ effects]
  simp only [State.initialEffects, List.isEmpty_nil, ite_true]
  simp only [Functions.liftError, GlobalOrder.mergeIndependent, GlobalOrder.uniqueKeys, ↓reduceIte,
    List.isEmpty_iff, bind_pure_comp, List.forIn_nil, List.mergeSort_nil, map_pure, program, AdditionSource.program,
    Silmaril.Compiler.Core.ElaborationProcess.LiteralMain.program, LiteralEmission.literal, body, List.map_nil, bindings,
    AdditionSource.bindings, AdditionSource.intType, List.mergeSort_singleton, Functions.externalKind, List.map_cons]
  rfl

/-- The actual complete Functions dispatcher succeeds from the source-fixed
host freshness, including label, arithmetic, return temporary and save symbol. -/
theorem functions_elaborate (expression : Expression) :
    Functions.elaborate config Silmaril.Cerberus.Target.emptyEnvironment runtime (program expression) (freshness expression) =
      (.ok (bindings expression),
        State.initial ⟨⟨[]⟩, 103 + 5 * expression.operations, (freshness expression).maximum⟩ .normal "Driver") := by
  rw [Functions.elaborate, State.runErrors, run_bind _ _ _ _ _ (translation_run expression)]
  rfl

theorem runtime_provided (expression : Expression) : RuntimeProvided (semanticFile expression) := rfl

theorem main_entry (expression : Expression) :
    (semanticFile expression).funs.lookup (Literal42.sym 1 "main") =
      some (.procedure .unknown (some 7) (.loaded .integer) [] (procedureBody expression)) := by
  cbv

theorem conversion_recognized (expression : Expression) :
    ConvInt.isConvLoadedInt (semanticFile expression) Literal42.conversion = true := by
  cbv

theorem body_save_free (expression : Expression) : ReturnLit.saveFree (coreBody expression) = true := rfl

theorem return_label (expression : Expression) :
    ReturnLit.ReturnLabel (Map.ofList (saves (procedureBody expression)).reverse) returnLabel :=
  ReturnLit.returnLabel_body rfl (body_save_free expression)

theorem wrapped_core_reaches (expression : Expression) (bounded : expression.Bounded)
    (labels : Labels) (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (wrappedCore expression) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), frames, focused memory⟩ := by
  have enter : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (wrappedCore expression) environment, frames, memory⟩
      ⟨.effectExpr (expression.core ⟨[]⟩ 101) environment, .bound :: frames, memory⟩ := by
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [wrappedCore, request, requestAux, awaitsScheduling]
  have computed : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (expression.core ⟨[]⟩ 101) environment, .bound :: frames, memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), expression.resultFrames ++ .bound :: frames, focused memory⟩ :=
    core_reaches (semanticFile expression) (runtime_provided expression) labels environment ⟨[]⟩ expression bounded
      101 memory (.bound :: frames)
  have leave : Forced.Reaches (semanticFile expression) labels
      ⟨.value (.loaded (.specified (.integer expression.value))), expression.resultFrames ++ .bound :: frames, focused memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), frames, focused memory⟩ := by
    cases expression <;> apply Forced.next (by intro outcome impossible; cases impossible) <;>
      simp [Expression.resultFrames, request, requestAux, awaitsScheduling]
  exact enter.trans (computed.trans leave)

theorem core_body_forced (expression : Expression) (bounded : expression.Bounded) (labels : Labels)
    (saved : ReturnLit.ReturnLabel labels returnLabel) (environment : Env) {frames : List Frame}
    (boundary : ReturnLit.NoBoundary frames) (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches (semanticFile expression) labels
        ⟨.effectExpr (coreBody expression) environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer expression.value)))), [], finish⟩ := by
  let statementFrames := Frame.strongBind (wildcard .unit) skip environment :: frames
  let transfer := ReturnControl.convertedReturn returnLabel Literal42.conversion (resultSymbol expression)
  let resultPattern := symbolPattern (resultSymbol expression) (.loaded .integer)
  let resultFrames := Frame.strongBind resultPattern transfer environment :: statementFrames
  let extended := extendEnv [(resultSymbol expression, .loaded (.specified (.integer expression.value)))] environment
  have enterBody : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (coreBody expression) environment, frames, memory⟩
      ⟨.effectExpr (coreReturn expression) environment, statementFrames, memory⟩ :=
    ReturnControl.sequence_forced [.loc .unknown, .stmt] (wildcard .unit) _ _ _ _ _
  have enterReturn : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (coreReturn expression) environment, statementFrames, memory⟩
      ⟨.effectExpr (wrappedCore expression) environment, resultFrames, memory⟩ :=
    ReturnControl.sequence_forced [.loc .unknown, .stmt] resultPattern _ transfer _ _ _
  have computed : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (wrappedCore expression) environment, resultFrames, memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), resultFrames, focused memory⟩ :=
    wrapped_core_reaches expression bounded labels environment resultFrames memory
  have bindResult : Forced.Reaches (semanticFile expression) labels
      ⟨.value (.loaded (.specified (.integer expression.value))), resultFrames, focused memory⟩
      ⟨.effectExpr transfer extended, statementFrames, focused memory⟩ := by
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, resultFrames, resultPattern, matchPattern,
      symbolPattern, symbolPatternWith, extended]
  have observed : extended.lookup (resultSymbol expression) = some (.loaded (.specified (.integer expression.value))) :=
    ConvInt.lookup_one rfl
  have resultBound : ConvInt.IsInt expression.value := by
    have valueBound : LiteralEmission.IsInt32 expression.value := bounded_value expression bounded
    exact ⟨valueBound.1, by have upper := valueBound.2; omega⟩
  have statementBoundary : ReturnLit.NoBoundary statementFrames := ReturnLit.noBoundary_cons boundary trivial
  obtain ⟨finish, stdout, returned⟩ := ReturnControl.converted_return_forced returnLabel returnLabel
    Literal42.conversion (resultSymbol expression) rfl saved (conversion_recognized expression) expression.value resultBound
    extended observed statementBoundary (focused memory)
  exact ⟨finish, stdout.trans (DiagnosticOperands.focused_stdout memory),
    enterBody.trans (enterReturn.trans (computed.trans (bindResult.trans returned)))⟩

theorem whole_main_forced (expression : Expression) (bounded : expression.Bounded)
    (enums : Map Sym IntegerType) (arguments : List String) :
    ∃ start labels finish, initial (semanticFile expression) enums arguments = .ok (start, labels) ∧
      Forced.Reaches (semanticFile expression) labels start
        ⟨.halt (.defined (.loaded (.specified (.integer expression.value)))), [], finish⟩ ∧ finish.stdout = "" := by
  have main : (semanticFile expression).main = some (Literal42.sym 1 "main") := rfl
  have noDefinitions : ∀ entry ∈ (semanticFile expression).globs, ∀ base value,
      entry.2 ≠ .definition base value := by
    intro entry member
    change entry ∈ [] at member
    cases member
  obtain ⟨start, labels, memory, accesses, started, stdout, entered⟩ := ElaborationTotal.initial_forced_body
    (semanticFile expression) enums arguments noDefinitions main (main_entry expression)
  have labelDefinitions : labels = Map.ofList (saves (procedureBody expression)).reverse := by
    have projected : (initial (semanticFile expression) enums arguments).toOption.map Prod.snd =
        some (Map.ofList (saves (procedureBody expression)).reverse) := by
      simp [initial, main, main_entry, Except.toOption]
    simpa [started, Except.toOption] using projected
  have saved : ReturnLit.ReturnLabel labels returnLabel := labelDefinitions.symm ▸ return_label expression
  let frames := [Frame.strongBind (wildcard .unit) (savedReturn expression) ∅, .annotations accesses]
  have boundary : ReturnLit.NoBoundary frames := by simp [frames, ReturnLit.NoBoundary, hasBoundary]
  have enterProcedure : Forced.Reaches (semanticFile expression) labels
      ⟨.effectExpr (procedureBody expression) ∅, [.annotations accesses], memory⟩
      ⟨.effectExpr (coreBody expression) ∅, frames, memory⟩ :=
    ReturnControl.sequence_forced [] (wildcard .unit) _ (savedReturn expression) ∅ _ _
  obtain ⟨finish, output, returned⟩ := core_body_forced expression bounded labels saved ∅ boundary memory
  exact ⟨start, labels, finish, started, entered.trans (enterProcedure.trans returned), output.trans stdout⟩

theorem whole_main_satisfies (expression : Expression) (bounded : expression.Bounded)
    (enums : Map Sym IntegerType) (arguments : List String) :
    ∃ start labels, initial (semanticFile expression) enums arguments = .ok (start, labels) ∧
      Silmaril.Cerberus.Institution.Satisfies ⟨semanticFile expression, labels, start⟩
        (ElaborationTotal.returnsInteger expression.value) := by
  obtain ⟨start, labels, finish, started, forced, stdout⟩ := whole_main_forced expression bounded enums arguments
  refine ⟨start, labels, started, ?_⟩
  intro behavior realized
  cases behavior with
  | finite actions state =>
    intro outcome halted
    have reachable := (Silmaril.Compiler.Category.Cerberus.Process.finite_iff_reaches
      (⟨semanticFile expression, labels, start⟩ : Silmaril.Cerberus.Institution.Model) state).mp ⟨actions, realized⟩
    have same := Forced.terminal_unique forced rfl reachable halted
    cases same
    exact ⟨Control.halt.inj halted.symm, stdout⟩
  | infinite states actions => exact Forced.no_infinite forced rfl states actions realized.1 realized.2

/-- The exact independently fixed Source record uses the actual successful
Functions output proved for arbitrary source operands. -/
theorem actual_elaborates (expression : Expression) : elaborate (source expression) = .ok (bindings expression) := by
  change (Functions.elaborate config Silmaril.Cerberus.Target.emptyEnvironment runtime
    (program expression) (freshness expression)).1 = .ok (bindings expression)
  exact congrArg Prod.fst (functions_elaborate expression)

/-- The independently selected same Source has an actual startup model with
universal integer-return semantics; no source adequacy is a supplied premise. -/
theorem source_model (expression : Expression) (bounded : expression.Bounded) :
    ∃ model : Silmaril.Cerberus.Institution.Model, Elaborates (source expression) model ∧
      Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger expression.value) := by
  obtain ⟨start, labels, started, correct⟩ := whole_main_satisfies expression bounded
    (Map.ofList (source expression).enumBindings) (source expression).arguments
  exact ⟨⟨semanticFile expression, labels, start⟩,
    ⟨bindings expression, actual_elaborates expression, rfl, started⟩, correct⟩

/-- Every model admitted by the existing actual Source elaboration relation
has the proved whole-main behavior; deterministic elaboration/startup fixes the
model rather than selecting a favorable model. -/
theorem every_source_model (expression : Expression) (bounded : expression.Bounded)
    (model : Silmaril.Cerberus.Institution.Model) (elaborated : Elaborates (source expression) model) :
    Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger expression.value) := by
  obtain ⟨otherBindings, accepted, file, actualStart⟩ := elaborated
  have sameBindings : otherBindings = bindings expression :=
    Except.ok.inj (accepted.symm.trans (actual_elaborates expression))
  subst otherBindings
  obtain ⟨start, labels, started, correct⟩ := whole_main_satisfies expression bounded
    (Map.ofList (source expression).enumBindings) (source expression).arguments
  rw [file] at actualStart
  have pairEquality : (model.initialState, model.labels) = (start, labels) :=
    Except.ok.inj (actualStart.symm.trans started)
  have sameState : model.initialState = start := congrArg Prod.fst pairEquality
  have sameLabels : model.labels = labels := congrArg Prod.snd pairEquality
  have modelEquality : model = ⟨semanticFile expression, labels, start⟩ := by
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
theorem source_process_exact (expression : Expression) (bounded : expression.Bounded)
    (observation : Silmaril.Compiler.Category.Cerberus.Process.Spec.Obs) :
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh (sourceDocument expression)
      (source expression).arguments observation ↔ observation = expectedExit expression := by
  obtain ⟨start, labels, finish, started, forced, stdout⟩ := whole_main_forced expression bounded
    (Map.ofList (source expression).enumBindings) (source expression).arguments
  have startup : Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart (sourceDocument expression)
      (source expression).arguments = .ok (start, labels) := by
    simpa [Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart, sourceDocument, document] using started
  have actual : Elaborates (source expression)
      (Silmaril.Compiler.Category.Cerberus.Process.model (sourceDocument expression) start labels) :=
    ⟨bindings expression, actual_elaborates expression, rfl, started⟩
  have correct := every_source_model expression bounded _ actual
  exact ReturnControl.integer_process_exact (sourceDocument expression) (source expression).arguments
    start labels startup expression.value correct _ forced.erase rfl stdout observation

/-- Actual source UB is excluded by the all-behavior theorem of the same
source's successful elaboration/startup model. -/
theorem source_no_undefined_behaviour (expression : Expression) (bounded : expression.Bounded) :
    ¬ Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreUB (sourceDocument expression)
      (source expression).arguments := by
  obtain ⟨model, actual, correct⟩ := source_model expression bounded
  obtain ⟨otherBindings, accepted, file, started⟩ := actual
  have sameBindings : otherBindings = bindings expression :=
    Except.ok.inj (accepted.symm.trans (actual_elaborates expression))
  subst otherBindings
  have startup : Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart (sourceDocument expression)
      (source expression).arguments = .ok (model.initialState, model.labels) := by
    simpa [Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart, sourceDocument, document, file] using started
  have modelEquality : model = Silmaril.Compiler.Category.Cerberus.Process.model
      (sourceDocument expression) model.initialState model.labels := by
    cases model with
    | mk program labels initialState =>
      exact congrArg (fun program => Silmaril.Cerberus.Institution.Model.mk program labels initialState) file
  intro undefined
  obtain ⟨actions, state, location, reason, realized, halted⟩ :=
    (Silmaril.Compiler.Category.Cerberus.Process.coreUB_iff_realises_ub (sourceDocument expression)
      (source expression).arguments model.initialState model.labels startup).1 undefined
  have actualRealized : model.realises (.finite actions state) := modelEquality.symm ▸ realized
  have impossible := (correct (.finite actions state) actualRealized (.ub location reason) halted).1
  cases impossible

/-- Exact meaning in the existing native compiler source contract, retaining
its UB alternative and then excluding it by a derived whole-main theorem. -/
theorem source_behaviors_exact (expression : Expression) (bounded : expression.Bounded) (observation : Observation) :
    observation ∈ sourceBehaviors (source expression) ↔ observation ∈ specification expression := by
  rw [sourceBehaviors_iff (actual_elaborates expression)]
  change (Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreUB (sourceDocument expression) (source expression).arguments ∨
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh (sourceDocument expression) (source expression).arguments
      (observe observation)) ↔ observe observation = expectedExit expression
  rw [source_process_exact expression bounded]
  exact or_iff_right (source_no_undefined_behaviour expression bounded)

/-- The same actual whole-Core source model satisfies the existing projected
institution sentence, as well as the stronger full-state integer sentence. -/
theorem projected_source_model (expression : Expression) (bounded : expression.Bounded) :
    ∃ model : Silmaril.Cerberus.Institution.Model, Elaborates (source expression) model ∧
      Silmaril.Cerberus.Institution.Satisfies model (ElaborationTotal.returnsInteger expression.value) ∧
      Silmaril.Cerberus.Institution.Satisfies model (Institution.sentence (specification expression)) := by
  obtain ⟨model, elaborated, correct⟩ := source_model expression bounded
  refine ⟨model, elaborated, correct, (Institution.satisfies_sentence_iff _ _).2 ?_⟩
  rw [Institution.project_eq_sourceBehaviors elaborated]
  intro observation behavior
  exact (source_behaviors_exact expression bounded observation).1 behavior


end Silmaril.Compiler.Core.SignedArithmetic.Main
