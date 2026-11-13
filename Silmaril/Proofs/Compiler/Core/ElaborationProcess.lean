module

public import Silmaril.Compiler.Core.ElaborationProcess.Defs
public import Init.Data.List.Sort.Lemmas
public import Silmaril.Compiler.Core.ElaborationCorrectness.Thms
public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs
public import Silmaril.Compiler.Category.Cerberus.Process.Thms

/-! The source-to-Core bridge below uses actual elaboration equations. Runtime
conversion recognition and integer bounds remain explicit; neither elaboration
success nor a Core behavior is assumed as a certificate.
-/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationProcess
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction
open Silmaril.Compile.Core.Verified

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

private theorem freshReturnLabel_run (before : State.Context)
    (available : before.freshness.next ≤ before.freshness.maximum) :
    State.run Functions.freshReturnLabel before =
      (.ok ⟨before.freshness.digest, before.freshness.next, .id s!"ret_{before.freshness.next}"⟩,
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) := by
  simp only [Functions.freshReturnLabel, State.freshInteger, run_bind, run_get,
    Freshness.integer_of_bound before.freshness available, run_set, run_pure]

private theorem freshDescription_run (before : State.Context)
    (available : before.freshness.next ≤ before.freshness.maximum) :
    State.run (State.freshDescription .none) before =
      (.ok ⟨before.freshness.digest, before.freshness.next, .none⟩,
       {before with freshness := {before.freshness with next := before.freshness.next + 1}}) := by
  simp only [State.freshDescription, run_bind, run_get,
    Freshness.description_of_bound before.freshness .none available, run_set, run_pure]

private theorem body_run (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : Functions.RuntimeInputs)
    (source : LiteralMain) (freshness : Freshness.Context)
    (available : freshness.next + 1 ≤ freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
      runtime.stdlib = some (conversion, .function resultType parameters body)) :
    State.run (Statements.translate config types runtime.stdlib
      ⟨source.returnType, returnLabel freshness, false⟩ source.body (some source.symbol) runtime.aliases)
      (State.initial {freshness with next := freshness.next + 1} .normal "Driver") =
      (.ok (source.coreBody freshness conversion),
       State.initial {freshness with next := freshness.next + 2} .normal "Driver") := by
  let before := State.initial {freshness with next := freshness.next + 1} .normal "Driver"
  let blockContext : State.Context := {before with effects :=
    {before.effects with visibleObjects := [] :: before.effects.visibleObjects, compoundLiterals := []}}
  have returned := ElaborationCorrectness.returnLiteral_run_withAliases config types runtime.stdlib runtime.aliases
    ⟨source.returnType, returnLabel freshness, false⟩ source.returnAnnotations rfl rfl
    source.statementLocation source.expressionLocation source.returnDesugaring source.statementAttributes
    source.number source.basis source.suffix blockContext rfl rfl available
    conversion resultType parameters body found (some source.symbol)
  simp only [Statements.translate, ElaborationCorrectness.returnLiteral,
    Statements.construct.eq_def, Scheduling.execute_defer] at returned
  rw [LiteralMain.body, Statements.translate, Statements.construct.eq_def]
  simp only [List.attach_cons, List.attach_nil, List.map_nil,
    Scheduling.mapM, Scheduling.buildMapAt, Nat.reduceLT, ite_eq_left, pure_bind]
  simp only [ElaborationCorrectness.returnLiteral]
  rw [Statements.construct.eq_def, Scheduling.map_defer]
  simp only [Scheduling.defer, pure_bind]
  rw [← Scheduling.defer, Scheduling.execute_defer]
  simp only [List.isEmpty_nil, ite_true]
  rw [run_map]
  simp only [State.withBlockObjects, State.allocateConstAliases, run_bind, run_getEffects,
    run_pure, run_modifyEffects, List.foldl_nil, List.map_nil,
    Scheduling.sequenceActions]
  rw [returned]
  simp [before, blockContext, State.initial, State.initialEffects, LiteralMain.coreBody,
    returnTemporary, Nat.add_assoc, run_map, run_modifyEffects, run_pure,
    Except.map, addAttributes, Statements.annotate]

/-- Three allocations come from the actual translation: the return label, the
returned expression's binding, and the saved return value. This is a successful
elaboration theorem, rather than an assumed certificate about external output. -/
theorem literal_elaborate (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : Functions.RuntimeInputs)
    (source : LiteralMain) (freshness : Freshness.Context)
    (available : freshness.next + 2 ≤ freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
      runtime.stdlib = some (conversion, .function resultType parameters body)) :
    Functions.elaborate config types runtime source.program freshness =
      (.ok (source.bindings runtime freshness conversion), finalContext freshness) := by
  have emptyGlobals : GlobalOrder.mergeIndependent [] = .ok [] := by
    simp only [GlobalOrder.mergeIndependent, GlobalOrder.uniqueKeys, List.mergeSort_nil]
    rfl
  have firstAvailable : freshness.next ≤ freshness.maximum := by omega
  have secondAvailable : freshness.next + 1 ≤ freshness.maximum := by omega
  have labelAllocated :
      State.run Functions.freshReturnLabel (State.initial freshness .normal "Driver") =
        (.ok (returnLabel freshness),
          State.initial {freshness with next := freshness.next + 1} .normal "Driver") := by
    simpa [State.initial, State.initialEffects, returnLabel] using
      freshReturnLabel_run (State.initial freshness .normal "Driver") firstAvailable
  have translated :
      State.run (Statements.translate config types runtime.stdlib
        ⟨source.returnType, returnLabel freshness, false⟩ source.body
        (some source.symbol) runtime.aliases)
        (State.initial {freshness with next := freshness.next + 1} .normal "Driver") =
        (.ok (source.coreBody freshness conversion),
          State.initial {freshness with next := freshness.next + 2} .normal "Driver") :=
    body_run config types runtime source freshness secondAvailable
      conversion resultType parameters body found
  have temporaryAllocated :
      State.run (State.freshDescription .none)
        (State.initial {freshness with next := freshness.next + 2} .normal "Driver") =
        (.ok (saveTemporary freshness), finalContext freshness) := by
    simpa [State.initial, State.initialEffects, saveTemporary, finalContext] using
      freshDescription_run
        (State.initial {freshness with next := freshness.next + 2} .normal "Driver") available
  simp only [State.initial, State.initialEffects, LiteralMain.returnType,
    returnLabel, saveTemporary, finalContext, toString] at labelAllocated translated temporaryAllocated
  simp [Functions.elaborate, State.runErrors, Functions.translate, LiteralMain.program,
    Functions.declaration, Functions.reserveParameterSymbols, Functions.resultType,
    Functions.objectType, Functions.liftError, Functions.integerType, emptyGlobals,
    LiteralMain.returnType, State.getCallingConvention, run_bind, run_getEffects,
    Functions.insertSymbol, Functions.externalKind, LiteralMain.bindings, finalContext,
    returnLabel, saveTemporary, State.initial, State.initialEffects, labelAllocated,
    translated, temporaryAllocated, run_pure, toString]

/-- The recognizer sees the actual saved-label function assembled by the real
elaborator. Its only semantic input is recognition of the supplied runtime's
integer conversion function; no successful execution is assumed. -/
theorem literal_recognize (source : LiteralMain) (runtime : Functions.RuntimeInputs)
    (freshness : Freshness.Context) (conversion : Sym) (commit implementation : String)
    (enums : Option (List (Sym × IntegerType)))
    (conversionRecognized : ConvInt.isConvLoadedInt
      (source.bindings runtime freshness conversion).toFile conversion = true)
    (range : ConvInt.IsInt source.number) :
    ReturnLit.recognize (document (source.bindings runtime freshness conversion)
      commit implementation enums) = some source.number := by
  rcases source with ⟨symbol, location, marker, attributes, blockDesugaring,
    statementLocation, expressionLocation, returnDesugaring, statementAttributes,
    returnAnnotations, number, basis, suffix⟩
  cases statementAttributes with
  | mk annotations =>
    cases annotations <;>
      simp [ReturnLit.recognize, document, LiteralMain.bindings, Codec.FileBindings.toFile,
        Map.ofList, Functions.returnSave, LiteralMain.coreBody, LiteralMain.returnType,
        Statements.unitSequence, ElaborationCorrectness.returnCore, ReturnLit.recognizeBody,
        ReturnLit.saveFree, ReturnLit.retLit, strongSequence, wildcard, saveWith,
        pureEffect, symbolPure, symbolPureWith, addLocation, addStatement, addAnnotation,
        addAttributes, deleteFirst, skip, Construction.run, call, ctype, valuePure,
        symbolPattern, symbolPatternWith, Constants.loadedInteger, ConvInt.IsInt] at *
    all_goals exact ⟨conversionRecognized, range⟩

/-- Nonempty operational content for the actual source fragment: the real
elaborator returns this file and it has a genuine Core-institution behavior
observed as the literal exit status with empty output. This is an existential
behavior theorem, not universal safety, termination, or an Ail refinement law. -/
theorem literal_process (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : Functions.RuntimeInputs)
    (source : LiteralMain) (freshness : Freshness.Context)
    (available : freshness.next + 2 ≤ freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
      runtime.stdlib = some (conversion, .function resultType parameters body))
    (conversionRecognized : ConvInt.isConvLoadedInt
      (source.bindings runtime freshness conversion).toFile conversion = true)
    (range : ConvInt.IsInt source.number) (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) (arguments : List String) :
    let core := document (source.bindings runtime freshness conversion) commit implementation enums
    ∃ initial labels behavior,
      Functions.elaborate config types runtime source.program freshness =
        (.ok core.bindings, finalContext freshness) ∧
      Category.Cerberus.Process.Spec.coreStart core arguments = .ok (initial, labels) ∧
      (Category.Cerberus.Process.model core initial labels).realises behavior ∧
      Category.Cerberus.Process.Observes behavior (.exit (source.number % 256).toNat []) := by
  let core := document (source.bindings runtime freshness conversion) commit implementation enums
  have recognized := literal_recognize source runtime freshness conversion commit implementation enums
    conversionRecognized range
  obtain ⟨initial, labels, final, start, _, _, _⟩ :=
    ReturnLit.recognize_reaches core source.number recognized
      (Map.ofList (core.enumBindings.getD [])) arguments
  have process := ReturnLit.recognize_sound core source.number recognized arguments
  obtain ⟨behavior, realises, observes⟩ :=
    (Category.Cerberus.Process.coreBeh_iff_realises_observes core arguments initial labels start
      (.exit (source.number % 256).toNat [])).1 process
  exact ⟨initial, labels, behavior,
    literal_elaborate config types runtime source freshness available conversion resultType parameters body found,
    start, realises, observes⟩

end Silmaril.Compiler.Core.ElaborationProcess
