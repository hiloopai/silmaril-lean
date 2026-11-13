module

public import Silmaril.Compiler.Core.ElaborationCallProcess.Defs
public import Silmaril.Compiler.Core.CallReturn.Thms
public import Silmaril.Compiler.Core.ElaborationTotal.Thms
public import Silmaril.Compiler.Category.Cerberus.Hets.Thms

/-! Whole-process composition for the independently selected two-function
source. Actual elaboration and startup are proved, then a forced execution
constrains every terminal behavior and rules out every infinite trace. -/
@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationCallProcess
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Core.CalleeReturn
open Silmaril.Compiler.Core.CallReturn
open Construction Example
attribute [local cbv_eval] Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil
theorem source_elaborates : elaborated.1.toOption.isSome = true := by cbv
private def bindings : Codec.FileBindings := elaborated.1.toOption.get source_elaborates
private def file : Program := bindings.toFile

/-- Inspect the actual source-generated main body, without supplying its Core. -/
private def emittedCall : Option EE := do
  let .procedure _ _ _ []
    (.mk _ (.sseq _ (.mk _ (.sseq _ (.mk _ (.sseq _ (.mk _ (.bound expression)) _)) _)) _))
    ← file.funs.lookup mainSymbol | none
  pure expression

private theorem source_call_recognized :
    emittedCall.bind (Call.callSite file) = some (fSymbol, true) := by cbv

private theorem source_call_exists : emittedCall.isSome = true := by cbv
private def callExpression : EE := emittedCall.get source_call_exists

private def emittedCallee : Option EE := do
  let .procedure _ _ _ [] body ← file.funs.lookup fSymbol | none
  pure body
private theorem source_callee_exists : emittedCallee.isSome = true := by cbv
private def calleeBody : EE := emittedCallee.get source_callee_exists

private theorem source_generated_call_returns (labels : Labels) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧ Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr callExpression environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer 42))), frames, finish⟩ := by
  apply callSite_forced_return (g := fSymbol) (loc := .unknown) (attrs := .mk [])
    (fty := intType) (variadic := false) (proto := true) (body := calleeBody)
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv


open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Cerberus.Core
open Silmaril.Compiler.Core.ElaborationTotal
open ReturnConst (focusMemory focusMemory_stdout)

section ReturnCall
variable {file : Program} {labels : Labels}
private theorem focusMemory_eq_of_location (annotations : List Annot) (memory : Mem.Concrete.State)
    (location : (focusMemory annotations memory).currentLocation = memory.currentLocation) :
    focusMemory annotations memory = memory := by
  revert location
  unfold focusMemory
  split
  · split
    · intro _; rfl
    · intro location
      simp only at location
      subst location
      rfl
  · intro _; rfl

private theorem focusMemory_update (annotations : List Annot) (memory : Mem.Concrete.State) :
    ({memory with currentLocation := (focusMemory annotations memory).currentLocation} :
      Mem.Concrete.State) = focusMemory annotations memory := by
  unfold focusMemory
  split
  · split <;> rfl
  · rfl

private theorem focus_forced {annotations : List Annot} {node : ExprNode Codec.wireModel Unit Unit Sym}
    {environment : Env} {frames : List Frame} {memory : Mem.Concrete.State}
    {control : Control} {following : List Frame}
    (requested : request file labels ⟨.effectExpr (.mk annotations node) environment, frames, memory⟩ =
      if (focusMemory annotations memory).currentLocation == memory.currentLocation then .next control following
      else .next (.setLocation (focusMemory annotations memory).currentLocation control) following) :
    Forced.Reaches file labels ⟨.effectExpr (.mk annotations node) environment, frames, memory⟩
      ⟨control, following, focusMemory annotations memory⟩ := by
  by_cases equal : (focusMemory annotations memory).currentLocation == memory.currentLocation
  · have same : focusMemory annotations memory = memory := by
      exact focusMemory_eq_of_location annotations memory (by simpa using equal)
    rw [same]
    exact Forced.next (by intro outcome impossible; cases impossible) (by rw [requested, same]; simp)
  · refine (Forced.next (c' := .setLocation (focusMemory annotations memory).currentLocation control)
      (k' := following) (by intro outcome impossible; cases impossible)
      (by rw [requested]; simp [equal])).trans ?_
    apply Forced.update (by intro outcome impossible; cases impossible)
    rw [← focusMemory_update annotations memory]
    simp [request, requestAux, awaitsScheduling]

private theorem effectPure_forced (annotations : List Annot) (expression : PE) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk annotations (.pure expression)) environment, frames, memory⟩
      ⟨.pureExpr expression environment, .diagnosticLocation memory.currentLocation :: frames,
        focusMemory annotations memory⟩ :=
  focus_forced (ReturnConst.request_effect_pure file labels annotations expression environment frames memory)

private theorem sequence_forced (annotations : List Annot) (pattern : Pattern Sym)
    (first rest : EE) (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk annotations (.sseq pattern first rest)) environment, frames, memory⟩
      ⟨.effectExpr first environment, .strongBind pattern rest environment :: frames, memory⟩ := by
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

private theorem pop_forced {frame : Frame} (value : Val) (frames : List Frame)
    (memory : Mem.Concrete.State) (kind : frame = .bound ∨ ∃ location, frame = .diagnosticLocation location) :
    Forced.Reaches file labels ⟨.value value, frame :: frames, memory⟩ ⟨.value value, frames, memory⟩ := by
  apply Forced.next (by intro outcome impossible; cases impossible)
  rcases kind with rfl | ⟨location, rfl⟩ <;> simp [request, requestAux, awaitsScheduling]

private theorem value_forced_halt (value : Val) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.value value, [], memory⟩ ⟨.halt (.defined value), [], memory⟩ := by
  apply Forced.end_ (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

private theorem jump_forced_halt {returnLabel label : Sym} (same : label.key = returnLabel.key)
    (saved : ReturnLit.ReturnLabel labels returnLabel) (value : Val) (environment : Env)
    {frames : List Frame} (boundary : ReturnLit.NoBoundary frames) (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches file labels ⟨.value value, .runLabel label [] [] environment :: frames, memory⟩
        ⟨.halt (.defined value), [], finish⟩ := by
  obtain ⟨parameter, bodyAnnotations, symbolAnnotations, occurrence, sameParameter, lookup⟩ := saved
  have labelLookup : labels.lookup label = some
      ([parameter], .mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence)))) := by
    rw [ReturnLit.lookup_key same]
    exact lookup
  refine ⟨focusMemory bodyAnnotations memory, focusMemory_stdout bodyAnnotations memory, ?_⟩
  have noBoundary : hasBoundary frames = false := boundary
  refine (Forced.next (c' := .effectExpr (.mk bodyAnnotations (.pure (.mk symbolAnnotations ()
    (.sym occurrence)))) (extendEnv ([parameter].zip [value]) environment)) (k' := [])
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling, requestJump, noBoundary, jump, jumpDestination,
      ReturnLit.procedureContext_noBoundary boundary, labelLookup]
  refine (effectPure_forced bodyAnnotations _ _ [] memory).trans ?_
  refine (Forced.next (c' := .value value) (k' := [.diagnosticLocation memory.currentLocation])
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · have parameterValue : (extendEnv [(parameter, value)] environment).lookup occurrence = some value :=
      ConvInt.lookup_one sameParameter
    simp [request, requestAux, awaitsScheduling, parameterValue]
  exact (pop_forced _ _ _ (.inr ⟨_, rfl⟩)).trans (value_forced_halt value _)


/-- A syntactically recognized return-call statement follows the actual call,
converts the actual returned literal, and jumps through the actual saved return
label. Arbitrary boundary-free main-local continuations are allowed. -/
theorem retCall_forced {returnLabel : Sym} (saved : ReturnLit.ReturnLabel labels returnLabel)
    (expression : EE) {callee : Sym} {term : IntExpr.Term} {number : Int}
    {location : Loc} {attributes : Attributes} {result : Ctype}
    {variadic prototype : Bool} {body : EE}
    (recognized : Call.retCall file returnLabel expression = some (callee, term))
    (metadata : file.funInfo.lookup callee =
      some (location, attributes, result, [], variadic, prototype))
    (integerResult : Call.retKind result = some true)
    (ordinary : libraryCall file callee = none)
    (resolved : procedureBody file callee [] = .ok (body, []))
    (literalBody : ReturnLit.recognizeBody file body = some number)
    (bounds : ConvInt.IsInt number) (environment : Env)
    {frames : List Frame} (boundary : ReturnLit.NoBoundary frames) (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
      ⟨.effectExpr expression environment, frames, memory⟩
      ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩ := by
  unfold Call.retCall at recognized
  split at recognized
  next _ annotations patternAnnotations temporary type boundAnnotations callExpression
      runAnnotations label conversionAnnotations conversion typeAnnotations ctypeAnnotations
      symbolAnnotations occurrence =>
    show ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
      ⟨.effectExpr _ environment, frames, memory⟩
      ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
    split at recognized
    next accepted =>
      show ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
        ⟨.effectExpr _ environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
      obtain ⟨sameLabel, sameTemporary, runtime⟩ := accepted
      split at recognized
      next foundCallee foundCall =>
        show ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
          ⟨.effectExpr _ environment, frames, memory⟩
          ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
        split at recognized
        next foundTerm foundBody =>
          show ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
            ⟨.effectExpr _ environment, frames, memory⟩
            ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
          cases recognized
          let runExpression : EE := .mk runAnnotations (.run () label
            [.mk conversionAnnotations () (.call (.sym conversion)
              [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations
                (.basic (.integer (.signed .int)))))),
               .mk symbolAnnotations () (.sym occurrence)])])
          let continuation : List Frame :=
            Frame.strongBind (.mk patternAnnotations (.base (some temporary, type)))
              runExpression environment :: frames
          let value : Val := .loaded (.specified (.integer number))
          obtain ⟨middle, locationOnly, callReturned⟩ :
              ∃ middle, LocationOnly memory middle ∧ Forced.Reaches file labels
                ⟨.effectExpr callExpression environment, .bound :: continuation, memory⟩
                ⟨.value value, .bound :: continuation, middle⟩ :=
            callSite_forced_return (labels := labels) foundCall metadata integerResult
              ordinary resolved literalBody environment (.bound :: continuation) memory
          let extended : Env := extendEnv [(temporary, value)] environment
          have operands : Eval file (tagsOf file (focusMemory runAnnotations middle)) extended
              (.inr [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations
                (.basic (.integer (.signed .int)))))), .mk symbolAnnotations () (.sym occurrence)])
              (.inr [.ctype (.mk ctypeAnnotations (.basic (.integer (.signed .int)))), value]) :=
            .cons .val (.cons (.sym (ConvInt.lookup_one sameTemporary)) .nil)
          have evaluation : Eval file (tagsOf file (focusMemory runAnnotations middle)) extended
              (.inl (.mk conversionAnnotations () (.call (.sym conversion)
                [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations
                  (.basic (.integer (.signed .int)))))), .mk symbolAnnotations () (.sym occurrence)])))
              (.inl value) := ConvInt.convLoadedInt_eval (ann := ctypeAnnotations) runtime bounds operands
          obtain ⟨finish, stdout, savedReturn⟩ : ∃ finish,
              finish.stdout = (focusMemory runAnnotations middle).stdout ∧
                Forced.Reaches file labels
                  ⟨.value value, .runLabel label [] [] extended :: frames,
                    focusMemory runAnnotations middle⟩
                  ⟨.halt (.defined value), [], finish⟩ :=
            jump_forced_halt (file := file) sameLabel saved value extended
              boundary (focusMemory runAnnotations middle)
          have enterCall : Forced.Reaches file labels
              ⟨.effectExpr (.mk boundAnnotations (.bound callExpression)) environment,
                continuation, memory⟩
              ⟨.effectExpr callExpression environment, .bound :: continuation, memory⟩ := by
            apply Forced.next (by intro outcome impossible; cases impossible)
            simp [request, requestAux, awaitsScheduling]
          have leaveBound : Forced.Reaches file labels
              ⟨.value value, .bound :: continuation, middle⟩
              ⟨.value value, continuation, middle⟩ :=
            pop_forced value continuation middle (.inl rfl)
          have bindResult : Forced.Reaches file labels
              ⟨.value value, continuation, middle⟩
              ⟨.effectExpr runExpression extended, frames, middle⟩ := by
            apply Forced.next (by intro outcome impossible; cases impossible)
            simp [request, requestAux, awaitsScheduling, continuation, extended, value, matchPattern]
          have convertAndReturn : Forced.Reaches file labels
              ⟨.effectExpr runExpression extended, frames, middle⟩
              ⟨.halt (.defined value), [], finish⟩ := by
            refine (focus_forced (memory := middle) Straight.request_run).trans ?_
            exact ((pureEvaluation_forced file _ evaluation) labels _ _ rfl).trans savedReturn
          have outputPreserved : finish.stdout = memory.stdout :=
            stdout.trans ((focusMemory_stdout runAnnotations middle).trans locationOnly.stdout)
          refine ⟨finish, outputPreserved, ?_⟩
          exact (sequence_forced annotations _ _ runExpression environment frames memory).trans
            (enterCall.trans (callReturned.trans (leaveBound.trans (bindResult.trans convertAndReturn))))
        next => cases recognized
      next => cases recognized
    next => cases recognized
  next _ annotations patternAnnotations type first rest =>
    show ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
      ⟨.effectExpr _ environment, frames, memory⟩
      ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
    obtain ⟨finish, stdout, returned⟩ : ∃ finish, finish.stdout = memory.stdout ∧
        Forced.Reaches file labels
          ⟨.effectExpr first environment,
            .strongBind (.mk patternAnnotations (.base (none, type))) rest environment :: frames, memory⟩
          ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩ :=
      retCall_forced saved first recognized metadata integerResult ordinary resolved literalBody bounds environment
        (frames := .strongBind (.mk patternAnnotations (.base (none, type))) rest environment :: frames)
        (ReturnLit.noBoundary_cons boundary trivial) memory
    exact ⟨finish, stdout, (sequence_forced annotations _ first rest environment frames memory).trans returned⟩
  next => cases recognized
termination_by sizeOf expression
end ReturnCall


private def emittedMain : Option EE := do
  let .procedure _ _ _ [] body ← file.funs.lookup mainSymbol | none
  pure body
private theorem source_main_exists : emittedMain.isSome = true := by cbv
private def mainCore : EE := emittedMain.get source_main_exists
private def outerParts? : Option (List Annot × Pat × EE × EE) :=
  match mainCore with
  | .mk annotations (.sseq pattern first ending) => some (annotations, pattern, first, ending)
  | _ => none
private theorem outer_parts_exist : outerParts?.isSome = true := by cbv
private def parts := outerParts?.get outer_parts_exist
private def mainReturnLabel : Sym := ⟨⟨[]⟩, 100, .id "ret_100"⟩

private theorem main_core_shape :
    mainCore = .mk parts.1 (.sseq parts.2.1 parts.2.2.1 parts.2.2.2) := by cbv
private theorem main_saved :
    ReturnLit.ReturnLabel (Map.ofList (saves mainCore).reverse) mainReturnLabel := by
  refine ⟨⟨⟨[]⟩, 105, .none⟩, [], [], ⟨⟨[]⟩, 105, .none⟩, rfl, ?_⟩
  cbv
private theorem main_returns_call :
    Call.retCall file mainReturnLabel parts.2.2.1 = some (fSymbol, .lit 42) := by cbv

/-- The actual source-generated main body halts through its real saved label.
The environment and any main-local boundary-free continuation are arbitrary. -/
private theorem source_main_body_forced (labels : Labels)
    (saved : ReturnLit.ReturnLabel labels mainReturnLabel)
    (environment : Env) (frames : List Frame) (boundary : ReturnLit.NoBoundary frames)
    (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧ Forced.Reaches file labels
      ⟨.effectExpr mainCore environment, frames, memory⟩
      ⟨.halt (.defined (.loaded (.specified (.integer 42)))), [], finish⟩ := by
  obtain ⟨finish, stdout, returned⟩ := retCall_forced
    (file := file) (labels := labels) saved parts.2.2.1
    (callee := fSymbol) (term := .lit 42) (number := 42)
    (location := .unknown) (attributes := .mk []) (result := intType)
    (variadic := false) (prototype := true) (body := calleeBody)
    main_returns_call (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
    (by constructor <;> decide +kernel)
    environment (frames := .strongBind parts.2.1 parts.2.2.2 environment :: frames)
    (ReturnLit.noBoundary_cons boundary trivial) memory
  refine ⟨finish, stdout, ?_⟩
  rw [main_core_shape]
  exact (sequence_forced parts.1 parts.2.1 parts.2.2.1 parts.2.2.2
    environment frames memory).trans returned

/-- Start the actual source-generated file with the actual Core startup rules.
The no-parameter main result is independent of argv and the enum registry. -/
private theorem source_startup_forced (enums : Map Sym IntegerType) (arguments : List String) :
    ∃ start labels finish,
      initial file enums arguments = .ok (start, labels) ∧
      Forced.Reaches file labels start finish ∧
      finish.control = .halt (.defined (.loaded (.specified (.integer 42)))) ∧
      finish.memory.stdout = "" := by
  have globs : file.globs = [] := by cbv
  have main : file.main = some mainSymbol := by cbv
  have declaration : file.funs.lookup mainSymbol =
      some (.procedure .unknown (some 8) (.loaded .integer) [] mainCore) := by cbv
  obtain ⟨start, labels, memory, accesses, started, stdout, entered⟩ :=
    initial_forced_body file enums arguments (by simp [globs]) main declaration
  have labelsEq : labels = Map.ofList (saves mainCore).reverse := by
    have initialization := started
    simp [initial, globs, main, declaration] at initialization
    exact initialization.2.symm
  have saved : ReturnLit.ReturnLabel labels mainReturnLabel := by
    rw [labelsEq]
    exact main_saved
  obtain ⟨finish, output, returned⟩ := source_main_body_forced labels saved ∅ [.annotations accesses]
    (by simp [ReturnLit.NoBoundary, hasBoundary]) memory
  exact ⟨start, labels, _, started, entered.trans returned, rfl, output.trans stdout⟩


open Silmaril.Compiler.Category.Cerberus

/-- A forced halt yields universal institution satisfaction and exactly one
completed process observation. Finite unfinished prefixes remain behaviors. -/
theorem forced_total (document : Codec.Document) (arguments : List String)
    {start finish : Dynamics.State} {labels : Labels} {number : Int}
    (started : Process.Spec.coreStart document arguments = .ok (start, labels))
    (forced : Forced.Reaches document.file labels start finish)
    (halted : finish.control = .halt (.defined (.loaded (.specified (.integer number)))))
    (stdout : finish.memory.stdout = "") :
    Silmaril.Cerberus.Institution.Satisfies (Process.model document start labels) (returnsInteger number) ∧
      ∀ observation, Process.Spec.CoreBeh document arguments observation ↔
        observation = .exit (number % 256).toNat [] := by
  have correct : Silmaril.Cerberus.Institution.Satisfies
      (Process.model document start labels) (returnsInteger number) := by
    intro behavior realized
    cases behavior with
    | finite actions state =>
        show ∀ outcome, state.control = .halt outcome →
          outcome = .defined (.loaded (.specified (.integer number))) ∧ state.memory.stdout = ""
        intro outcome stateHalted
        have reachable : Relation.ReflTransGen (Process.Spec.coreStep document.file labels) start state := (Process.finite_iff_reaches (Process.model document start labels) state).1
          ⟨actions, realized⟩
        have same : state = finish := Forced.terminal_unique forced halted reachable stateHalted
        cases same
        exact ⟨Control.halt.inj (stateHalted.symm.trans halted), stdout⟩
    | infinite states actions =>
        show False
        exact Forced.no_infinite forced halted states actions realized.1 realized.2
  refine ⟨correct, fun observation => ?_⟩
  constructor
  next =>
    show Process.Spec.CoreBeh document arguments observation →
      observation = .exit (number % 256).toNat []
    intro behavior
    obtain ⟨execution, realized, observed⟩ :=
      (Process.coreBeh_iff_realises_observes document arguments start labels started observation).1 behavior
    have terminal : returnsInteger number execution := correct execution realized
    cases execution with
    | finite actions state =>
        show observation = .exit (number % 256).toNat []
        cases observation with
        | exit status bytes =>
            show (.exit status bytes : Process.Spec.Obs) = .exit (number % 256).toNat []
            obtain ⟨value, stateHalted, statusAllowed, output⟩ := observed
            obtain ⟨returned, empty⟩ := terminal (.defined value) stateHalted
            have valueEquality : value = .loaded (.specified (.integer number)) := Outcome.defined.inj returned
            have statusEquality : status = (number % 256).toNat := by
              simpa only [valueEquality, Process.Spec.exitStatuses] using statusAllowed
            have bytesEquality : bytes = [] := by
              simpa [Process.Spec.coreBytes, empty] using output.symm
            exact congrArg₂ (fun status bytes => (.exit status bytes : Process.Spec.Obs))
              statusEquality bytesEquality
        | abort bytes =>
            have impossible : Outcome.aborted = .defined (.loaded (.specified (.integer number))) :=
              (terminal .aborted observed.1).1
            cases impossible
        | trap | fault | diverges | exhausted => exact observed.elim
    | infinite states actions => exact terminal.elim
  next =>
    show observation = .exit (number % 256).toNat [] →
      Process.Spec.CoreBeh document arguments observation
    intro same
    subst observation
    have behavior : Process.Spec.CoreBeh document arguments
        (.exit (number % 256).toNat (Process.Spec.coreBytes finish.memory.stdout)) :=
      .exit ⟨start, labels, started, forced.erase⟩ halted rfl
    simpa [Process.Spec.coreBytes, stdout] using behavior

private def actualDocument (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) : Codec.Document :=
  Silmaril.Compiler.Core.ElaborationProcess.document bindings commit implementation enums

private theorem source_elaboration_actual : elaborated.1 = .ok bindings := by cbv

theorem source_freshness_actual : elaborated.2.freshness.next = 109 := by cbv

/-- Actual elaboration of the coherent-export typed-Ail f/main fixture, actual
Core startup, universal institution satisfaction and exact completed process
behavior. Runtime, frontend target and source syntax are fixed explicitly above;
argv, commit/implementation strings and enum registry remain arbitrary. -/
theorem whole_source_f_main_total (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) (arguments : List String) :
    ∃ bindings start labels,
      Example.elaborated.1 = .ok bindings ∧
      let document := Silmaril.Compiler.Core.ElaborationProcess.document bindings commit implementation enums
      Process.Spec.coreStart document arguments = .ok (start, labels) ∧
      Silmaril.Cerberus.Institution.Satisfies (Process.model document start labels) (returnsInteger 42) ∧
      ∀ observation, Process.Spec.CoreBeh document arguments observation ↔
        observation = .exit 42 [] := by
  let document := actualDocument commit implementation enums
  obtain ⟨start, labels, finish, started, forced, halted, stdout⟩ :=
    source_startup_forced (Map.ofList (enums.getD [])) arguments
  have coreStarted : Process.Spec.coreStart document arguments = .ok (start, labels) := started
  obtain ⟨correct, observations⟩ := forced_total document arguments coreStarted forced halted stdout
  exact ⟨bindings, start, labels, source_elaboration_actual, coreStarted, correct, by simpa [document, actualDocument] using observations⟩


/-- The same actual source result in the compiler-category behavioral language. -/
theorem whole_source_f_main_category (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) (arguments : List String) :
    ∃ bindings start labels,
      Example.elaborated.1 = .ok bindings ∧
      let document := Silmaril.Compiler.Core.ElaborationProcess.document bindings commit implementation enums
      Process.Spec.coreStart document arguments = .ok (start, labels) ∧
      Silmaril.Compiler.Category.Cerberus.language.Sat (Process.model document start labels) {behavior | returnsInteger 42 behavior} ∧
      ∀ observation, Process.Spec.CoreBeh document arguments observation ↔
        observation = .exit 42 [] := by
  obtain ⟨bindings, start, labels, elaborated, started, correct, observations⟩ :=
    whole_source_f_main_total commit implementation enums arguments
  exact ⟨bindings, start, labels, elaborated, started, satisfies_category correct, observations⟩

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category

/-- The result at the existing Hets graph's operational node, along its real
Core-behavior realization edge. No target/compiler property is inferred. -/
theorem whole_source_f_main_graph (target : Language.{0})
    (convention : Silmaril.Compiler.Category.Cerberus.language ⟶ target)
    (readback : Convention.ReadBack convention) (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) (arguments : List String) :
    ∃ bindings start labels,
      Example.elaborated.1 = .ok bindings ∧
      let document := Silmaril.Compiler.Core.ElaborationProcess.document bindings commit implementation enums
      Process.Spec.coreStart document arguments = .ok (start, labels) ∧
      (Silmaril.Compiler.Category.Cerberus.Core.room fullVocabulary).Sat
        (Discrete.mk (Process.model document start labels))
        ((((Hets.graph target convention readback).comor Hets.Translation.realize).ρ.app
          (Discrete.mk PUnit.unit)).sen {behavior | returnsInteger 42 behavior}) := by
  obtain ⟨bindings, start, labels, elaborated, started, correct, _⟩ :=
    whole_source_f_main_total commit implementation enums arguments
  exact ⟨bindings, start, labels, elaborated, started,
    (Hets.operational_satisfaction target convention readback _ _).2 correct⟩
end Silmaril.Compiler.Core.ElaborationCallProcess
