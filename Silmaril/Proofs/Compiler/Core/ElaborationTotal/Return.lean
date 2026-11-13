module

public import Silmaril.Compiler.Core.ElaborationTotal.Defs
public import Silmaril.Proofs.Compiler.Core.ElaborationTotal.Pure
public import Silmaril.Proofs.Compiler.Core.ElaborationTotal.Startup

/-! Forced-transition counterparts of the imported literal-return reachability
proof. Runtime recognition still inspects actual function syntax. The proof
strengthening inverts every possible response along the selected pure path. -/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Compile.Core.Verified
open ReturnConst (focusMemory focusMemory_stdout)
open Silmaril.Cerberus.Core

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

private theorem boundLiteral_forced (boundAnnotations expressionAnnotations valueAnnotations : List Annot)
    (number : Int) (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels
      ⟨.effectExpr (.mk boundAnnotations (.bound (.mk expressionAnnotations
        (.pure (.mk valueAnnotations () (.val (.loaded (.specified (.integer number))))))))) environment,
        frames, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), frames, focusMemory expressionAnnotations memory⟩ := by
  refine (Forced.next (c' := .effectExpr (.mk expressionAnnotations (.pure
    (.mk valueAnnotations () (.val (.loaded (.specified (.integer number))))))) environment)
    (k' := .bound :: frames)
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling]
  refine (effectPure_forced expressionAnnotations _ environment _ memory).trans ?_
  refine (Forced.next (c' := .value (.loaded (.specified (.integer number))))
    (k' := .diagnosticLocation memory.currentLocation :: .bound :: frames)
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling, runtimeValue, runtimeLoaded, runtimeObject]
  exact (pop_forced _ _ _ (.inr ⟨_, rfl⟩)).trans (pop_forced _ _ _ (.inl rfl))

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

theorem retLit_forced (returnLabel : Sym) (saved : ReturnLit.ReturnLabel labels returnLabel)
    (expression : EE) (number : Int) (recognized : ReturnLit.retLit file returnLabel expression = some number)
    (environment : Env) {frames : List Frame} (boundary : ReturnLit.NoBoundary frames)
    (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches file labels ⟨.effectExpr expression environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩ := by
  unfold ReturnLit.retLit at recognized
  split at recognized
  · show ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches file labels ⟨.effectExpr _ environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
    rename_i _ annotations patternAnnotations temporary type boundAnnotations expressionAnnotations
      valueAnnotations otherNumber runAnnotations label callAnnotations conversion typeAnnotations
      ctypeAnnotations symbolAnnotations occurrence
    split at recognized
    · show ∃ finish, finish.stdout = memory.stdout ∧
        Forced.Reaches file labels ⟨.effectExpr _ environment, frames, memory⟩
          ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩
      rename_i accepted
      obtain ⟨sameLabel, sameTemporary, runtime, lower, upper⟩ := accepted
      cases recognized
      let value : Val := .loaded (.specified (.integer number))
      let focused := focusMemory expressionAnnotations memory
      let extended := extendEnv [(temporary, value)] environment
      let runExpression : EE := .mk runAnnotations (.run () label [.mk callAnnotations () (.call (.sym conversion)
        [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations (.basic (.integer (.signed .int)))))),
         .mk symbolAnnotations () (.sym occurrence)])])
      have bounds : ConvInt.IsInt number := ⟨lower, upper⟩
      have temporaryValue : extended.lookup occurrence = some value := ConvInt.lookup_one sameTemporary
      have operands : Eval file (tagsOf file (focusMemory runAnnotations focused)) extended
          (.inr [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations (.basic (.integer (.signed .int)))))),
            .mk symbolAnnotations () (.sym occurrence)])
          (.inr [.ctype (.mk ctypeAnnotations (.basic (.integer (.signed .int)))), value]) :=
        .cons .val (.cons (.sym temporaryValue) .nil)
      have evaluation : Eval file (tagsOf file (focusMemory runAnnotations focused)) extended
          (.inl (.mk callAnnotations () (.call (.sym conversion)
            [.mk typeAnnotations () (.val (.ctype (.mk ctypeAnnotations (.basic (.integer (.signed .int)))))),
             .mk symbolAnnotations () (.sym occurrence)]))) (.inl value) :=
        ConvInt.convLoadedInt_eval (ann := ctypeAnnotations) runtime bounds operands
      obtain ⟨finish, stdout, jumped⟩ := jump_forced_halt (file := file) sameLabel saved value extended boundary
        (focusMemory runAnnotations focused)
      refine ⟨finish, by simp [stdout, focused], ?_⟩
      refine (sequence_forced annotations _ _ runExpression environment frames memory).trans ?_
      refine (boundLiteral_forced boundAnnotations expressionAnnotations valueAnnotations number environment
        _ memory).trans ?_
      refine (Forced.next (c' := .effectExpr runExpression extended) (k' := frames)
        (by intro outcome impossible; cases impossible) ?_).trans ?_
      · simp [request, requestAux, awaitsScheduling, matchPattern, extended, value]
      refine (focus_forced (memory := focused) Straight.request_run).trans ?_
      exact ((pureEvaluation_forced file _ evaluation) labels _ _ rfl).trans jumped
    · cases recognized
  · rename_i _ annotations patternAnnotations type first rest
    obtain ⟨finish, stdout, returned⟩ := retLit_forced returnLabel saved first number recognized environment
      (frames := .strongBind (.mk patternAnnotations (.base (none, type))) rest environment :: frames)
      (ReturnLit.noBoundary_cons boundary trivial) memory
    exact ⟨finish, stdout, (sequence_forced annotations _ first rest environment frames memory).trans returned⟩
  · cases recognized
termination_by sizeOf expression

private theorem recognize_noDefinitions (document : Codec.Document) (number : Int)
    (recognized : ReturnLit.recognize document = some number) :
    ∀ entry ∈ document.file.globs, ∀ base expression, entry.2 ≠ .definition base expression := by
  unfold ReturnLit.recognize at recognized
  split at recognized
  · cases recognized
  rename_i noDefinitions
  rintro ⟨symbol, global⟩ member base expression rfl
  exact noDefinitions (List.any_eq_true.mpr ⟨_, member, rfl⟩)

/-- Recognition identifies a real zero-parameter procedure and its body. -/
private theorem recognize_procedure (document : Codec.Document) (number : Int)
    (recognized : ReturnLit.recognize document = some number) :
    ∃ symbol location marker type body,
      document.file.main = some symbol ∧
      document.file.funs.lookup symbol = some (.procedure location marker type [] body) ∧
      ReturnLit.recognizeBody document.file body = some number := by
  unfold ReturnLit.recognize at recognized
  split at recognized
  · cases recognized
  cases main : document.file.main with
  | none => simp [main] at recognized
  | some symbol =>
    cases declaration : document.file.funs.lookup symbol with
    | none => simp [main, declaration] at recognized
    | some entry =>
      cases entry <;> try { simp [main, declaration] at recognized }
      case procedure location marker type parameters body =>
        cases parameters with
        | cons parameter rest => simp [main, declaration] at recognized
        | nil => exact ⟨symbol, location, marker, type, body, rfl, declaration,
            by simpa [main, declaration] using recognized⟩

theorem recognized_forced (document : Codec.Document) (number : Int)
    (recognized : ReturnLit.recognize document = some number) (enums : Map Sym IntegerType)
    (arguments : List String) :
    ∃ start labels finish, initial document.file enums arguments = .ok (start, labels) ∧
      Forced.Reaches document.file labels start finish ∧
      finish.control = .halt (.defined (.loaded (.specified (.integer number)))) ∧ finish.memory.stdout = "" := by
  have noDefinition : ∀ entry ∈ document.file.globs, ∀ base expression,
      entry.2 ≠ .definition base expression := recognize_noDefinitions document number recognized
  obtain ⟨symbol, location, marker, type, body, main, declaration, bodyRecognized⟩ :=
    recognize_procedure document number recognized
  obtain ⟨start, labels, memory, accesses, started, stdout, entered⟩ := initial_forced_body
    document.file enums arguments noDefinition main declaration
  have labelDefinitions : labels = Map.ofList (saves body).reverse := by
    have projected : (initial document.file enums arguments).toOption.map Prod.snd =
        some (Map.ofList (saves body).reverse) := by
      simp [initial, main, declaration, Except.toOption]
    simpa [started, Except.toOption] using projected
  unfold ReturnLit.recognizeBody at bodyRecognized
  split at bodyRecognized
  · show ∃ start labels finish, initial document.file enums arguments = .ok (start, labels) ∧
      Forced.Reaches document.file labels start finish ∧
      finish.control = .halt (.defined (.loaded (.specified (.integer number)))) ∧ finish.memory.stdout = ""
    rename_i annotations patternAnnotations outerType first saveAnnotations returnLabel returnType
      parameter parameterInfo bodyAnnotations symbolAnnotations occurrence
    split at bodyRecognized
    · show ∃ start labels finish, initial document.file enums arguments = .ok (start, labels) ∧
        Forced.Reaches document.file labels start finish ∧
        finish.control = .halt (.defined (.loaded (.specified (.integer number)))) ∧ finish.memory.stdout = ""
      rename_i accepted
      obtain ⟨sameParameter, saveFree⟩ := accepted
      have saved : ReturnLit.ReturnLabel labels returnLabel := by
        rw [labelDefinitions]
        exact ReturnLit.returnLabel_body sameParameter saveFree
      let ending : EE := .mk saveAnnotations
        (.save (returnLabel, returnType) [(parameter, parameterInfo)]
          (.mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence)))))
      have boundary : ReturnLit.NoBoundary
          [.strongBind (.mk patternAnnotations (.base (none, outerType))) ending ∅,
            .annotations accesses] := by simp [ReturnLit.NoBoundary, hasBoundary]
      obtain ⟨finish, output, returned⟩ := retLit_forced returnLabel saved first number bodyRecognized ∅
        boundary memory
      have unchangedOutput : finish.stdout = "" := by simp [output, stdout]
      exact ⟨start, labels, _, started,
        entered.trans ((sequence_forced annotations _ first _ ∅ _ memory).trans returned),
        rfl, unchangedOutput⟩
    · cases bodyRecognized
  · cases bodyRecognized

end Silmaril.Compiler.Core.ElaborationTotal
