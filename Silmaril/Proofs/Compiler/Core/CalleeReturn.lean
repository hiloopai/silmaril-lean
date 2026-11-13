module

public import Silmaril.Compiler.Core.CalleeReturn.Defs
public import Silmaril.Compiler.Core.ElaborationTotal.Thms

/-! Adapt the actual literal-return forced paths to a callee boundary. Every
edge is an actual Core transition; caller frames are retained without assuming
they are boundary-free. Only this recognized pure-literal domain has the stated
memory preservation. -/
@[expose] public section

namespace Silmaril.Compiler.Core.CalleeReturn
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Compile.Core.Verified
open ReturnConst (focusMemory focusMemory_stdout)
open Silmaril.Cerberus.Core
open Silmaril.Compiler.Core.ElaborationTotal (pureEvaluation_forced)
variable {file : Program} {labels : Labels}

theorem LocationOnly.trans {first middle last : Mem.Concrete.State}
    (left : LocationOnly first middle) (right : LocationOnly middle last) :
    LocationOnly first last := by
  obtain ⟨location, rfl⟩ := left
  obtain ⟨finalLocation, rfl⟩ := right
  exact ⟨finalLocation, rfl⟩

theorem LocationOnly.stdout {before after : Mem.Concrete.State}
    (onlyLocation : LocationOnly before after) : after.stdout = before.stdout := by
  obtain ⟨location, rfl⟩ := onlyLocation
  rfl

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

theorem focus_location (annotations : List Annot) (memory : Mem.Concrete.State) :
    LocationOnly memory (focusMemory annotations memory) :=
  ⟨_, (focusMemory_update annotations memory).symm⟩

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


theorem procedureContext_prefix {localFrames : List Frame} (boundary : ReturnLit.NoBoundary localFrames)
    (ownLabels : Labels) (callerFrames : List Frame) (fallback : Labels) :
    procedureContext fallback (localFrames ++ .procedureReturn ownLabels :: callerFrames) =
      (ownLabels, .procedureReturn ownLabels :: callerFrames) := by
  induction localFrames with
  | nil => rfl
  | cons frame localFrames previous =>
    unfold ReturnLit.NoBoundary hasBoundary at boundary
    simp only [List.any_cons, Bool.or_eq_false_iff] at boundary
    cases frame <;> simp_all [procedureContext, ReturnLit.NoBoundary, hasBoundary]

/-- A return label is resolved in the callee, and only the callee localFrames and
boundary are discarded. The arbitrary caller continuation is preserved exactly. -/
theorem jump_forced_return {returnLabel label : Sym} (same : label.key = returnLabel.key)
    (ownLabels : Labels) (saved : ReturnLit.ReturnLabel ownLabels returnLabel)
    (value : Val) (environment : Env) {localFrames : List Frame}
    (boundary : ReturnLit.NoBoundary localFrames) (callerFrames : List Frame)
    (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels
        ⟨.value value, .runLabel label [] [] environment ::
          (localFrames ++ .procedureReturn ownLabels :: callerFrames), memory⟩
        ⟨.value value, callerFrames, finish⟩ := by
  obtain ⟨parameter, bodyAnnotations, symbolAnnotations, occurrence, sameParameter, lookup⟩ := saved
  have labelLookup : ownLabels.lookup label = some
      ([parameter], .mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence)))) := by
    rw [ReturnLit.lookup_key same]
    exact lookup
  refine ⟨focusMemory bodyAnnotations memory, focus_location bodyAnnotations memory, ?_⟩
  refine (Forced.next (c' := .effectExpr (.mk bodyAnnotations (.pure (.mk symbolAnnotations ()
    (.sym occurrence)))) (extendEnv ([parameter].zip [value]) environment))
    (k' := .procedureReturn ownLabels :: callerFrames)
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling, requestJump, hasBoundary, List.any_append,
      jump, jumpDestination, procedureContext_prefix boundary, labelLookup]
  refine (effectPure_forced bodyAnnotations _ _ _ memory).trans ?_
  refine (Forced.next (c' := .value value)
    (k' := .diagnosticLocation memory.currentLocation :: .procedureReturn ownLabels :: callerFrames)
    (by intro outcome impossible; cases impossible) ?_).trans ?_
  · have parameterValue : (extendEnv [(parameter, value)] environment).lookup occurrence = some value :=
      ConvInt.lookup_one sameParameter
    simp [request, requestAux, awaitsScheduling, parameterValue]
  refine (pop_forced _ _ _ (.inr ⟨_, rfl⟩)).trans ?_
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]


theorem returnsTo_cons {ownLabels : Labels} {callerFrames frames : List Frame}
    {frame : Frame} (boundary : ReturnsTo ownLabels callerFrames frames)
    (localFrame : match frame with | .procedureReturn _ | .globalResult .. => False | _ => True) :
    ReturnsTo ownLabels callerFrames (frame :: frames) := by
  obtain ⟨localFrames, noBoundary, rfl⟩ := boundary
  exact ⟨frame :: localFrames, ReturnLit.noBoundary_cons noBoundary localFrame, rfl⟩

theorem jump_boundary {returnLabel label : Sym} (same : label.key = returnLabel.key)
    (ownLabels : Labels) (saved : ReturnLit.ReturnLabel ownLabels returnLabel)
    (value : Val) (environment : Env) {frames : List Frame} (callerFrames : List Frame)
    (boundary : ReturnsTo ownLabels callerFrames frames) (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels ⟨.value value, .runLabel label [] [] environment :: frames, memory⟩
        ⟨.value value, callerFrames, finish⟩ := by
  obtain ⟨localFrames, noBoundary, rfl⟩ := boundary
  exact jump_forced_return same ownLabels saved value environment noBoundary callerFrames memory

theorem retLit_forced_return (returnLabel : Sym) (ownLabels : Labels)
    (saved : ReturnLit.ReturnLabel ownLabels returnLabel)
    (expression : EE) (number : Int) (recognized : ReturnLit.retLit file returnLabel expression = some number)
    (environment : Env) {frames : List Frame} (callerFrames : List Frame)
    (boundary : ReturnsTo ownLabels callerFrames frames)
    (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels ⟨.effectExpr expression environment, frames, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩ := by
  unfold ReturnLit.retLit at recognized
  split at recognized
  · show ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels ⟨.effectExpr _ environment, frames, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩
    rename_i _ annotations patternAnnotations temporary type boundAnnotations expressionAnnotations
      valueAnnotations otherNumber runAnnotations label callAnnotations conversion typeAnnotations
      ctypeAnnotations symbolAnnotations occurrence
    split at recognized
    · show ∃ finish, LocationOnly memory finish ∧
        Forced.Reaches file labels ⟨.effectExpr _ environment, frames, memory⟩
          ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩
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
      obtain ⟨finish, location, jumped⟩ := jump_boundary (file := file) sameLabel ownLabels saved value extended callerFrames boundary
        (focusMemory runAnnotations focused)
      refine ⟨finish, (focus_location expressionAnnotations memory).trans
        ((focus_location runAnnotations focused).trans location), ?_⟩
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
    obtain ⟨finish, location, returned⟩ := retLit_forced_return returnLabel ownLabels saved first number recognized environment
      (frames := .strongBind (.mk patternAnnotations (.base (none, type))) rest environment :: frames)
      callerFrames (returnsTo_cons boundary trivial) memory
    exact ⟨finish, location, (sequence_forced annotations _ first rest environment frames memory).trans returned⟩
  · cases recognized
termination_by sizeOf expression


/-- A recognized actual literal body returns to its caller, using the label map
installed by the actual procedure dispatch rule. -/
theorem body_forced_return (body : EE) (number : Int)
    (recognized : ReturnLit.recognizeBody file body = some number)
    (environment : Env) (callerFrames : List Frame) (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels
        ⟨.effectExpr body environment,
          .procedureReturn (Map.ofList (saves body).reverse) :: callerFrames, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩ := by
  unfold ReturnLit.recognizeBody at recognized
  split at recognized
  · show ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels
        ⟨.effectExpr _ environment, .procedureReturn _ :: callerFrames, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩
    rename_i annotations patternAnnotations outerType first saveAnnotations returnLabel returnType
      parameter parameterInfo bodyAnnotations symbolAnnotations occurrence
    split at recognized
    · show ∃ finish, LocationOnly memory finish ∧
        Forced.Reaches file labels
          ⟨.effectExpr _ environment, .procedureReturn _ :: callerFrames, memory⟩
          ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩
      rename_i accepted
      obtain ⟨sameParameter, saveFree⟩ := accepted
      let ending : EE := .mk saveAnnotations
        (.save (returnLabel, returnType) [(parameter, parameterInfo)]
          (.mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence)))))
      let body : EE := .mk annotations (.sseq (.mk patternAnnotations (.base (none, outerType))) first ending)
      let ownLabels := Map.ofList (saves body).reverse
      have saved : ReturnLit.ReturnLabel ownLabels returnLabel :=
        ReturnLit.returnLabel_body sameParameter saveFree
      have localBoundary : ReturnLit.NoBoundary
          [.strongBind (.mk patternAnnotations (.base (none, outerType))) ending environment] := by
        simp [ReturnLit.NoBoundary, hasBoundary]
      have boundary : ReturnsTo ownLabels callerFrames
          (.strongBind (.mk patternAnnotations (.base (none, outerType))) ending environment ::
            .procedureReturn ownLabels :: callerFrames) :=
        ⟨[.strongBind (.mk patternAnnotations (.base (none, outerType))) ending environment],
          localBoundary, rfl⟩
      obtain ⟨finish, location, returned⟩ := retLit_forced_return returnLabel ownLabels saved first number
        recognized environment callerFrames boundary memory
      exact ⟨finish, location, (sequence_forced annotations _ first ending environment _ memory).trans returned⟩
    · cases recognized
  · cases recognized

/-- Actual known zero-argument procedure dispatch followed by a recognized
literal return. The caller environment and its complete continuation are inputs;
no statement about eventual caller behavior or general call safety is assumed. -/
theorem procedure_forced_return (callee : Sym) (body : EE) (number : Int)
    (ordinary : libraryCall file callee = none)
    (resolved : procedureBody file callee [] = .ok (body, []))
    (recognized : ReturnLit.recognizeBody file body = some number)
    (environment : Env) (callerFrames : List Frame) (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧
      Forced.Reaches file labels
        ⟨.apply (.procedure environment) [.loaded (.specified (.pointer (.function callee)))],
          callerFrames, memory⟩
        ⟨.value (.loaded (.specified (.integer number))), callerFrames, finish⟩ := by
  obtain ⟨finish, location, returned⟩ := body_forced_return body number recognized
    (extendEnv [] environment) callerFrames memory
  refine ⟨finish, location, (Forced.scheduled (by intro outcome impossible; cases impossible) ?_).trans returned⟩
  simp [request, requestAux, awaitsScheduling, ordinary, resolved, scheduledRequest]

end Silmaril.Compiler.Core.CalleeReturn
