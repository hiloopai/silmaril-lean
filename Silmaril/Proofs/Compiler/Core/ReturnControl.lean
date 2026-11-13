module

public import Silmaril.Compiler.Core.ReturnControl.Defs
/-! Public generic actual-Core administrative and return-control lemmas.
These factor the existing ElaborationTotal proof pattern without changing its
source or replacing any actual transition or runtime function. -/
@[expose] public section
namespace Silmaril.Compiler.Core.ReturnControl
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration.Construction
open ReturnConst (focusMemory focusMemory_stdout)

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

theorem focus_forced {annotations : List Annot} {node : ExprNode Codec.wireModel Unit Unit Sym}
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

theorem effectPure_forced (annotations : List Annot) (expression : PE) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk annotations (.pure expression)) environment, frames, memory⟩
      ⟨.pureExpr expression environment, .diagnosticLocation memory.currentLocation :: frames,
        focusMemory annotations memory⟩ :=
  focus_forced (ReturnConst.request_effect_pure file labels annotations expression environment frames memory)

theorem sequence_forced (annotations : List Annot) (pattern : Pattern Sym)
    (first rest : EE) (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk annotations (.sseq pattern first rest)) environment, frames, memory⟩
      ⟨.effectExpr first environment, .strongBind pattern rest environment :: frames, memory⟩ := by
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

theorem pop_forced {frame : Frame} (value : Val) (frames : List Frame)
    (memory : Mem.Concrete.State) (kind : frame = .bound ∨ ∃ location, frame = .diagnosticLocation location) :
    Forced.Reaches file labels ⟨.value value, frame :: frames, memory⟩ ⟨.value value, frames, memory⟩ := by
  apply Forced.next (by intro outcome impossible; cases impossible)
  rcases kind with rfl | ⟨location, rfl⟩ <;> simp [request, requestAux, awaitsScheduling]

theorem value_forced_halt (value : Val) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.value value, [], memory⟩ ⟨.halt (.defined value), [], memory⟩ := by
  apply Forced.end_ (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

theorem jump_forced_halt {returnLabel label : Sym} (same : label.key = returnLabel.key)
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

/-- A genuine recognized conversion call and actual saved-label jump return
every independently bounded signed integer from any nonboundary continuation.
The environment read is explicit; no runtime evaluation is assumed. -/
theorem converted_return_forced (returnLabel label conversion occurrence : Sym)
    (sameLabel : label.key = returnLabel.key) (saved : ReturnLit.ReturnLabel labels returnLabel)
    (recognized : ConvInt.isConvLoadedInt file conversion = true)
    (number : Int) (bounded : ConvInt.IsInt number) (environment : Env)
    (observed : environment.lookup occurrence = some (.loaded (.specified (.integer number))))
    {frames : List Frame} (boundary : ReturnLit.NoBoundary frames) (memory : Mem.Concrete.State) :
    ∃ finish, finish.stdout = memory.stdout ∧
      Forced.Reaches file labels ⟨.effectExpr (convertedReturn label conversion occurrence) environment, frames, memory⟩
        ⟨.halt (.defined (.loaded (.specified (.integer number)))), [], finish⟩ := by
  let value : Val := .loaded (.specified (.integer number))
  let invocation := call (.sym conversion) [ctype signedIntType, symbolPure occurrence]
  have operands : Eval file (tagsOf file memory) environment
      (.inr [ctype signedIntType, symbolPure occurrence]) (.inr [.ctype signedIntType, value]) :=
    .cons .val (.cons (.sym observed) .nil)
  have evaluation : Eval file (tagsOf file memory) environment (.inl invocation) (.inl value) :=
    ConvInt.convLoadedInt_eval recognized bounded operands
  have begin : Forced.Reaches file labels
      ⟨.effectExpr (convertedReturn label conversion occurrence) environment, frames, memory⟩
      ⟨.pureExpr invocation environment, .runLabel label [] [] environment :: frames, memory⟩ := by
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [convertedReturn, invocation, Silmaril.Cerberus.Elaboration.Construction.run, request, requestAux, awaitsScheduling]
  have evaluated := ElaborationTotal.pureEvaluation_forced file _ evaluation labels
    (.runLabel label [] [] environment :: frames) memory rfl
  obtain ⟨finish, stdout, jumped⟩ := jump_forced_halt sameLabel saved value environment boundary memory
  exact ⟨finish, stdout, begin.trans (evaluated.trans jumped)⟩

/-- Universal whole-Core integer return plus one actual completed path fixes
exactly the existing process observation. Finite prefixes remain in the Core
model; this statement only projects completed process observations. -/
theorem integer_process_exact (document : Codec.Document) (arguments : List String)
    (start : Dynamics.State) (labels : Labels)
    (started : Silmaril.Compiler.Category.Cerberus.Process.Spec.coreStart document arguments = .ok (start, labels))
    (number : Int)
    (correct : Silmaril.Cerberus.Institution.Satisfies
      (Silmaril.Compiler.Category.Cerberus.Process.model document start labels) (ElaborationTotal.returnsInteger number))
    (finish : Dynamics.State) (reached : Relation.ReflTransGen (fun before after => ∃ action, Step document.file labels before action after) start finish)
    (halted : finish.control = .halt (.defined (.loaded (.specified (.integer number)))))
    (stdout : finish.memory.stdout = "")
    (observation : Silmaril.Compiler.Category.Cerberus.Process.Spec.Obs) :
    Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh document arguments observation ↔
      observation = .exit (number % 256).toNat [] := by
  constructor
  · show Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh document arguments observation →
      observation = .exit (number % 256).toNat []
    intro behavior
    obtain ⟨execution, realized, observed⟩ :=
      (Silmaril.Compiler.Category.Cerberus.Process.coreBeh_iff_realises_observes document arguments start labels started observation).1 behavior
    have terminal : ElaborationTotal.returnsInteger number execution := correct execution realized
    cases execution with
    | finite actions state =>
      show observation = .exit (number % 256).toNat []
      cases observation with
      | exit status bytes =>
        show (.exit status bytes : Silmaril.Compiler.Category.Cerberus.Process.Spec.Obs) = .exit (number % 256).toNat []
        obtain ⟨value, stateHalted, statusAllowed, output⟩ := observed
        obtain ⟨returned, outputEmpty⟩ := terminal (.defined value) stateHalted
        have valueEquality : value = .loaded (.specified (.integer number)) := Outcome.defined.inj returned
        have statusEquality : status = (number % 256).toNat := by
          simpa only [valueEquality, Silmaril.Compiler.Category.Cerberus.Process.Spec.exitStatuses] using statusAllowed
        have bytesEquality : bytes = [] := by
          simpa [Silmaril.Compiler.Category.Cerberus.Process.Spec.coreBytes, outputEmpty] using output.symm
        exact congrArg₂ (fun status bytes => (.exit status bytes : Silmaril.Compiler.Category.Cerberus.Process.Spec.Obs))
          statusEquality bytesEquality
      | abort bytes =>
        have impossible : Outcome.aborted = .defined (.loaded (.specified (.integer number))) :=
          (terminal .aborted observed.1).1
        cases impossible
      | trap | fault | diverges | exhausted => exact observed.elim
    | infinite states actions => exact terminal.elim
  · intro same
    have reach : Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreReach document arguments finish := by
      apply (Silmaril.Compiler.Category.Cerberus.Process.coreReach_iff_realises document arguments start labels started finish).2
      exact (Silmaril.Compiler.Category.Cerberus.Process.finite_iff_reaches _ finish).2 reached
    have completed : Silmaril.Compiler.Category.Cerberus.Process.Spec.CoreBeh document arguments
        (.exit (number % 256).toNat (Silmaril.Compiler.Category.Cerberus.Process.Spec.coreBytes finish.memory.stdout)) :=
      .exit reach halted (by simp [Silmaril.Compiler.Category.Cerberus.Process.Spec.exitStatuses])
    simpa [same, stdout, Silmaril.Compiler.Category.Cerberus.Process.Spec.coreBytes] using completed

end Silmaril.Compiler.Core.ReturnControl
