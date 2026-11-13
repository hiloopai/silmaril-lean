module

public import Silmaril.Compiler.Core.ElaborationSemantics.Defs

/-! Local actual-Core reachability for constant returns. These reuse the
imported Core dynamics and `ReturnLit`/`ConvInt` results. Runtime recognition,
integer bounds, label resolution and procedure context remain explicit
premises; no accepting Ail translator or whole compiler theorem is asserted.
-/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationSemantics
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.SeqReach (Reaches PureEval focusMemory)
open Silmaril.Compile.Core.Verified

variable {file : Program} {labels : Labels}

/-- A bound around an arbitrary pure computation discharges its own frame.
The location of the enclosed `pure`, rather than the bound, focuses memory. -/
theorem bound_pure_reaches (boundAnnotations expressionAnnotations : List Annot)
    {expression : PE} {env : Env} {value : Val}
    (evaluates : PureEval file labels expression env value)
    (frames : List Frame) (memory : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk boundAnnotations
        (.bound (.mk expressionAnnotations (.pure expression)))) env, frames, memory⟩
      ⟨.value value, frames, focusMemory expressionAnnotations memory⟩ := by
  have enter : Reaches file labels
      ⟨.effectExpr (.mk boundAnnotations
        (.bound (.mk expressionAnnotations (.pure expression)))) env, frames, memory⟩
      ⟨.effectExpr (.mk expressionAnnotations (.pure expression)) env, .bound :: frames, memory⟩ :=
    ReturnLit.bound_reaches boundAnnotations _ env frames memory
  have compute : Reaches file labels
      ⟨.effectExpr (.mk expressionAnnotations (.pure expression)) env, .bound :: frames, memory⟩
      ⟨.value value, .bound :: frames, focusMemory expressionAnnotations memory⟩ :=
    SeqReach.effect_pure_reaches expressionAnnotations evaluates _ memory
  have leave : Reaches file labels
      ⟨.value value, .bound :: frames, focusMemory expressionAnnotations memory⟩
      ⟨.value value, frames, focusMemory expressionAnnotations memory⟩ :=
    ReturnLit.pop_reaches value frames _ (.inl rfl)
  exact enter.trans (compute.trans leave)

/-- Annotated variant of `CallReach.run_saved_value`. Return-body and run
locations are retained; a renamed display description is allowed for the
return parameter's occurrence. Intervening local frames are discarded and
the caller resumes with the computed value. -/
theorem run_saved_value (runAnnotations bodyAnnotations symbolAnnotations : List Annot)
    (label parameter occurrence : Sym) (same : occurrence.key = parameter.key)
    (env : Env) (argument : PE) (value : Val)
    (evaluates : PureEval file labels argument env value)
    (localFrames caller : List Frame) (localLabels : Labels) (memory : Mem.Concrete.State)
    (context : procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup label = some
      ([parameter], .mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence))))) :
    Reaches file labels
      ⟨.effectExpr (.mk runAnnotations (.run () label [argument])) env,
        localFrames ++ .procedureReturn localLabels :: caller, memory⟩
      ⟨.value value, caller, focusMemory bodyAnnotations (focusMemory runAnnotations memory)⟩ := by
  let frames : List Frame := localFrames ++ .procedureReturn localLabels :: caller
  let focused : Mem.Concrete.State := focusMemory runAnnotations memory
  let resultEnv : Env := extendEnv ([parameter].zip [value]) env
  have enter : Reaches file labels
      ⟨.effectExpr (.mk runAnnotations (.run () label [argument])) env, frames, memory⟩
      ⟨.pureExpr argument env, .runLabel label [] [] env :: frames, focused⟩ :=
    Straight.focus_reaches Straight.request_run
  have compute : Reaches file labels
      ⟨.pureExpr argument env, .runLabel label [] [] env :: frames, focused⟩
      ⟨.value value, .runLabel label [] [] env :: frames, focused⟩ := evaluates _ _
  have jump : Reaches file labels
      ⟨.value value, .runLabel label [] [] env :: frames, focused⟩
      ⟨.effectExpr (.mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence))))
        resultEnv, .procedureReturn localLabels :: caller, focused⟩ :=
    LoopReach.run_arguments_reaches .nil [] value frames _ focused localLabels [parameter]
      _ context lookup rfl
  have parameterValue : resultEnv.lookup occurrence = some value := ConvInt.lookup_one same
  have body : Reaches file labels
      ⟨.effectExpr (.mk bodyAnnotations (.pure (.mk symbolAnnotations () (.sym occurrence))))
        resultEnv, .procedureReturn localLabels :: caller, focused⟩
      ⟨.value value, .procedureReturn localLabels :: caller, focusMemory bodyAnnotations focused⟩ :=
    SeqReach.effect_pure_reaches bodyAnnotations
      (SeqReach.pure_symbol symbolAnnotations occurrence resultEnv value parameterValue) _ focused
  have leave : Reaches file labels
      ⟨.value value, .procedureReturn localLabels :: caller, focusMemory bodyAnnotations focused⟩
      ⟨.value value, caller, focusMemory bodyAnnotations focused⟩ :=
    CallReach.return_reaches value localLabels caller _
  exact enter.trans (compute.trans (jump.trans (body.trans leave)))

/-- The existing runtime recognizer establishes the actual pure call's value,
uniformly in continuations and memory, without substituting a primitive for
`conv_loaded_int`. -/
theorem converted_int_pure (conversion temporary : Sym) (number : Int)
    (recognized : ConvInt.isConvLoadedInt file conversion = true)
    (bounds : ConvInt.IsInt number) (env : Env)
    (callAnnotations typeAnnotations ctypeAnnotations symbolAnnotations : List Annot) :
    PureEval file labels
      (.mk callAnnotations () (.call (.sym conversion)
        [.mk typeAnnotations () (.val (.ctype (ConvInt.intTy ctypeAnnotations))),
         .mk symbolAnnotations () (.sym temporary)]))
      (extendEnv [(temporary, .loaded (.specified (.integer number)))] env)
      (.loaded (.specified (.integer number))) := by
  intro frames memory
  let value : Val := .loaded (.specified (.integer number))
  let localEnv : Env := extendEnv [(temporary, value)] env
  have lookup : localEnv.lookup temporary = some value := ConvInt.lookup_one rfl
  have evaluation : Silmaril.Cerberus.Core.PureEval.Eval file
      (Silmaril.Cerberus.Core.PureEval.tagsOf file memory) localEnv
      (.inl (.mk callAnnotations () (.call (.sym conversion)
        [.mk typeAnnotations () (.val (.ctype (ConvInt.intTy ctypeAnnotations))),
         .mk symbolAnnotations () (.sym temporary)]))) (.inl value) :=
    ConvInt.convLoadedInt_eval recognized bounds (.cons .val (.cons (.sym lookup) .nil))
  exact (Silmaril.Cerberus.Core.PureEval.Eval.sound file _ evaluation) labels frames memory rfl

/-- Direct statement rule for the actual bounded literal/binding/runtime-call
shape. An enclosing function supplies its actual saved return-label lookup.
The rule resumes the caller and preserves stdout, including under local frames. -/
theorem constant_return_reaches
    (sequenceAnnotations patternAnnotations boundAnnotations expressionAnnotations
      valueAnnotations runAnnotations callAnnotations typeAnnotations ctypeAnnotations
      symbolAnnotations bodyAnnotations returnSymbolAnnotations : List Annot)
    (temporary label conversion parameter occurrence : Sym)
    (same : occurrence.key = parameter.key) (number : Int)
    (recognized : ConvInt.isConvLoadedInt file conversion = true)
    (bounds : ConvInt.IsInt number) (env : Env)
    (localFrames caller : List Frame) (localLabels : Labels) (memory : Mem.Concrete.State)
    (context : procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup label = some
      ([parameter], .mk bodyAnnotations (.pure (.mk returnSymbolAnnotations () (.sym occurrence))))) :
    Reaches file labels
      ⟨.effectExpr (.mk sequenceAnnotations
        (.sseq (.mk patternAnnotations (.base (some temporary, .loaded .integer)))
          (.mk boundAnnotations (.bound (.mk expressionAnnotations
            (.pure (.mk valueAnnotations () (.val (.loaded (.specified (.integer number)))))))))
          (.mk runAnnotations (.run () label
            [.mk callAnnotations () (.call (.sym conversion)
              [.mk typeAnnotations () (.val (.ctype (ConvInt.intTy ctypeAnnotations))),
               .mk symbolAnnotations () (.sym temporary)])])))) env,
        localFrames ++ .procedureReturn localLabels :: caller, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), caller,
        focusMemory bodyAnnotations (focusMemory runAnnotations (focusMemory expressionAnnotations memory))⟩ := by
  let value : Val := .loaded (.specified (.integer number))
  let localEnv : Env := extendEnv [(temporary, value)] env
  let frames : List Frame := localFrames ++ .procedureReturn localLabels :: caller
  let convertedArgument : PE := .mk callAnnotations () (.call (.sym conversion)
    [.mk typeAnnotations () (.val (.ctype (ConvInt.intTy ctypeAnnotations))),
     .mk symbolAnnotations () (.sym temporary)])
  let returnBody : EE := .mk runAnnotations (.run () label [convertedArgument])
  let pattern : Pattern Sym := .mk patternAnnotations (.base (some temporary, .loaded .integer))
  let boundBody : EE := .mk boundAnnotations (.bound (.mk expressionAnnotations
    (.pure (.mk valueAnnotations () (.val (.loaded (.specified (.integer number))))))))
  have literal : PureEval file labels
      (.mk valueAnnotations () (.val (.loaded (.specified (.integer number))))) env value :=
    SeqReach.pure_value valueAnnotations (.loaded (.specified (.integer number))) env
  have matched : matchPattern
      (.mk patternAnnotations (.base (some temporary, .loaded .integer))) value =
      some [(temporary, value)] := by simp [matchPattern]
  have sequence : Reaches file labels
      ⟨.effectExpr (.mk sequenceAnnotations (.sseq pattern boundBody returnBody)) env, frames, memory⟩
      ⟨.effectExpr returnBody localEnv, frames, focusMemory expressionAnnotations memory⟩ :=
    SeqReach.sseq_reaches sequenceAnnotations
      (bound_pure_reaches boundAnnotations expressionAnnotations literal _ memory) matched
  have converted : PureEval file labels convertedArgument localEnv value :=
    converted_int_pure conversion temporary number recognized bounds env
      callAnnotations typeAnnotations ctypeAnnotations symbolAnnotations
  have returned : Reaches file labels
      ⟨.effectExpr returnBody localEnv, frames, focusMemory expressionAnnotations memory⟩
      ⟨.value value, caller,
        focusMemory bodyAnnotations (focusMemory runAnnotations (focusMemory expressionAnnotations memory))⟩ :=
    run_saved_value runAnnotations bodyAnnotations returnSymbolAnnotations
      label parameter occurrence same localEnv _ value converted localFrames caller localLabels
      (focusMemory expressionAnnotations memory) context lookup
  exact sequence.trans returned

end Silmaril.Compiler.Core.ElaborationSemantics
