module

public import Silmaril.Compiler.Native.Correctness.AdditionFocused.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionFocused
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics Silmaril.Cerberus.Core.PureEval
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core
open Silmaril.Compiler.Native.Correctness.AdditionSource
open Silmaril.Cerberus.Core.DiagnosticOperands
open Construction

/-- The actual generated weak/unsequenced addition expression has a forced
finite execution for all independent nonoverflowing operands. This local
statement preserves its exact empty access-annotation continuation and accounts
for the actual diagnostic memory update from arbitrary incoming memory. -/
theorem expression_forced (file : Dynamics.Program) (labels : Labels) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State)
    (left right : Int) (bounded : Bounds left right) :
    Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (coreExpression left right) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: frames, focused memory⟩ := by
  let pattern := Pattern.mk [] (.ctor .tuple [operands.left.pattern, operands.right.pattern])
  let continuation := Frame.effectBind pattern (pureEffect resultPure) environment :: frames
  let extended := extendEnv [(fresh 101, .loaded (.specified (.integer left))),
    (fresh 102, .loaded (.specified (.integer right)))] environment
  have begin : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (coreExpression left right) environment, frames, memory⟩
      ⟨.effectExpr (.mk [] (.unseq [Silmaril.Cerberus.Core.PureOperands.constant left,
        Silmaril.Cerberus.Core.PureOperands.constant right])) environment, continuation, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, coreExpression, continuation, pattern]
  have operandPath := Silmaril.Cerberus.Core.DiagnosticOperands.unseq_pair_forced file labels left right
    environment continuation memory
  have bindOperands : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
        .annotations [] :: continuation, focused memory⟩
      ⟨.effectExpr (pureEffect resultPure) extended, .annotations [] :: frames, focused memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, continuation, pattern, operands, symbolPattern,
      symbolPatternWith, matchPattern, matchPatterns, extended]
  have beginResult : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (pureEffect resultPure) extended, .annotations [] :: frames, focused memory⟩
      ⟨.pureExpr resultPure extended, .diagnosticLocation (focused memory).currentLocation :: .annotations [] :: frames, focused memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, pureEffect]
  have getLeft : extended.lookup (fresh 101) = some (.loaded (.specified (.integer left))) :=
    Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  have getRight : extended.lookup (fresh 102) = some (.loaded (.specified (.integer right))) := by
    change (extendEnv [(fresh 101, .loaded (.specified (.integer left)))]
      (extendEnv [(fresh 102, .loaded (.specified (.integer right)))] environment)).lookup (fresh 102) = _
    rw [Silmaril.Compile.Core.Verified.ConvInt.lookup_one_other (by decide +kernel)]
    exact Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  have evaluated := ElaborationTotal.pureEvaluation_forced file (tagsOf file (focused memory))
    (result_eval file (tagsOf file (focused memory)) extended left right bounded getLeft getRight) labels
      (.diagnosticLocation (focused memory).currentLocation :: .annotations [] :: frames) (focused memory) rfl
  have pop : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.loaded (.specified (.integer (left + right)))),
        .diagnosticLocation (focused memory).currentLocation :: .annotations [] :: frames, focused memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: frames, focused memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  exact begin.trans (operandPath.trans (bindOperands.trans (beginResult.trans (evaluated.trans pop))))

/-- The generated full-expression bound consumes the exact empty access
annotation produced by actual unsequenced evaluation. -/
theorem wrapped_expression_forced (file : Dynamics.Program) (labels : Labels) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State)
    (left right : Int) (bounded : Bounds left right) :
    Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), frames, focused memory⟩ := by
  have enter : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, frames, memory⟩
      ⟨.effectExpr (coreExpression left right) environment, .bound :: frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  have expression := expression_forced file labels environment (.bound :: frames) memory left right bounded
  have leave : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: .bound :: frames, focused memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), frames, focused memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  exact enter.trans (expression.trans leave)

/-- There is a real forced terminal execution of the local generated
full-expression model, independent of fuel or any runner's choice policy. -/
theorem local_model_forced (left right : Int) (bounded : Bounds left right)
    (environment : Env) (memory : Mem.Concrete.State) :
    Silmaril.Cerberus.Core.Forced.Reaches (localModel left right environment memory).program
      (localModel left right environment memory).labels (localModel left right environment memory).initialState
      ⟨.halt (.defined (.loaded (.specified (.integer (left + right))))), [], focused memory⟩ := by
  have expression := wrapped_expression_forced (bindings left right).toFile ∅ environment [] memory
    left right bounded
  refine expression.trans ?_
  apply Silmaril.Cerberus.Core.Forced.end_ (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

/-- Universal satisfaction quantifies all actual finite prefixes and all
infinite executions of the local actual generated expression. Whole C startup
and the enclosing return transfer are separate from this explicit local slice. -/
theorem local_model_satisfies (left right : Int) (bounded : Bounds left right)
    (environment : Env) (memory : Mem.Concrete.State)
    (stdout : memory.stdout = "") :
    Silmaril.Cerberus.Institution.Satisfies (localModel left right environment memory)
      (ElaborationTotal.returnsInteger (left + right)) := by
  have forced := local_model_forced left right bounded environment memory
  intro behavior realized
  cases behavior with
  | finite actions state =>
    intro outcome halted
    have reachable := (Silmaril.Compiler.Category.Cerberus.Process.finite_iff_reaches
      (localModel left right environment memory) state).mp ⟨actions, realized⟩
    have same := Silmaril.Cerberus.Core.Forced.terminal_unique forced rfl reachable halted
    cases same
    exact ⟨Control.halt.inj halted.symm, (focused_stdout memory).trans stdout⟩
  | infinite states actions =>
    exact Silmaril.Cerberus.Core.Forced.no_infinite forced rfl states actions realized.1 realized.2

end Silmaril.Compiler.Native.Correctness.AdditionFocused
