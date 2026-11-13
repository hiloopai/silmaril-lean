module

public import Silmaril.Compiler.Native.Correctness.AdditionSource.Defs
public import Silmaril.Cerberus.Core.PureOperands.Thms
public import Silmaril.Compiler.Core.ElaborationTotal.Thms
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Correctness.AdditionSource
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core
open Construction
attribute [local cbv_eval] String.toUTF8_eq_toByteArray
attribute [local cbv_eval] Expressions.expression.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton

/-- The actual recursive expression dispatcher allocates the five source
operands and produces the explicit weak/unsequenced Core arithmetic syntax. -/
theorem expression_elaborates (left right : Int) :
    State.run (Expressions.expression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib (expression left right))
      (State.initial ⟨⟨[]⟩, 101, 1000⟩ .normal "Driver") =
      (.ok (coreExpression left right), State.initial ⟨⟨[]⟩, 106, 1000⟩ .normal "Driver") := by
  cbv

/-- Actual Functions elaboration succeeds for arbitrary mathematical operands;
source bounds are semantic inputs later, not elaboration-success premises. -/
theorem functions_elaborate (left right : Int) :
    Functions.elaborate config Silmaril.Cerberus.Target.emptyEnvironment runtime (program left right) ⟨⟨[]⟩, 100, 1000⟩ =
      (.ok (bindings left right), State.initial ⟨⟨[]⟩, 108, 1000⟩ .normal "Driver") := by
  cbv

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval

private theorem int_bounds (tags : Mem.Concrete.Tags) :
    Mem.Concrete.registeredIntegerBounds tags (.signed .int) = some (-2147483648, 2147483647) := rfl

/-- Actual direct Core signed-int conversion preserves every independently
bounded operand. Tags and the runtime file are unrestricted. -/
theorem convert_int (tags : Mem.Concrete.Tags) (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    primitive (.conv (.signed .int)) [.object (.integer number)] tags = .ok (.object (.integer number)) := by
  have lower : (-2147483648 : Int) ≤ number := bounded.1
  have upper : number ≤ (2147483647 : Int) := by
    have limit : number < (2147483648 : Int) := bounded.2
    omega
  simp [primitive, int_bounds, lower, upper, pure, Except.pure, Dynamics.integer]

/-- The actual exceptional-condition primitive accepts exactly this
nonoverflowing signed sum, without substituting an expected-result runtime. -/
theorem checked_add (tags : Mem.Concrete.Tags) (left right : Int)
    (bounded : LiteralEmission.IsInt32 (left + right)) :
    primitive (.catchInt (.signed .int) .add)
      [.object (.integer left), .object (.integer right)] tags = .ok (.object (.integer (left + right))) := by
  have lower : (-2147483648 : Int) ≤ left + right := bounded.1
  have upper : left + right ≤ (2147483647 : Int) := by
    have limit : left + right < (2147483648 : Int) := bounded.2
    omega
  simp [primitive, int_bounds, integerOp, lower, upper, pure, Except.pure, Dynamics.integer]

/-- Outside the independently stated signed-sum range, the actual primitive
retains its exceptional-condition UB rather than returning a wrapped value. -/
theorem checked_add_overflow (tags : Mem.Concrete.Tags) (left right : Int)
    (outside : ¬ LiteralEmission.IsInt32 (left + right)) :
    primitive (.catchInt (.signed .int) .add)
      [.object (.integer left), .object (.integer right)] tags =
      .error (.ub .unknown .UB036_exceptional_condition) := by
  by_cases lower : (-2147483648 : Int) ≤ left + right
  · have upper : ¬ left + right ≤ (2147483647 : Int) := by
      intro within
      apply outside
      change (-2147483648 : Int) ≤ left + right ∧ left + right < 2147483648
      exact ⟨lower, by omega⟩
    simp [primitive, int_bounds, integerOp, lower, upper]
    rfl
  · simp [primitive, int_bounds, integerOp, lower]
    rfl

/-- The pure case and checked arithmetic following the real unsequenced
operand computation evaluate for every independently bounded pair. -/
theorem result_eval (file : Dynamics.Program) (tags : Mem.Concrete.Tags) (environment : Env)
    (left right : Int) (bounded : Bounds left right)
    (leftValue : environment.lookup (fresh 101) = some (.loaded (.specified (.integer left))))
    (rightValue : environment.lookup (fresh 102) = some (.loaded (.specified (.integer right)))) :
    Eval file tags environment (.inl resultPure) (.inl (.loaded (.specified (.integer (left + right))))) := by
  unfold resultPure
  refine .case_ (xs := [(fresh 103, .object (.integer left)), (fresh 104, .object (.integer right))])
    (.ctor (.cons (.sym leftValue) (.cons (.sym rightValue) .nil)) rfl) rfl ?_
  have getLeft : (extendEnv [(fresh 103, .object (.integer left)), (fresh 104, .object (.integer right))]
      environment).lookup (fresh 103) = some (.object (.integer left)) := by
    exact Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  have getRight : (extendEnv [(fresh 103, .object (.integer left)), (fresh 104, .object (.integer right))]
      environment).lookup (fresh 104) = some (.object (.integer right)) := by
    rw [show extendEnv [(fresh 103, .object (.integer left)), (fresh 104, .object (.integer right))] environment =
      extendEnv [(fresh 103, .object (.integer left))]
        (extendEnv [(fresh 104, .object (.integer right))] environment) from rfl]
    rw [Silmaril.Compile.Core.Verified.ConvInt.lookup_one_other (by decide +kernel)]
    exact Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  exact .ctor (.cons (.catchInt
    (.cons (.convInt (.cons (.sym getLeft) .nil) (convert_int tags left bounded.1))
      (.cons (.convInt (.cons (.sym getRight) .nil) (convert_int tags right bounded.2.1)) .nil))
    (checked_add tags left right bounded.2.2)) .nil) rfl

/-- The actual generated weak/unsequenced addition expression has a forced
finite execution for all independent nonoverflowing operands. This local
statement preserves its exact empty access-annotation continuation and states
the incoming diagnostic-location boundary explicitly. -/
theorem expression_forced (file : Dynamics.Program) (labels : Labels) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State) (located : memory.currentLocation = .unknown)
    (left right : Int) (bounded : Bounds left right) :
    Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (coreExpression left right) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: frames, memory⟩ := by
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
  have operandPath := Silmaril.Cerberus.Core.PureOperands.unseq_pair_forced file labels left right
    environment continuation memory located
  have bindOperands : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
        .annotations [] :: continuation, memory⟩
      ⟨.effectExpr (pureEffect resultPure) extended, .annotations [] :: frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, continuation, pattern, operands, symbolPattern,
      symbolPatternWith, matchPattern, matchPatterns, extended]
  have beginResult : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (pureEffect resultPure) extended, .annotations [] :: frames, memory⟩
      ⟨.pureExpr resultPure extended, .diagnosticLocation memory.currentLocation :: .annotations [] :: frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, pureEffect]
  have getLeft : extended.lookup (fresh 101) = some (.loaded (.specified (.integer left))) :=
    Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  have getRight : extended.lookup (fresh 102) = some (.loaded (.specified (.integer right))) := by
    change (extendEnv [(fresh 101, .loaded (.specified (.integer left)))]
      (extendEnv [(fresh 102, .loaded (.specified (.integer right)))] environment)).lookup (fresh 102) = _
    rw [Silmaril.Compile.Core.Verified.ConvInt.lookup_one_other (by decide +kernel)]
    exact Silmaril.Compile.Core.Verified.ConvInt.lookup_one rfl
  have evaluated := ElaborationTotal.pureEvaluation_forced file (tagsOf file memory)
    (result_eval file (tagsOf file memory) extended left right bounded getLeft getRight) labels
      (.diagnosticLocation memory.currentLocation :: .annotations [] :: frames) memory rfl
  have pop : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.loaded (.specified (.integer (left + right)))),
        .diagnosticLocation memory.currentLocation :: .annotations [] :: frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  exact begin.trans (operandPath.trans (bindOperands.trans (beginResult.trans (evaluated.trans pop))))

/-- The generated full-expression bound consumes the exact empty access
annotation produced by actual unsequenced evaluation. -/
theorem wrapped_expression_forced (file : Dynamics.Program) (labels : Labels) (environment : Env)
    (frames : List Frame) (memory : Mem.Concrete.State) (located : memory.currentLocation = .unknown)
    (left right : Int) (bounded : Bounds left right) :
    Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), frames, memory⟩ := by
  have enter : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, frames, memory⟩
      ⟨.effectExpr (coreExpression left right) environment, .bound :: frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  have expression := expression_forced file labels environment (.bound :: frames) memory located left right bounded
  have leave : Silmaril.Cerberus.Core.Forced.Reaches file labels
      ⟨.value (.loaded (.specified (.integer (left + right)))), .annotations [] :: .bound :: frames, memory⟩
      ⟨.value (.loaded (.specified (.integer (left + right)))), frames, memory⟩ := by
    apply Silmaril.Cerberus.Core.Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  exact enter.trans (expression.trans leave)

/-- There is a real forced terminal execution of the local generated
full-expression model, independent of fuel or any runner's choice policy. -/
theorem local_model_forced (left right : Int) (bounded : Bounds left right)
    (environment : Env) (memory : Mem.Concrete.State) (located : memory.currentLocation = .unknown) :
    Silmaril.Cerberus.Core.Forced.Reaches (localModel left right environment memory).program
      (localModel left right environment memory).labels (localModel left right environment memory).initialState
      ⟨.halt (.defined (.loaded (.specified (.integer (left + right))))), [], memory⟩ := by
  have expression := wrapped_expression_forced (bindings left right).toFile ∅ environment [] memory
    located left right bounded
  refine expression.trans ?_
  apply Silmaril.Cerberus.Core.Forced.end_ (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

/-- Universal satisfaction quantifies all actual finite prefixes and all
infinite executions of the local actual generated expression. Whole C startup
and the enclosing return transfer are separate from this explicit local slice. -/
theorem local_model_satisfies (left right : Int) (bounded : Bounds left right)
    (environment : Env) (memory : Mem.Concrete.State) (located : memory.currentLocation = .unknown)
    (stdout : memory.stdout = "") :
    Silmaril.Cerberus.Institution.Satisfies (localModel left right environment memory)
      (ElaborationTotal.returnsInteger (left + right)) := by
  have forced := local_model_forced left right bounded environment memory located
  intro behavior realized
  cases behavior with
  | finite actions state =>
    intro outcome halted
    have reachable := (Silmaril.Compiler.Category.Cerberus.Process.finite_iff_reaches
      (localModel left right environment memory) state).mp ⟨actions, realized⟩
    have same := Silmaril.Cerberus.Core.Forced.terminal_unique forced rfl reachable halted
    cases same
    exact ⟨Control.halt.inj halted.symm, stdout⟩
  | infinite states actions =>
    exact Silmaril.Cerberus.Core.Forced.no_infinite forced rfl states actions realized.1 realized.2

end Silmaril.Compiler.Native.Correctness.AdditionSource
