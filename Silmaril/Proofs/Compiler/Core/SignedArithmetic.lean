module

public import Silmaril.Compiler.Core.SignedArithmetic.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionSource.Thms
public import Silmaril.Cerberus.Core.DiagnosticOperands.Thms
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
attribute [local cbv_eval] String.toUTF8_eq_toByteArray

theorem bounded_value (expression : Expression) (bounded : expression.Bounded) :
    Silmaril.Compiler.Native.Correctness.LiteralEmission.IsInt32 expression.value := by
  cases expression with
  | literal _ => exact bounded
  | binary _ _ _ => exact bounded.2.2

/-- Every node carries the existing concrete signed-int annotation; this does
not assume the independent arithmetic bounds or perform semantic evaluation. -/
theorem actual_type (expression : Expression) :
    Silmaril.Cerberus.GeneralizedTypes.expressionType config Silmaril.Cerberus.Target.emptyEnvironment expression.ail = .ok intType := by
  cases expression <;> rfl

/-- The recursive algebra is exactly the actual dependent typed-Ail expression
dispatcher on this source grammar, including the real operator allocation order. -/
theorem actual_dispatcher (expression : Expression) :
    Expressions.expression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail =
      expression.computation := by
  induction expression with
  | literal number =>
    rw [Expression.ail, Expressions.expression.eq_def]
    rfl

  | binary operator left right leftIH rightIH =>
    rw [Expression.ail, Expressions.expression.eq_def]
    dsimp only
    have typeNode : Silmaril.Cerberus.GeneralizedTypes.expressionType config Silmaril.Cerberus.Target.emptyEnvironment
        (.mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
          (.binary left.ail (.arithmetic operator.ail) right.ail)) = .ok intType := rfl
    rw [typeNode, actual_type left, actual_type right, leftIH, rightIH]
    rfl

/-- The explicit recursive output retains the actual modular arithmetic
builder, including the different conversion syntax and subtraction tag. -/
theorem actual_finish (operator : Operator) (digest : Digest) (next : Nat)
    (left right : Construction.Effect) :
    (Arithmetic.finish config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib .unknown
      intType intType intType operator.ail (operands digest next) left right).map
        (Expressions.annotate (.rvalue (.basic (.integer (.concrete (.signed .int))))) .unknown intType) =
      .ok (binaryCore operator digest next left right) := by
  cases operator <;> cbv

theorem advance_add (context : State.Context) (first second : Nat) :
    advance (advance context first) second = advance context (first + second) := by
  simp [advance, Nat.add_assoc]

/-- A real fresh allocation succeeds exactly under its independent host bound. -/
theorem fresh_symbol (context : State.Context) (type : BaseType)
    (room : context.freshness.next ≤ context.freshness.maximum) :
    State.run (State.wrappedFreshSymbol type) context =
      (.ok ⟨fresh context.freshness.digest context.freshness.next,
        Construction.symbolPattern (fresh context.freshness.digest context.freshness.next) type,
        Construction.symbolPure (fresh context.freshness.digest context.freshness.next)⟩, advance context 1) := by
  have allocated : Freshness.description .none context.freshness =
      .ok (fresh context.freshness.digest context.freshness.next,
        {context.freshness with next := context.freshness.next + 1}) := by
    simp [Freshness.description, Freshness.integer, room, fresh]
  dsimp only [State.run, State.wrappedFreshSymbol, State.wrappedFreshSymbolWith, State.freshDescription,
    ExceptT.run, Bind.bind, Pure.pure, MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw,
    Functor.map, ExceptT.map, StateT.map, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.bind, StateT.pure, StateT.get, StateT.set]
  rw [allocated]
  rfl

theorem run_bind {α β : Type} (first : State.ElabM α) (thenDo : α → State.ElabM β)
    (context after : State.Context) (value : α) (ran : State.run first context = (.ok value, after)) :
    State.run (first >>= thenDo) context = State.run (thenDo value) after := by
  have raw : first context = (.ok value, after) := ran
  dsimp only [State.run, ExceptT.run, ExceptT.mk, Bind.bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  rw [raw]

/-- Five actual allocations, including the unused capability symbol, retain
the exact state effects and advance only the real fresh counter. -/
theorem fresh_operands (context : State.Context)
    (room : context.freshness.next + 4 ≤ context.freshness.maximum) :
    State.run (Arithmetic.freshOperands .integer .integer) context =
      (.ok (operands context.freshness.digest context.freshness.next), advance context 5) := by
  unfold Arithmetic.freshOperands
  rw [run_bind _ _ _ _ _ (fresh_symbol context _ (by omega))]
  rw [run_bind _ _ _ _ _ (fresh_symbol (advance context 1) _ (by
    change context.freshness.next + 1 ≤ context.freshness.maximum
    omega))]
  rw [run_bind _ _ _ _ _ (fresh_symbol (advance (advance context 1) 1) _ (by
    change context.freshness.next + 1 + 1 ≤ context.freshness.maximum
    omega))]
  rw [run_bind _ _ _ _ _ (fresh_symbol (advance (advance (advance context 1) 1) 1) _ (by
    change context.freshness.next + 1 + 1 + 1 ≤ context.freshness.maximum
    omega))]
  rw [run_bind _ _ _ _ _ (fresh_symbol (advance (advance (advance (advance context 1) 1) 1) 1) _ (by
    change context.freshness.next + 1 + 1 + 1 + 1 ≤ context.freshness.maximum
    omega))]
  rfl

theorem actual_translate (operator : Operator) (left right : State.ElabM Construction.Effect) :
    Arithmetic.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib .unknown
      intType intType intType operator.ail left right =
      (if operator = .add then do
        let allocated ← Arithmetic.freshOperands .integer .integer
        let first ← left
        let second ← right
        Constants.liftResult (Arithmetic.finish config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
          .unknown intType intType intType operator.ail allocated first second)
      else do
        let first ← left
        let second ← right
        let allocated ← Arithmetic.freshOperands .integer .integer
        Constants.liftResult (Arithmetic.finish config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
          .unknown intType intType intType operator.ail allocated first second)) := by
  cases operator <;> rfl

theorem actual_finish_run (operator : Operator) (digest : Digest) (next : Nat)
    (left right : Construction.Effect) (context : State.Context) :
    State.run (do
      let core ← Constants.liftResult (Arithmetic.finish config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib .unknown
        intType intType intType operator.ail (operands digest next) left right)
      pure (Expressions.annotate (.rvalue (.basic (.integer (.concrete (.signed .int))))) .unknown intType core)) context =
      (.ok (binaryCore operator digest next left right), context) := by
  cases operator <;> cbv

/-- Structural source elaboration succeeds with exactly five allocations per
arithmetic node. The host bound is independent of any semantic execution. -/
theorem computation_run (expression : Expression) (context : State.Context)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum + 1) :
    State.run expression.computation context =
      (.ok (expression.core context.freshness.digest context.freshness.next),
        advance context (5 * expression.operations)) := by
  induction expression generalizing context with
  | literal number => cbv
  | binary operator left right leftIH rightIH =>
    show State.run (Expression.binary operator left right).computation context =
      (.ok ((Expression.binary operator left right).core context.freshness.digest context.freshness.next),
        advance context (5 * (Expression.binary operator left right).operations))
    have totalRoom : context.freshness.next + 5 * (1 + left.operations + right.operations) ≤
        context.freshness.maximum + 1 := room
    rw [Expression.computation, actual_translate]
    by_cases add : operator = .add
    · show State.run _ context =
        (.ok ((Expression.binary operator left right).core context.freshness.digest context.freshness.next),
          advance context (5 * (Expression.binary operator left right).operations))
      simp only [ite_eq_left add, bind_assoc]
      have allocRoom : context.freshness.next + 4 ≤ context.freshness.maximum := by omega
      have leftRoom : (advance context 5).freshness.next + 5 * left.operations ≤ context.freshness.maximum + 1 := by
        change context.freshness.next + 5 + 5 * left.operations ≤ context.freshness.maximum + 1
        omega
      have leftRun : State.run left.computation (advance context 5) =
          (.ok (left.core (advance context 5).freshness.digest (advance context 5).freshness.next),
            advance (advance context 5) (5 * left.operations)) := leftIH (advance context 5) leftRoom
      let middle := advance (advance context 5) (5 * left.operations)
      have rightRoom : middle.freshness.next + 5 * right.operations ≤ middle.freshness.maximum + 1 := by
        change context.freshness.next + 5 + 5 * left.operations + 5 * right.operations ≤ context.freshness.maximum + 1
        omega
      have rightRun : State.run right.computation middle =
          (.ok (right.core middle.freshness.digest middle.freshness.next), advance middle (5 * right.operations)) :=
        rightIH middle rightRoom
      rw [run_bind _ _ _ _ _ (fresh_operands context allocRoom)]
      rw [run_bind _ _ _ _ _ leftRun]
      rw [run_bind _ _ _ _ _ rightRun]
      rw [actual_finish_run]
      simp [Expression.core, add, advance, middle, Expression.operations, Nat.mul_add, Nat.add_assoc]
    · show State.run _ context =
        (.ok ((Expression.binary operator left right).core context.freshness.digest context.freshness.next),
          advance context (5 * (Expression.binary operator left right).operations))
      simp only [ite_eq_right add, bind_assoc]
      have leftRoom : context.freshness.next + 5 * left.operations ≤ context.freshness.maximum + 1 := by omega
      have leftRun : State.run left.computation context =
          (.ok (left.core context.freshness.digest context.freshness.next), advance context (5 * left.operations)) :=
        leftIH context leftRoom
      let middle := advance context (5 * left.operations)
      have rightRoom : middle.freshness.next + 5 * right.operations ≤ middle.freshness.maximum + 1 := by
        change context.freshness.next + 5 * left.operations + 5 * right.operations ≤ context.freshness.maximum + 1
        omega
      have rightRun : State.run right.computation middle =
          (.ok (right.core middle.freshness.digest middle.freshness.next), advance middle (5 * right.operations)) :=
        rightIH middle rightRoom
      let allocatedAt := advance middle (5 * right.operations)
      have allocRoom : allocatedAt.freshness.next + 4 ≤ allocatedAt.freshness.maximum := by
        change context.freshness.next + 5 * left.operations + 5 * right.operations + 4 ≤ context.freshness.maximum
        omega
      rw [run_bind _ _ _ _ _ leftRun]
      rw [run_bind _ _ _ _ _ rightRun]
      rw [run_bind _ _ _ _ _ (fresh_operands allocatedAt allocRoom)]
      rw [actual_finish_run]
      simp [Expression.core, add, advance, middle, allocatedAt, Expression.operations, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem expression_elaborates (expression : Expression) (context : State.Context)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum + 1) :
    State.run (Expressions.expression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail) context =
      (.ok (expression.core context.freshness.digest context.freshness.next),
        advance context (5 * expression.operations)) := by
  rw [actual_dispatcher]
  exact computation_run expression context room

theorem fresh_key_ne (digest : Digest) (next first second : Nat) (different : first ≠ second) :
    (fresh digest (next + first)).key ≠ (fresh digest (next + second)).key := by
  intro equal
  have indices : next + first = next + second := congrArg Prod.snd equal
  exact different (Nat.add_left_cancel indices)

/-- Each real signed operation accepts precisely the independently stated
representable result on this arithmetic fragment. -/
theorem checked_operation (operator : Operator) (tags : Mem.Concrete.Tags) (left right : Int)
    (bounded : Silmaril.Compiler.Native.Correctness.LiteralEmission.IsInt32 (operator.apply left right)) :
    Dynamics.primitive (.catchInt (.signed .int) operator.integer)
      [.object (.integer left), .object (.integer right)] tags =
        .ok (.object (.integer (operator.apply left right))) := by
  have lower : (-2147483648 : Int) ≤ operator.apply left right := bounded.1
  have upper : operator.apply left right ≤ (2147483647 : Int) := by
    have limit : operator.apply left right < (2147483648 : Int) := bounded.2
    omega
  have intBounds : Mem.Concrete.registeredIntegerBounds tags (.signed .int) =
      some (-2147483648, 2147483647) := rfl
  cases operator <;>
    simp_all [Operator.integer, Operator.apply, Dynamics.primitive, Dynamics.integerOp,
      pure, Except.pure, Dynamics.integer]

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Core Silmaril.Compiler.Core.Source

theorem runtime_integer_lookup (file : Program) (provided : RuntimeProvided file) :
    ConvInt.lookupFun file Native.Correctness.Literal42.convertInteger =
      some (.function (.object .integer)
        [(Native.Correctness.Literal42.typeParameter, .ctype),
          (Native.Correctness.Literal42.numberParameter, .object .integer)]
        Native.Correctness.Literal42.convertIntegerBody) := by
  unfold ConvInt.lookupFun
  rw [provided]
  cbv

theorem runtime_representable_lookup (file : Program) (provided : RuntimeProvided file) :
    ConvInt.lookupFun file Native.Correctness.Literal42.representable =
      some (.function .boolean
        [(Native.Correctness.Literal42.numberParameter, .object .integer),
          (Native.Correctness.Literal42.typeParameter, .ctype)]
        Native.Correctness.Literal42.representableBody) := by
  unfold ConvInt.lookupFun
  rw [provided]
  cbv

theorem runtime_integer_recognized (file : Program) (provided : RuntimeProvided file) :
    ConvInt.convInt file (.function (.object .integer)
      [(Native.Correctness.Literal42.typeParameter, .ctype),
        (Native.Correctness.Literal42.numberParameter, .object .integer)]
      Native.Correctness.Literal42.convertIntegerBody) = true := by
  unfold ConvInt.convInt
  dsimp only [Native.Correctness.Literal42.convertIntegerBody, Construction.ifPure, Construction.ifPureWith,
    Construction.operation, Construction.symbolPure, Construction.symbolPureWith, Construction.ctype,
    Construction.valuePure, Construction.call]
  rw [runtime_representable_lookup file provided]
  cbv

theorem converted_eval (file : Program) (provided : RuntimeProvided file) (tags : Mem.Concrete.Tags)
    (environment : Env) (standard : String) (operator : Operator) (expression : Construction.Pure) (number : Int)
    (bounded : Native.Correctness.LiteralEmission.IsInt32 number)
    (evaluated : PureEval.Eval file tags environment (.inl expression) (.inl (.object (.integer number)))) :
    PureEval.Eval file tags environment (.inl (Construction.standardPure standard (converted operator expression)))
      (.inl (.object (.integer number))) := by
  by_cases direct : operator = .add
  · rw [converted, ite_eq_left direct]
    exact .convInt (.cons evaluated .nil) (Native.Correctness.AdditionSource.convert_int tags number bounded)
  · rw [converted, ite_eq_right direct]
    apply ConvInt.convInt_eval (runtime_integer_lookup file provided) (runtime_integer_recognized file provided)
    · exact ⟨bounded.1, by have limit := bounded.2; omega⟩
    · exact .cons .val (.cons evaluated .nil)

theorem result_eval (file : Program) (provided : RuntimeProvided file) (tags : Mem.Concrete.Tags)
    (environment : Env) (operator : Operator) (digest : Digest) (next : Nat) (left right : Int)
    (leftBound : Native.Correctness.LiteralEmission.IsInt32 left)
    (rightBound : Native.Correctness.LiteralEmission.IsInt32 right)
    (resultBound : Native.Correctness.LiteralEmission.IsInt32 (operator.apply left right))
    (leftValue : environment.lookup (fresh digest next) = some (.loaded (.specified (.integer left))))
    (rightValue : environment.lookup (fresh digest (next + 1)) = some (.loaded (.specified (.integer right)))) :
    PureEval.Eval file tags environment (.inl (resultPure operator digest next))
      (.inl (.loaded (.specified (.integer (operator.apply left right))))) := by
  unfold resultPure
  refine .case_ (xs := [(fresh digest (next + 2), .object (.integer left)),
    (fresh digest (next + 3), .object (.integer right))])
    (.ctor (.cons (.sym leftValue) (.cons (.sym rightValue) .nil)) rfl) rfl ?_
  let extended := extendEnv [(fresh digest (next + 2), .object (.integer left)),
    (fresh digest (next + 3), .object (.integer right))] environment
  have getLeft : extended.lookup (fresh digest (next + 2)) = some (.object (.integer left)) :=
    ConvInt.lookup_one rfl
  have getRight : extended.lookup (fresh digest (next + 3)) = some (.object (.integer right)) := by
    change (extendEnv [(fresh digest (next + 2), .object (.integer left))]
      (extendEnv [(fresh digest (next + 3), .object (.integer right))] environment)).lookup
        (fresh digest (next + 3)) = _
    rw [ConvInt.lookup_one_other (fresh_key_ne digest next 3 2 (by decide +kernel))]
    exact ConvInt.lookup_one rfl
  have convertedLeft : PureEval.Eval file tags extended
      (.inl (Construction.standardPure operator.conversionStandard
        (converted operator (Construction.symbolPure (fresh digest (next + 2))))))
      (.inl (.object (.integer left))) :=
    converted_eval file provided tags extended operator.conversionStandard operator _ left leftBound (.sym getLeft)
  have convertedRight : PureEval.Eval file tags extended
      (.inl (Construction.standardPure operator.conversionStandard
        (converted operator (Construction.symbolPure (fresh digest (next + 3))))))
      (.inl (.object (.integer right))) :=
    converted_eval file provided tags extended operator.conversionStandard operator _ right rightBound (.sym getRight)
  exact .ctor (.cons (.catchInt (.cons convertedLeft (.cons convertedRight .nil))
    (checked_operation operator tags left right resultBound)) .nil) rfl

private abbrev constant := PureOperands.constant

private theorem constant_plain (number : Int) (environment : Env) (memory : Mem.Concrete.State) :
    Administrative.Plain ⟨.effectExpr (constant number) environment, [], memory⟩ := by
  constructor
  · rfl
  · simp [constant, PureOperands.constant, controlHasCCall, hasCCall]
  · simp [activeCall]

private theorem pure_plain (number : Int) (environment : Env) (location : Loc) (memory : Mem.Concrete.State) :
    Administrative.Plain ⟨.pureExpr (Constants.loadedInteger number) environment, [.diagnosticLocation location], memory⟩ :=
  (PureAdministrative.FramesPlain.nil.diagnosticLocation location).expression _ _ _

/-- Actual constant syntax derives its own path under any incoming memory.
If focusing changes the location, the path has a genuine update edge. -/
private theorem constant_path (file : Program) (labels : Labels) (number : Int) (environment : Env)
    (memory : Mem.Concrete.State) :
    Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
      ⟨.value (.loaded (.specified (.integer number))), [], focused memory⟩ := by
  let pureControl : Control := .pureExpr (Constants.loadedInteger number) environment
  let frames : List Frame := [.diagnosticLocation memory.currentLocation]
  have startPlain : Administrative.Plain ⟨.effectExpr (constant number) environment, [], memory⟩ :=
    constant_plain number environment memory
  have startRunning : Administrative.NotDone ⟨.effectExpr (constant number) environment, [], memory⟩ := by
    intro value accesses impossible
    cases impossible
  have begin : Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
      ⟨pureControl, frames, focused memory⟩ := by
    cases library : libraryLocation .unknown
    · show Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
        ⟨pureControl, frames, focused memory⟩
      by_cases located : memory.currentLocation = .unknown
      · show Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
          ⟨pureControl, frames, focused memory⟩
        have unchanged : focused memory = memory := by simp [focused, DiagnosticOperands.focused, ← located]
        rw [unchanged]
        have nextPlain : Administrative.Plain ⟨pureControl, frames, memory⟩ :=
          pure_plain number environment memory.currentLocation memory
        refine .cons (.next startPlain startRunning nextPlain ?_) (.refl nextPlain)
        intro outer
        simp [requestAux, awaitsScheduling, constant, PureOperands.constant, located, library, pureControl, frames]
      · show Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
          ⟨pureControl, frames, focused memory⟩
        have notUnknown : Loc.unknown ≠ memory.currentLocation := Ne.symm located
        have setterPlain : Administrative.Plain ⟨.setLocation .unknown pureControl, frames, memory⟩ := by
          constructor
          · rfl
          · simp [pureControl, frames, controlHasCCall]
          · simp [pureControl, frames, activeCall]
        have nextPlain : Administrative.Plain ⟨pureControl, frames, focused memory⟩ :=
          pure_plain number environment memory.currentLocation (focused memory)
        refine .cons (.next startPlain startRunning setterPlain ?_) ?_
        · intro outer
          simp [requestAux, awaitsScheduling, constant, PureOperands.constant, notUnknown, library, pureControl, frames]
        · refine .cons (.update setterPlain (by intro value accesses impossible; cases impossible) nextPlain ?_)
            (.refl nextPlain)
          intro outer
          simp [requestAux, awaitsScheduling, focused, DiagnosticOperands.focused, library, pureControl, frames]
    · show Administrative.Path file labels ⟨.effectExpr (constant number) environment, [], memory⟩
        ⟨pureControl, frames, focused memory⟩
      have unchanged : focused memory = memory := by simp [focused, DiagnosticOperands.focused, library]
      rw [unchanged]
      have nextPlain : Administrative.Plain ⟨pureControl, frames, memory⟩ :=
        pure_plain number environment memory.currentLocation memory
      refine .cons (.next startPlain startRunning nextPlain ?_) (.refl nextPlain)
      intro outer
      simp [requestAux, awaitsScheduling, constant, PureOperands.constant, library, pureControl, frames]
  have evaluated : PureEval.Eval file (PureEval.tagsOf file (focused memory)) environment
      (.inl (Constants.loadedInteger number)) (.inl (.loaded (.specified (.integer number)))) := .val
  have evalPath : Administrative.Path file labels ⟨pureControl, frames, focused memory⟩
      ⟨.value (.loaded (.specified (.integer number))), frames, focused memory⟩ :=
    PureAdministrative.pureEvaluation_path file (PureEval.tagsOf file (focused memory)) evaluated
      labels frames (focused memory) (PureAdministrative.FramesPlain.nil.diagnosticLocation memory.currentLocation) rfl
  have valuePlain : Administrative.Plain ⟨.value (.loaded (.specified (.integer number))), frames, focused memory⟩ :=
    (PureAdministrative.FramesPlain.nil.diagnosticLocation memory.currentLocation).value
      (.loaded (.specified (.integer number))) (focused memory)
  have finalPlain : Administrative.Plain ⟨.value (.loaded (.specified (.integer number))), [], focused memory⟩ :=
    PureAdministrative.FramesPlain.nil.value (.loaded (.specified (.integer number))) (focused memory)
  refine begin.trans (evalPath.trans (.cons (.next valuePlain ?_ finalPlain ?_) (.refl finalPlain)))
  · intro value accesses valueEq annotationsEq
    cases annotationsEq
  · intro outer
    simp [requestAux, awaitsScheduling, frames]

private theorem binary_path (file : Program) (provided : RuntimeProvided file) (labels : Labels)
    (environment : Env) (operator : Operator) (digest : Digest) (next : Nat)
    (leftCore rightCore : EE) (left right : Int) (leftFrames rightFrames : List Frame)
    (memory rightMemory finalMemory : Mem.Concrete.State)
    (leftBound : Native.Correctness.LiteralEmission.IsInt32 left)
    (rightBound : Native.Correctness.LiteralEmission.IsInt32 right)
    (resultBound : Native.Correctness.LiteralEmission.IsInt32 (operator.apply left right))
    (rightPath : Administrative.Path file labels ⟨.effectExpr rightCore environment, [], memory⟩
      ⟨.value (.loaded (.specified (.integer right))), rightFrames, rightMemory⟩)
    (rightAnnotations : annotationsOnly rightFrames = some [])
    (leftPath : Administrative.Path file labels ⟨.effectExpr leftCore environment, [], rightMemory⟩
      ⟨.value (.loaded (.specified (.integer left))), leftFrames, finalMemory⟩)
    (leftAnnotations : annotationsOnly leftFrames = some []) :
    Administrative.Path file labels ⟨.effectExpr (binaryCore operator digest next leftCore rightCore) environment, [], memory⟩
      ⟨.value (.loaded (.specified (.integer (operator.apply left right)))), [.annotations []], finalMemory⟩ := by
  let pattern := Pattern.mk [] (.ctor .tuple [(operands digest next).left.pattern, (operands digest next).right.pattern])
  let body := Construction.pureEffect (resultPure operator digest next)
  let continuation : List Frame := [.effectBind pattern body environment]
  let extended := extendEnv [(fresh digest next, .loaded (.specified (.integer left))),
    (fresh digest (next + 1), .loaded (.specified (.integer right)))] environment
  have leftFree : hasCCall leftCore = false := by
    simpa [controlHasCCall] using leftPath.source_plain.callfree
  have rightFree : hasCCall rightCore = false := by
    simpa [controlHasCCall] using rightPath.source_plain.callfree
  have sourcePlain : Administrative.Plain
      ⟨.effectExpr (binaryCore operator digest next leftCore rightCore) environment, [], memory⟩ := by
    constructor
    · rfl
    · simp [binaryCore, Construction.pureEffect, controlHasCCall, hasCCall, leftFree, rightFree]
    · simp [activeCall]
  have framesPlain : Administrative.PlainFrames continuation := by
    constructor <;> simp [continuation, body, Construction.pureEffect, controlHasCCall, activeCall, hasCCall]
  have unsequenced : Administrative.Path file labels
      ⟨.effectExpr (.mk [] (.unseq [leftCore, rightCore])) environment, [], memory⟩
      ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
        [.annotations []], finalMemory⟩ :=
    Administrative.unseq_pair leftCore rightCore environment _ _ leftFrames rightFrames memory rightMemory finalMemory
      rightPath rightAnnotations leftPath leftAnnotations
  have operandsPath : Administrative.Path file labels
      (Administrative.extend ⟨.effectExpr (.mk [] (.unseq [leftCore, rightCore])) environment, [], memory⟩ continuation)
      (Administrative.extend
        ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
          [.annotations []], finalMemory⟩ continuation) := unsequenced.extended continuation framesPlain
  have begin : Administrative.Path file labels
      ⟨.effectExpr (binaryCore operator digest next leftCore rightCore) environment, [], memory⟩
      (Administrative.extend ⟨.effectExpr (.mk [] (.unseq [leftCore, rightCore])) environment, [], memory⟩ continuation) := by
    refine .cons (.next sourcePlain (by intro value accesses impossible; cases impossible)
      operandsPath.source_plain ?_) (.refl operandsPath.source_plain)
    intro outer
    simp [requestAux, awaitsScheduling, binaryCore, pattern, continuation, body]
  have bodyPlain : Administrative.Plain ⟨.effectExpr body extended, [.annotations []], finalMemory⟩ := by
    constructor
    · rfl
    · simp [body, Construction.pureEffect, controlHasCCall, hasCCall]
    · simp [activeCall]
  have bindOperands : Administrative.Path file labels
      (Administrative.extend
        ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
          [.annotations []], finalMemory⟩ continuation)
      ⟨.effectExpr body extended, [.annotations []], finalMemory⟩ := by
    refine .cons (.next operandsPath.target_plain ?_ bodyPlain ?_) (.refl bodyPlain)
    · intro value accesses valueEq annotationsEq
      have impossible : (none : Option (List Access)) = some accesses := by
        simpa only [Administrative.extend, continuation, List.singleton_append, annotationsOnly,
          Option.map_none] using annotationsEq
      cases impossible
    · intro outer
      simp [requestAux, awaitsScheduling, Administrative.extend, continuation, pattern, operands,
        Construction.symbolPattern, Construction.symbolPatternWith, matchPattern, matchPatterns, extended]
  let pureFrames : List Frame := [.diagnosticLocation finalMemory.currentLocation, .annotations []]
  have pureFramesPlain : PureAdministrative.FramesPlain pureFrames :=
    (PureAdministrative.FramesPlain.nil.annotations []).diagnosticLocation finalMemory.currentLocation
  have purePlain : Administrative.Plain
      ⟨.pureExpr (resultPure operator digest next) extended, pureFrames, finalMemory⟩ :=
    pureFramesPlain.expression _ _ _
  have beginResult : Administrative.Path file labels ⟨.effectExpr body extended, [.annotations []], finalMemory⟩
      ⟨.pureExpr (resultPure operator digest next) extended, pureFrames, finalMemory⟩ := by
    refine .cons (.next bodyPlain (by intro value accesses impossible; cases impossible) purePlain ?_) (.refl purePlain)
    intro outer
    simp [requestAux, awaitsScheduling, body, Construction.pureEffect, pureFrames]
  have getLeft : extended.lookup (fresh digest next) = some (.loaded (.specified (.integer left))) :=
    ConvInt.lookup_one rfl
  have getRight : extended.lookup (fresh digest (next + 1)) = some (.loaded (.specified (.integer right))) := by
    change (extendEnv [(fresh digest next, .loaded (.specified (.integer left)))]
      (extendEnv [(fresh digest (next + 1), .loaded (.specified (.integer right)))] environment)).lookup
        (fresh digest (next + 1)) = _
    have different : (fresh digest (next + 1)).key ≠ (fresh digest next).key := by
      simpa only [Nat.add_zero] using fresh_key_ne digest next 1 0 (by decide +kernel)
    rw [ConvInt.lookup_one_other different]
    exact ConvInt.lookup_one rfl
  have evaluated : Administrative.Path file labels
      ⟨.pureExpr (resultPure operator digest next) extended, pureFrames, finalMemory⟩
      ⟨.value (.loaded (.specified (.integer (operator.apply left right)))), pureFrames, finalMemory⟩ :=
    PureAdministrative.pureEvaluation_path file (PureEval.tagsOf file finalMemory)
    (result_eval file provided (PureEval.tagsOf file finalMemory) extended operator digest next left right
      leftBound rightBound resultBound getLeft getRight) labels pureFrames finalMemory pureFramesPlain rfl
  have finalPlain : Administrative.Plain
      ⟨.value (.loaded (.specified (.integer (operator.apply left right)))), [.annotations []], finalMemory⟩ :=
    (PureAdministrative.FramesPlain.nil.annotations []).value _ _
  have pop : Administrative.Path file labels
      ⟨.value (.loaded (.specified (.integer (operator.apply left right)))), pureFrames, finalMemory⟩
      ⟨.value (.loaded (.specified (.integer (operator.apply left right)))), [.annotations []], finalMemory⟩ := by
    refine .cons (.next evaluated.target_plain ?_ finalPlain ?_) (.refl finalPlain)
    · intro value accesses valueEq annotationsEq
      cases annotationsEq
    · intro outer
      simp [requestAux, awaitsScheduling, pureFrames]
  exact begin.trans (operandsPath.trans (bindOperands.trans (beginResult.trans (evaluated.trans pop))))

theorem result_annotations (expression : Expression) :
    annotationsOnly expression.resultFrames = some [] := by
  cases expression <;> rfl

/-- Every recursive source child derives its own real execution. The only
semantic-domain hypothesis is independent signed32 bounds at every node. -/
theorem core_path (file : Program) (provided : RuntimeProvided file) (labels : Labels)
    (environment : Env) (digest : Digest) (expression : Expression) :
    ∀ (_bounded : expression.Bounded) (next : Nat) (memory : Mem.Concrete.State),
      Administrative.Path file labels ⟨.effectExpr (expression.core digest next) environment, [], memory⟩
        ⟨.value (.loaded (.specified (.integer expression.value))), expression.resultFrames, focused memory⟩ := by
  induction expression with
  | literal number =>
    intro _bounded next memory
    exact constant_path file labels number environment memory
  | binary operator left right leftIH rightIH =>
    show ∀ (_bounded : (Expression.binary operator left right).Bounded) (next : Nat) (memory : Mem.Concrete.State),
      Administrative.Path file labels
        ⟨.effectExpr ((Expression.binary operator left right).core digest next) environment, [], memory⟩
        ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))), [.annotations []], focused memory⟩
    intro bounded next memory
    show Administrative.Path file labels
      ⟨.effectExpr ((Expression.binary operator left right).core digest next) environment, [], memory⟩
      ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))), [.annotations []], focused memory⟩
    have leftBound : Native.Correctness.LiteralEmission.IsInt32 left.value := bounded_value left bounded.1
    have rightBound : Native.Correctness.LiteralEmission.IsInt32 right.value := bounded_value right bounded.2.1
    have resultBound : Native.Correctness.LiteralEmission.IsInt32 (operator.apply left.value right.value) := bounded.2.2
    by_cases add : operator = .add
    · show Administrative.Path file labels
        ⟨.effectExpr ((Expression.binary operator left right).core digest next) environment, [], memory⟩
        ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))), [.annotations []], focused memory⟩
      have rightPath : Administrative.Path file labels
          ⟨.effectExpr (right.core digest (next + 5 + 5 * left.operations)) environment, [], memory⟩
          ⟨.value (.loaded (.specified (.integer right.value))), right.resultFrames, focused memory⟩ :=
        rightIH bounded.2.1 (next + 5 + 5 * left.operations) memory
      have leftPath : Administrative.Path file labels
          ⟨.effectExpr (left.core digest (next + 5)) environment, [], focused memory⟩
          ⟨.value (.loaded (.specified (.integer left.value))), left.resultFrames, focused (focused memory)⟩ :=
        leftIH bounded.1 (next + 5) (focused memory)
      have combined : Administrative.Path file labels
          ⟨.effectExpr (binaryCore operator digest next (left.core digest (next + 5))
            (right.core digest (next + 5 + 5 * left.operations))) environment, [], memory⟩
          ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))),
            [.annotations []], focused (focused memory)⟩ := binary_path file provided labels environment operator digest next
        (left.core digest (next + 5)) (right.core digest (next + 5 + 5 * left.operations))
        left.value right.value left.resultFrames right.resultFrames memory (focused memory)
        (focused (focused memory)) leftBound rightBound resultBound rightPath (result_annotations right)
        leftPath (result_annotations left)
      simpa only [Expression.core, ite_eq_left add, Expression.value, Expression.resultFrames,
        DiagnosticOperands.focused_idempotent] using combined
    · show Administrative.Path file labels
        ⟨.effectExpr ((Expression.binary operator left right).core digest next) environment, [], memory⟩
        ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))), [.annotations []], focused memory⟩
      have rightPath : Administrative.Path file labels
          ⟨.effectExpr (right.core digest (next + 5 * left.operations)) environment, [], memory⟩
          ⟨.value (.loaded (.specified (.integer right.value))), right.resultFrames, focused memory⟩ :=
        rightIH bounded.2.1 (next + 5 * left.operations) memory
      have leftPath : Administrative.Path file labels
          ⟨.effectExpr (left.core digest next) environment, [], focused memory⟩
          ⟨.value (.loaded (.specified (.integer left.value))), left.resultFrames, focused (focused memory)⟩ :=
        leftIH bounded.1 next (focused memory)
      have combined : Administrative.Path file labels
          ⟨.effectExpr (binaryCore operator digest (next + 5 * left.operations + 5 * right.operations)
            (left.core digest next) (right.core digest (next + 5 * left.operations))) environment, [], memory⟩
          ⟨.value (.loaded (.specified (.integer (operator.apply left.value right.value)))),
            [.annotations []], focused (focused memory)⟩ := binary_path file provided labels environment operator digest
        (next + 5 * left.operations + 5 * right.operations)
        (left.core digest next) (right.core digest (next + 5 * left.operations))
        left.value right.value left.resultFrames right.resultFrames memory (focused memory)
        (focused (focused memory)) leftBound rightBound resultBound rightPath (result_annotations right)
        leftPath (result_annotations left)
      simpa only [Expression.core, ite_eq_right add, Expression.value, Expression.resultFrames,
        DiagnosticOperands.focused_idempotent] using combined

/-- Actual forced execution under an arbitrary external continuation and
arbitrary incoming environment and diagnostic memory. -/
theorem core_reaches (file : Program) (provided : RuntimeProvided file) (labels : Labels)
    (environment : Env) (digest : Digest) (expression : Expression) (bounded : expression.Bounded)
    (next : Nat) (memory : Mem.Concrete.State) (outer : List Frame) :
    Forced.Reaches file labels ⟨.effectExpr (expression.core digest next) environment, outer, memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), expression.resultFrames ++ outer, focused memory⟩ := by
  exact (core_path file provided labels environment digest expression bounded next memory).forced outer

/-- Source adequacy for this grammar derives actual typed-Ail elaboration,
precise freshness, and real Core execution without assuming any of them. -/
theorem source_reaches (file : Program) (provided : RuntimeProvided file) (labels : Labels)
    (environment : Env) (expression : Expression) (bounded : expression.Bounded)
    (context : State.Context)
    (room : context.freshness.next + 5 * expression.operations ≤ context.freshness.maximum + 1)
    (memory : Mem.Concrete.State) (outer : List Frame) :
    State.run (Expressions.expression config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib expression.ail) context =
      (.ok (expression.core context.freshness.digest context.freshness.next), advance context (5 * expression.operations)) ∧
    Forced.Reaches file labels
      ⟨.effectExpr (expression.core context.freshness.digest context.freshness.next) environment, outer, memory⟩
      ⟨.value (.loaded (.specified (.integer expression.value))), expression.resultFrames ++ outer, focused memory⟩ := by
  constructor
  · exact expression_elaborates expression context room
  · exact core_reaches file provided labels environment context.freshness.digest expression bounded
      context.freshness.next memory outer

end Silmaril.Compiler.Core.SignedArithmetic
