module

public import Silmaril.Compiler.Native.Correctness.AdditionSource.Defs
public import Silmaril.Compiler.Core.Source.PureAdministrative.Thms
public import Silmaril.Cerberus.Core.Administrative.Continuation.Thms
public import Silmaril.Cerberus.Core.DiagnosticOperands.Defs
/-! A recursively generated, typed-Ail signed-int arithmetic fragment. The
mathematical domain checks every subexpression independently of elaboration,
execution, native compilation or any chosen expected-result runtime. -/
@[expose] public section
namespace Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration

inductive Operator where
  | add | sub | mul
  deriving DecidableEq, Repr

inductive Expression where
  | literal (number : Int)
  | binary (operator : Operator) (left right : Expression)
  deriving DecidableEq, Repr

def Operator.apply : Operator → Int → Int → Int
  | .add => Int.add
  | .sub => fun left right => left - right
  | .mul => Int.mul

def Operator.ail : Operator → ArithmeticOperator
  | .add => .add
  | .sub => .sub
  | .mul => .mul

def Expression.value : Expression → Int
  | .literal number => number
  | .binary operator left right => operator.apply left.value right.value

/-- The operand and operation result at every recursive node is independently
signed32 representable. There is no successful semantic path in this predicate. -/
def Expression.Bounded : Expression → Prop
  | .literal number => Silmaril.Compiler.Native.Correctness.LiteralEmission.IsInt32 number
  | .binary operator left right => left.Bounded ∧ right.Bounded ∧
      Silmaril.Compiler.Native.Correctness.LiteralEmission.IsInt32
        (operator.apply left.value right.value)

def intType : Ctype := .mk [.loc .unknown] (.basic (.integer (.signed .int)))

def Expression.ail : Expression → Ail.TypedExpression
  | .literal number => ElaborationCorrectness.integerLiteral .unknown number .decimal none
  | .binary operator left right =>
      .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
        (.binary left.ail (.arithmetic operator.ail) right.ail)

/-- Number of arithmetic nodes. Each actual supported operation allocates the
real five symbols; add does so before children while sub/mul do so after them. -/
def Expression.operations : Expression → Nat
  | .literal _ => 0
  | .binary _ left right => 1 + left.operations + right.operations

abbrev runtime := Silmaril.Compiler.Native.Correctness.AdditionSource.runtime
abbrev config := Silmaril.Compiler.Native.Correctness.AdditionSource.config

/-- The fixed constructed runtime is present as actual syntax. This profile
does not contain an evaluator, successful-execution or adequacy premise. -/
def RuntimeProvided (file : Dynamics.Program) : Prop := file.stdlib = Map.ofList runtime.stdlib

abbrev focused := Silmaril.Cerberus.Core.DiagnosticOperands.focused

def fresh (digest : Digest) (index : Nat) : Sym := ⟨digest, index, .none⟩

def operands (digest : Digest) (next : Nat) : Arithmetic.Operands :=
  let wrapped (offset : Nat) (type : BaseType) : State.WrappedSymbol :=
    let symbol := fresh digest (next + offset)
    ⟨symbol, Construction.symbolPattern symbol type, Construction.symbolPure symbol⟩
  ⟨wrapped 0 (.loaded .integer), wrapped 1 (.loaded .integer),
    wrapped 2 (.object .integer), wrapped 3 (.object .integer), wrapped 4 (.object .integer)⟩

def Operator.integer : Operator → IntOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

def Operator.standard : Operator → String
  | .add | .sub => "§6.5.6"
  | .mul => "§6.5.5"

def Operator.conversionStandard : Operator → String
  | .add | .sub => "§6.5.6#4"
  | .mul => "§6.5.5#3"

def Operator.operationStandard : Operator → String
  | .add => "§6.5.6#5"
  | .sub => "§6.5.6#6"
  | .mul => "§6.5.5#4"

def Operator.wrapperStandard : Operator → String
  | .add => "§6.5.6#5"
  | .sub => "§6.5.5#6"
  | .mul => "§6.5.5#4"

/-- Exact direct versus actual named-runtime conversion from Arithmetic.finish. -/
def converted (operator : Operator) (expression : Construction.Pure) : Construction.Pure :=
  if operator = .add then Construction.convertInteger (.signed .int) expression
  else Construction.call (.sym Silmaril.Compiler.Native.Correctness.Literal42.convertInteger)
    [Construction.ctype (.mk [] (.basic (.integer (.signed .int)))), expression]

def resultPure (operator : Operator) (digest : Digest) (next : Nat) : Construction.Pure :=
  let allocated := operands digest next
  let left := Construction.standardPure operator.conversionStandard (converted operator allocated.leftObject.expression)
  let right := Construction.standardPure operator.conversionStandard (converted operator allocated.rightObject.expression)
  Construction.casePure (.mk [] () (.ctor .tuple [allocated.left.expression, allocated.right.expression]))
    [(.mk [] (.ctor .tuple [Construction.specifiedPattern allocated.leftObject.pattern,
        Construction.specifiedPattern allocated.rightObject.pattern]),
      Construction.specified (Construction.standardPure operator.wrapperStandard
        (Construction.catchExceptionalCondition (.signed .int) operator.integer left right))),
      (Construction.wildcard (.tuple [.loaded .integer, .loaded .integer]),
        Construction.standardUndefined .unknown "§6.5#5" .UB036_exceptional_condition)]

def binaryCore (operator : Operator) (digest : Digest) (next : Nat)
    (left right : Construction.Effect) : Construction.Effect :=
  let allocated := operands digest next
  .mk [.loc .unknown, .expr, .value (.integer (.signed .int)), .std operator.standard]
    (.wseq (.mk [] (.ctor .tuple [allocated.left.pattern, allocated.right.pattern]))
      (.mk [] (.unseq [left, right])) (Construction.pureEffect (resultPure operator digest next)))

/-- Actual symbol allocation order, including each operation's unused fifth
symbol. The recursive source syntax, not a successful elaboration, fixes it. -/
def Expression.core : Expression → Digest → Nat → Construction.Effect
  | .literal number, _, _ => Silmaril.Cerberus.Core.PureOperands.constant number
  | .binary operator left right, digest, next =>
      if operator = .add then
        binaryCore operator digest next (left.core digest (next + 5))
          (right.core digest (next + 5 + 5 * left.operations))
      else
        binaryCore operator digest (next + 5 * left.operations + 5 * right.operations)
          (left.core digest next) (right.core digest (next + 5 * left.operations))

/-- Literal operands complete directly; arithmetic nodes retain the actual
empty-access annotation emitted by the real operand scheduler. -/
def Expression.resultFrames : Expression → List Dynamics.Frame
  | .literal _ => []
  | .binary _ _ _ => [.annotations []]

def advance (context : State.Context) (count : Nat) : State.Context :=
  {context with freshness := {context.freshness with next := context.freshness.next + count}}

/-- Structural reuse of the real modular elaborator. A subsequent equation
connects this recursive algebra to the actual dependent Expressions dispatcher;
there is no substitute Core arithmetic operator or runtime implementation. -/
def Expression.computation : Expression → State.ElabM Construction.Effect
  | .literal number => Constants.expression config Silmaril.Cerberus.Target.emptyEnvironment
      (ElaborationCorrectness.integerLiteral .unknown number .decimal none)
  | .binary operator left right => do
      let core ← Arithmetic.translate config Silmaril.Cerberus.Target.emptyEnvironment runtime.stdlib
        .unknown intType intType intType operator.ail left.computation right.computation
      return Expressions.annotate (.rvalue (.basic (.integer (.concrete (.signed .int))))) .unknown intType core

end Silmaril.Compiler.Core.SignedArithmetic
