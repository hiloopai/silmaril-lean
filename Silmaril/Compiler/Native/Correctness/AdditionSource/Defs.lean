module

public import Silmaril.Cerberus.Core.PureOperands.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralFamily.Defs
public import Silmaril.Compiler.Core.ElaborationTotal.Defs
/-! Independently fixed typed-Ail signed-int addition main, explicit constructed
conversion runtime and LP64 primitive target. Bounds inspect only mathematical
source operands and sum. No compiler success or successful Core execution is
part of the source domain. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionSource
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core
open Construction

abbrev runtime := Literal42.runtime
abbrev config := Silmaril.Compiler.Native.TargetCoherence.linuxLP64

def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
def fresh (index : Nat) : Sym := ⟨⟨[]⟩, index, .none⟩
def returnLabel : Sym := ⟨⟨[]⟩, 100, .id s!"ret_{100}"⟩

/-- The actual typed-Ail binary expression, with independent signed-int
annotations on the operator and both literal operands. -/
def expression (left right : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.binary (ElaborationCorrectness.integerLiteral .unknown left .decimal none)
      (.arithmetic .add) (ElaborationCorrectness.integerLiteral .unknown right .decimal none))

def body (left right : Int) : Ail.TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk [])
    (.block [] [.mk .unknown ⟨false, none⟩ (.mk []) (.return_ (expression left right))])

/-- Existing Ail file syntax, with exact declaration/definition metadata. -/
def program (left right : Int) : Ail.TypedProgram :=
  let original := (LiteralEmission.literal 0).program
  (original.1, {original.2 with functionDefinitions :=
    [(Literal42.sym 1 "main", {
      loc := .unknown
      marker := 7
      attrs := .mk []
      params := []
      body := body left right})]})

/-- All source inputs are fixed before elaboration, execution or compilation. -/
def source (left right : Int) : Source :=
  { LiteralFamily.source 0 with
    program := program left right
    commit := "formal-signed-int-addition-source-family"
    implementation := "constructed-conversion-runtime; explicit-linux-lp64-primitive-profile; signed-int-addition-main" }

/-- Independent source arithmetic bounds; the sum restriction excludes signed
overflow rather than assuming semantic definedness of the Core result. -/
def Bounds (left right : Int) : Prop :=
  LiteralEmission.IsInt32 left ∧ LiteralEmission.IsInt32 right ∧ LiteralEmission.IsInt32 (left + right)

/-- The exact allocated symbols from the actual addition branch; the unused
fifth operand is retained. The function return label precedes these five. -/
def operands : Arithmetic.Operands :=
  ⟨⟨fresh 101, symbolPattern (fresh 101) (.loaded .integer), symbolPure (fresh 101)⟩,
    ⟨fresh 102, symbolPattern (fresh 102) (.loaded .integer), symbolPure (fresh 102)⟩,
    ⟨fresh 103, symbolPattern (fresh 103) (.object .integer), symbolPure (fresh 103)⟩,
    ⟨fresh 104, symbolPattern (fresh 104) (.object .integer), symbolPure (fresh 104)⟩,
    ⟨fresh 105, symbolPattern (fresh 105) (.object .integer), symbolPure (fresh 105)⟩⟩

def resultPure : Pure :=
  let left := standardPure "§6.5.6#4" (convertInteger (.signed .int) (symbolPure (fresh 103)))
  let right := standardPure "§6.5.6#4" (convertInteger (.signed .int) (symbolPure (fresh 104)))
  casePure (.mk [] () (.ctor .tuple [symbolPure (fresh 101), symbolPure (fresh 102)]))
    [(.mk [] (.ctor .tuple [specifiedPattern operands.leftObject.pattern,
        specifiedPattern operands.rightObject.pattern]),
      specified (standardPure "§6.5.6#5" (catchExceptionalCondition (.signed .int) .add left right))),
      (wildcard (.tuple [.loaded .integer, .loaded .integer]),
        standardUndefined .unknown "§6.5#5" .UB036_exceptional_condition)]

/-- Explicit output syntax of the real Arithmetic/Expressions dispatch. The
actual elaborator equation is proved separately. -/
def coreExpression (left right : Int) : Effect :=
  .mk [.loc .unknown, .expr, .value (.integer (.signed .int)), .std "§6.5.6"]
    (.wseq (.mk [] (.ctor .tuple [operands.left.pattern, operands.right.pattern]))
      (.mk [] (.unseq [Silmaril.Cerberus.Core.PureOperands.constant left,
        Silmaril.Cerberus.Core.PureOperands.constant right])) (pureEffect resultPure))

def coreReturn (left right : Int) : Effect :=
  addLocation .unknown (addStatement (strongSequence (symbolPattern (fresh 106) (.loaded .integer))
    (.mk [.std "§6.5#2"] (.bound (coreExpression left right)))
    (Construction.run returnLabel [call (.sym Literal42.conversion) [ctype intType, symbolPure (fresh 106)]])))

def coreBody (left right : Int) : Effect :=
  addLocation .unknown (addStatement (Statements.unitSequence [coreReturn left right] skip))

def bindings (left right : Int) : Codec.FileBindings where
  main := some (Literal42.sym 1 "main")
  callingConvention := .normal
  tagDefs := []
  stdlib := runtime.stdlib
  impl := runtime.impl
  globs := []
  funs := [(Literal42.sym 1 "main", .procedure .unknown (some 7) (.loaded .integer) []
    (strongSequence (wildcard .unit) (coreBody left right)
      (Functions.returnSave (some (Literal42.sym 1 "main")) (Literal42.sym 1 "main") returnLabel
        (fresh 107) .unknown intType (.loaded .integer))))]
  extern := [(⟨.unknown, "main"⟩, [Literal42.sym 1 "main"], .normal (Literal42.sym 1 "main"))]
  funInfo := [(Literal42.sym 1 "main", .unknown, .mk [], intType, [], false, true)]
  loopAttributes := []
  visibleObjects := []

/-- The actual generated full-expression boundary, before its enclosing
return transfer and C startup. This local operational model is distinguished
from the whole-main initial state. -/
def localModel (left right : Int) (environment : Dynamics.Env) (memory : Mem.Concrete.State) :
    Silmaril.Cerberus.Institution.Model :=
  ⟨(bindings left right).toFile, ∅,
    ⟨.effectExpr (.mk [.std "§6.5#2"] (.bound (coreExpression left right))) environment, [], memory⟩⟩

end Silmaril.Compiler.Native.Correctness.AdditionSource
