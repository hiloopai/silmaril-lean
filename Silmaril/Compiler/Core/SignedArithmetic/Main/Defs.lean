module

public import Silmaril.Compiler.Core.SignedArithmetic.Thms
public import Silmaril.Compiler.Core.ReturnControl.Thms
public import Silmaril.Compiler.Native.Correctness.Institution.Thms
/-! Recursive typed-Ail signed-int mains, actual elaboration output and whole-Core
source contract. Host freshness is fixed from syntax; semantic arithmetic bounds
are independent and stated separately on every expression node. -/

@[expose] public section
namespace Silmaril.Compiler.Core.SignedArithmetic.Main
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Native.Correctness
open Construction

abbrev mainType := AdditionSource.intType
abbrev returnLabel := AdditionSource.returnLabel

def resultSymbol (expression : Expression) : Sym := fresh ⟨[]⟩ (101 + 5 * expression.operations)
def savedSymbol (expression : Expression) : Sym := fresh ⟨[]⟩ (102 + 5 * expression.operations)
def freshness (expression : Expression) : Freshness.Context := ⟨⟨[]⟩, 100, 102 + 5 * expression.operations⟩

def body (expression : Expression) : Ail.TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk [])
    (.block [] [.mk .unknown ⟨false, none⟩ (.mk []) (.return_ expression.ail)])

def program (expression : Expression) : Ail.TypedProgram :=
  let original := AdditionSource.program 0 0
  (original.1, {original.2 with functionDefinitions :=
    [(Literal42.sym 1 "main", {loc := .unknown, marker := 7, attrs := .mk [], params := [], body := body expression})]})

/-- The finite source syntax fixes sufficient host freshness before elaboration. -/
def source (expression : Expression) : Source :=
  {LiteralFamily.source 0 with
    program := program expression
    elaboration := {config := config, runtime := runtime, freshness := freshness expression}
    commit := "formal-recursive-signed-int-arithmetic-source-family"
    implementation := "constructed-conversion-runtime; explicit-linux-lp64-primitive-profile; recursive-signed-int-arithmetic-main"}

def wrappedCore (expression : Expression) : Effect :=
  .mk [.std "§6.5#2"] (.bound (expression.core ⟨[]⟩ 101))

def returnCore (expression : Expression) (digest : Digest) (next : Nat) (label : Sym) : Effect :=
  let symbol := fresh digest (next + 5 * expression.operations)
  strongSequence (symbolPattern symbol (.loaded .integer))
    (.mk [.std "§6.5#2"] (.bound (expression.core digest next)))
    (ReturnControl.convertedReturn label Literal42.conversion symbol)

def coreReturn (expression : Expression) : Effect :=
  addLocation .unknown (addStatement (returnCore expression ⟨[]⟩ 101 returnLabel))

def bodyCore (expression : Expression) (digest : Digest) (next : Nat) (label : Sym) : Effect :=
  addLocation .unknown (addStatement (Statements.unitSequence
    [addLocation .unknown (addStatement (returnCore expression digest next label))] skip))

def coreBody (expression : Expression) : Effect := bodyCore expression ⟨[]⟩ 101 returnLabel

def savedReturn (expression : Expression) : Effect :=
  Functions.returnSave (some (Literal42.sym 1 "main")) (Literal42.sym 1 "main") returnLabel
    (savedSymbol expression) .unknown mainType (.loaded .integer)

def procedureBody (expression : Expression) : Effect :=
  strongSequence (wildcard .unit) (coreBody expression) (savedReturn expression)

def bindings (expression : Expression) : Codec.FileBindings :=
  {AdditionSource.bindings 0 0 with funs :=
    [(Literal42.sym 1 "main", .procedure .unknown (some 7) (.loaded .integer) [] (procedureBody expression))]}

abbrev semanticFile (expression : Expression) := (bindings expression).toFile

def sourceDocument (expression : Expression) := document (source expression) (bindings expression)
def expectedExit (expression : Expression) : Silmaril.Compile.Core.Spec.Obs := .exit (expression.value % 256).toNat []
def specification (expression : Expression) : Set Observation := {observation | observe observation = expectedExit expression}

end Silmaril.Compiler.Core.SignedArithmetic.Main
