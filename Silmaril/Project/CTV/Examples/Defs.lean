module

public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionSource.Defs
public import Silmaril.Compiler.Core.ParameterCallReturn.Defs
public import Silmaril.Cerberus.TV.Compose.Defs

/-!
# Whole-program validation examples over elaborated Core

The programs are the Core files of `int main(void) { return a + b; }` that the Lean port of
Cerberus's elaborator produces for the LP64 primitive configuration with the explicitly
constructed conversion runtime (`Silmaril.Compiler.Native.Correctness.AdditionSource`): the
actual elaborated arithmetic, including the unsequenced evaluation of both operands, the
`catch_exceptional_condition` overflow check and the return through the saved return label.
Comparing two of them is the shape of validating a constant-folding step on Core.

They are closed (no arguments), deterministic up to the unsequenced operand evaluation, and
small; they are examples of the validator's statements, not a corpus. Programs with memory,
calls, loops and output are the next corpus stage (docs/projects/c-tv.md).
-/

@[expose] public section

namespace Silmaril.Project.CTV.Examples

open Silmaril.Cerberus
open Silmaril.Cerberus.TV
open Silmaril.Compiler.Native.Correctness

/-- `int main(void) { return a + b; }` as elaborated Core: its file bindings. -/
def addBindings (a b : Int) : Codec.FileBindings := AdditionSource.bindings a b

/-- `int main(void) { return a + b; }` as a closed program. -/
def add (a b : Int) : Closed := ⟨(addBindings a b).toFile, ∅, []⟩

/-- `main`'s symbol in these files. -/
def mainSym : Sym := Literal42.sym 1 "main"

/-- `main`'s definition in the file of `return a + b;`. -/
def mainDecl (a b : Int) : Core.FunDecl Codec.wireModel Unit Unit :=
  match (addBindings a b).funs with
  | (_, d) :: _ => d
  | [] => .builtinDecl .unknown .unit []

/-- `main`'s definitions in the function-level row. -/
def mainFoldBefore : Core.FunDecl Codec.wireModel Unit Unit := mainDecl 1 2
def mainFoldAfter : Core.FunDecl Codec.wireModel Unit Unit := mainDecl 3 0

/-- The contexts of the function-level rows: the `return 1 + 2;` file. -/
def mainContexts : List Codec.FileBindings := [addBindings 1 2]

/-- The programs the registered rows (`silmaril/c-tv.toml`) name. -/
def foldSource : Closed := add 1 2
def foldTarget : Closed := add 3 0
def wrongFoldTarget : Closed := add 2 2
def foldSourceBindings : Codec.FileBindings := addBindings 1 2
def foldTargetBindings : Codec.FileBindings := addBindings 3 0

/-- A **synthetic** file: the `1 + 2` file whose function information gives `main` the return
type `float`. It exists to exercise `Profile.AppliesTo` on a mention the x86-64 profile is not
coherent at; it is not the output of any frontend. -/
def floatSignatureBindings : Codec.FileBindings :=
  let b := addBindings 1 2
  { b with funInfo := b.funInfo.map fun (sym, loc, attrs, _, ps, v, d) =>
      (sym, loc, attrs, Ctype.mk [] (.basic (.floating (.realFloating .float))), ps, v, d) }

/-- The same file without a `main` symbol: its startup ends in an `error` gap. -/
def noMain : Closed := ⟨{ (add 1 2).file with main := none }, ∅, []⟩

/-- `INT_MAX + 1`: signed overflow, undefined behaviour (C11 §6.5p5). -/
def overflow : Closed := add 2147483647 1

/-- `return 2 + 2;`, a target that `overflow` covers only through undefined behaviour. -/
def overflowTarget : Closed := add 2 2

/-- An implementation whose exit status keeps only the low bit (a deliberately unusual host, to
show that observations depend on the implementation-defined choices). -/
def lowBitHost : Spec.Impl := { status := fun n => (n % 2).toNat }

/-! ## Two functions: `main` calls `id`

The typed Ail of `int id(int x) { return E; } int main(void) { return id(A); }` for a body `E` and
an argument `A`, elaborated by the Lean elaborator with the explicit runtime of
`Silmaril.Compiler.Core.ParameterCallReturn` (as that module's own example is). The module-level
rows replace both functions. -/

section TwoFunctions
open Silmaril.Compiler.Core.ParameterCallReturn Silmaril.Compiler.Core.ParameterCallReturn.Example
open Silmaril.Cerberus.Elaboration

/-- The integer constant `n`. -/
def lit (n : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant n .decimal none)))

/-- `a + b` on integer constants. -/
def addLit (a b : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.binary (lit a) (.arithmetic .add) (lit b))

/-- `id(arg)`. -/
def callId (arg : Ail.TypedExpression) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.call (.mk (.rvalue (.pointer qualifiers functionType)) [] .unknown (.functionDecay
      (.mk (.lvalue qualifiers functionType false) [] .unknown (.ident fSymbol)))) [arg])

/-- `int id(int x) { return idBody; } int main(void) { return id(arg); }`. -/
def twoFunctions (idBody arg : Ail.TypedExpression) : Ail.TypedProgram :=
  let (m, s) := program
  (m, { s with functionDefinitions := [
      (fSymbol, {loc := .unknown, marker := 7, attrs := .mk [], params := [parameterSymbol], body := statement (.block [] [statement (.return_ idBody)])}),
      (mainSymbol, {loc := .unknown, marker := 8, attrs := .mk [], params := [], body := statement (.block [] [statement (.return_ (callId arg))])})] })

/-- The elaborated file (`AdditionSource.bindings 0 0` if the elaborator rejected it; the rows
check that it does not, `twoFunctions_elaborate` in `CTvRows`). -/
def elabTwo (idBody arg : Ail.TypedExpression) : Codec.FileBindings :=
  match (Functions.elaborate Silmaril.Cerberus.Target.pinnedApple Target.emptyEnvironment runtime
      (twoFunctions idBody arg) freshness).1 with
  | .ok b => b
  | .error _ => AdditionSource.bindings 0 0

/-- A function's definition in a file (a dummy declaration if absent). -/
def defOf (b : Codec.FileBindings) (f : Sym) : Core.FunDecl Codec.wireModel Unit Unit :=
  match b.funs.find? (fun e => e.1.key == f.key) with
  | some (_, d) => d
  | none => .builtinDecl .unknown .unit []

/-- `int id(int x) { return x; } int main(void) { return id(42); }`. -/
def twoBefore : Codec.FileBindings := elabTwo parameterExpression integer42
/-- `int id(int x) { return 42; } int main(void) { return id(40 + 2); }`. -/
def twoAfter : Codec.FileBindings := elabTwo (lit 42) (addLit 40 2)
/-- `int id(int x) { return 41; } …`: a wrong replacement of `id`. -/
def twoWrong : Codec.FileBindings := elabTwo (lit 41) integer42

/-- The contexts of the module-level rows: the `twoBefore` file. -/
def twoContexts : List Codec.FileBindings := [twoBefore]

/-- Replace `id` (by `return 42;`) and `main` (by `return id(40 + 2);`). `id := return 42;` is not
a correct `id` in general: it refines only because the context calls `id(42)`. -/
def twoReplacements : List Replacement :=
  [⟨fSymbol, defOf twoBefore fSymbol, defOf twoAfter fSymbol⟩,
   ⟨mainSymbol, defOf twoBefore mainSymbol, defOf twoAfter mainSymbol⟩]

/-- Replace `id` by `return 41;`: refuted. -/
def twoWrongReplacements : List Replacement :=
  [⟨fSymbol, defOf twoBefore fSymbol, defOf twoWrong fSymbol⟩]

end TwoFunctions

end Silmaril.Project.CTV.Examples
