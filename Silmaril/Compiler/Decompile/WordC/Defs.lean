module

public import Silmaril.X86.Decompile.VC.Defs
public import Silmaril.Cerberus.Assertion.Pure.Defs
public import Silmaril.Compiler.C.Sem.C0.Defs
/-! Pure qword SSA expressions regenerated as real typed Ail and C source.
The shared arithmetic representation is the existing Cerberus assertion
`Pure.Term`; no additional expression language is introduced here. -/

@[expose] public section
namespace Silmaril.Compiler.Decompile.WordC

open Silmaril.X86 (Reg Word)
open Silmaril.X86.Decompile.SemLift (Ex)
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion

/-- Interpret the existing pure arithmetic language in unsigned machine words.
This is observation modulo 2^64 of its mathematical integer interpretation. -/
def wordValue (values : String → Word) (term : Pure.Term) : Word :=
  BitVec.ofInt 64 (term.eval fun name => (values name).toNat)

/-- Declared register inputs are explicit; an undeclared input is rejected.
Only pure 64-bit constants, moves, add/sub and bounded constant left shifts
are supported. Left shifts become multiplication by a nonnegative ULL literal.
Loads, 32-bit truncation, right shifts, bitwise operations, byte swaps, and
flags do not silently acquire C semantics. -/
def fromSSA (inputs : Reg → Option String) : Ex → Except String Pure.Term
  | .reg register =>
      match inputs register with
      | some name => .ok (.var name)
      | none => .error "SSA expression reads an undeclared register input"
  | .const value => .ok (.literal value.toNat)
  | .ext .q value => fromSSA inputs value
  | .alu .q .add left right => return .add (← fromSSA inputs left) (← fromSSA inputs right)
  | .alu .q .sub left right => return .sub (← fromSSA inputs left) (← fromSSA inputs right)
  | .shift .q .shl value count => do
      if count < 64 then
        return .mul (← fromSSA inputs value) (.literal (BitVec.twoPow 64 count).toNat)
      else .error "constant shift count is outside the unsigned 64-bit C fragment"
  | _ => .error "SSA expression is outside the pure unsigned 64-bit C fragment"

/-- Fixed LP64 unsigned-long-long object type. -/
def unsignedType : Ctype := .mk [] (.basic (.integer (.unsigned .longLong)))

def unsignedAnnotation : GenTypeCategory :=
  .rvalue (.basic (.integer (.concrete (.unsigned .longLong))))

def unsignedExpr (node : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk unsignedAnnotation [] .unknown node

def localExpr (symbol : Sym) : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ unsignedType false) [] .unknown (.ident symbol)

/-- Actual typed Ail expressions consumed by C0 and the C compiler. Literals
are normalized into ULL's range, including arbitrary `Pure.Term` integers. -/
def toAil (symbols : String → Sym) : Pure.Term → TypedExpression
  | .literal value => unsignedExpr (.const (.integer
      (.iconstant (BitVec.ofInt 64 value).toNat .decimal (some .ull))))
  | .var name => unsignedExpr (.rvalue (localExpr (symbols name)))
  | .add left right => unsignedExpr
      (.binary (toAil symbols left) (.arithmetic .add) (toAil symbols right))
  | .sub left right => unsignedExpr
      (.binary (toAil symbols left) (.arithmetic .sub) (toAil symbols right))
  | .mul left right => unsignedExpr
      (.binary (toAil symbols left) (.arithmetic .mul) (toAil symbols right))

/-- Every arithmetic operation has unsigned 64-bit operands; parentheses make
the source independent of operator precedence. -/
def printExpr (renderName : String → String) : Pure.Term → String
  | .literal value => s!"{(BitVec.ofInt 64 value).toNat}ULL"
  | .var name => renderName name
  | .add left right => s!"({printExpr renderName left} + {printExpr renderName right})"
  | .sub left right => s!"({printExpr renderName left} - {printExpr renderName right})"
  | .mul left right => s!"({printExpr renderName left} * {printExpr renderName right})"

def freeNames : Pure.Term → List String
  | .literal _ => []
  | .var name => [name]
  | .add left right | .sub left right | .mul left right => freeNames left ++ freeNames right

def identifier (name : String) : Bool :=
  let first := fun c : Char => c == '_' ||
    decide ('a' ≤ c ∧ c ≤ 'z') || decide ('A' ≤ c ∧ c ≤ 'Z')
  let rest := fun c : Char => first c || decide ('0' ≤ c ∧ c ≤ '9')
  match name.toList with
  | [] => false
  | head :: tail => first head && tail.all rest

/-- Emit a complete fixed-profile C function. Names must be distinct C
identifiers and every variable must be declared. Prefixing generated names
avoids C keywords and reserved external identifiers without a keyword table. -/
def printFunction (name : String) (parameters : List String) (term : Pure.Term) :
    Except String String := do
  if !identifier name || !(parameters.all identifier) then
    throw "generated function or parameter name is not an ASCII identifier"
  if parameters.eraseDups.length != parameters.length then
    throw "generated parameter names are not distinct"
  if !(freeNames term).all (fun input => parameters.contains input) then
    throw "generated expression contains an undeclared C parameter"
  let parameters := parameters.map fun parameter => "unsigned long long wc_" ++ parameter
  let arguments := if parameters.isEmpty then "void" else String.intercalate ", " parameters
  return "unsigned long long wc_" ++ name ++ "(" ++ arguments ++ ") {\n  return " ++
    printExpr ("wc_" ++ ·) term ++ ";\n}\n"

def height : Pure.Term → Nat
  | .literal _ | .var _ => 1
  | .add left right | .sub left right | .mul left right => max (height left) (height right) + 1

/-- Symbols for the generated function's actual parameter slots. -/
def parameterSymbol (parameters : List String) (name : String) : Sym :=
  ⟨⟨[]⟩, parameters.idxOf name, .id ("wc_" ++ name)⟩

structure Artifact where
  term : Pure.Term
  expression : TypedExpression
  source : String

/-- A pure, separate regeneration pass from the existing SSA expression graph
to typed Ail plus a concrete C translation unit. No source text is parsed or
executed by this transformation. -/
def regenerate (name : String) (inputs : List (Reg × String)) (expression : Ex) :
    Except String Artifact := do
  if (inputs.map Prod.fst).eraseDups.length != inputs.length then
    throw "generated input registers are not distinct"
  let parameters := inputs.map Prod.snd
  let term ← fromSSA (fun register => inputs.lookup register) expression
  let source ← printFunction name parameters term
  return ⟨term, toAil (parameterSymbol parameters) term, source⟩

end Silmaril.Compiler.Decompile.WordC
