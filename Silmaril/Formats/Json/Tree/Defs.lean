module
public import Silmaril.Formats.Json.Profiles.Defs
public import Silmaril.Formats.Json.Encoding.Defs
@[expose] public section
namespace Silmaril.Formats.Json

/-- Nested JSON value tree. Objects retain member order and duplicate names;
strings retain UTF-16 units, including unpaired surrogate escapes. -/
inductive Tree (N : Type := Decimal) where
  | scalar (value : Scalar N)
  | array (items : List (Tree N))
  | object (members : List (Units × Tree N))

namespace Tree

def null {N : Type} : Tree N := .scalar none
def bool {N : Type} (b : Bool) : Tree N := .scalar (some (.bool b))
def string {N : Type} (s : Units) : Tree N := .scalar (some (.string s))
def number {N : Type} (n : N) : Tree N := .scalar (some (.number n))
mutual
  def toAst {N : Type} : Tree N → Ast N
    | .scalar s => .scalar s
    | .array xs => .list (arrayToAst xs)
    | .object xs => .map (objectToAst xs)
  def arrayToAst {N : Type} : List (Tree N) → Syn N .arr
    | [] => .nil
    | x :: xs => .cons x.toAst (arrayToAst xs)
  def objectToAst {N : Type} : List (Units × Tree N) → Syn N .obj
    | [] => .objNil
    | (k, v) :: xs => .objCons k v.toAst (objectToAst xs)
end
mutual
  def ofAst {N : Type} : Ast N → Tree N
    | .scalar s => .scalar s
    | .list xs => .array (arrayOfAst xs)
    | .map xs => .object (objectOfAst xs)
  def arrayOfAst {N : Type} : Syn N .arr → List (Tree N)
    | .nil => []
    | .cons x xs => ofAst x :: arrayOfAst xs
  def objectOfAst {N : Type} : Syn N .obj → List (Units × Tree N)
    | .objNil => []
    | .objCons k v xs => (k, ofAst v) :: objectOfAst xs
end

/-- Typed semantic refinement, independent of syntax dialect or spelling. -/
abbrev Refined {N : Type} (accept : Ast N → Bool) :=
  {tree : Tree N // accept tree.toAst = true}

abbrev Rfc := Tree Decimal
abbrev Integer := Tree Int
abbrev Json5 := Tree Number
/-- JSONC changes syntax only, so has the same value vocabulary as RFC JSON. -/
abbrev Jsonc := Rfc
abbrev Unicode (N : Type := Decimal) := Refined (allStrings (N := N) scalarUnicode)
abbrev Unique (N : Type := Decimal) := Refined (distinctKeys (N := N))
abbrev PortableInteger := Refined (fun ast : Ast Int => portableIntegers.accepts .empty ast)
abbrev IjsonMagnitude := Refined (fun ast : Ast Decimal => ijsonMagnitude.accepts .empty ast)
abbrev BoundedDecimal (digits : Nat) (lo hi : Int) :=
  Refined (fun ast : Ast Decimal => (boundedDecimals digits lo hi).accepts .empty ast)
abbrev Container (N : Type := Decimal) :=
  Refined (fun ast : Ast N => containerRoot.accepts .empty ast)

def refine? {N : Type} (accept : Ast N → Bool) (tree : Tree N) : Option (Refined accept) :=
  if h : accept tree.toAst = true then some ⟨tree, h⟩ else none

def parse? (bytes : Bytes) : Option Rfc := ofAst <$> Json.parse? bytes
def parseInteger? (bytes : Bytes) : Option Integer := ofAst <$> Json.parseInteger? bytes
def parseJsonc? (bytes : Bytes) : Option Jsonc := ofAst <$> Json.parseJsonc? bytes
def parseJson5? (bytes : Bytes) : Option Json5 := ofAst <$> Json.parseJson5? bytes

def parseRefined? {N : Type} (decode : Bytes → Option (Ast N))
    (accept : Ast N → Bool) (bytes : Bytes) : Option (Refined accept) := do
  refine? accept (ofAst (← decode bytes))

def parsePortableInteger? := parseRefined? Json.parseInteger?
  (fun ast => portableIntegers.accepts .empty ast)

def abstractEvents {N : Type} (tree : Tree N) := Json.events tree.toAst
def encode (tree : Rfc) := Json.encode tree.toAst
def encodeInteger (tree : Integer) := Json.encodeInteger tree.toAst
def encodeJson5 (tree : Json5) := Json.encodeJson5 tree.toAst
/-- Concrete syntax forgets to the JSON5 vocabulary; RFC trees have finite numbers. -/
def ofCst (cst : Cst) : Json5 := ofAst cst.ast
end Tree
end Silmaril.Formats.Json
