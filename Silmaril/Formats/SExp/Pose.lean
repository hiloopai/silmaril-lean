module

public import Silmaril.Formats.SExp.Parser
public import Silmaril.Formats.Json.RfcParser

/-!
# Portable S-expressions (POSE)

Implements the grammar published by `s-expressions/pose`: proper lists,
lowercase ASCII symbols, strings with only `\\` and `\"` escapes, and exact
integer/floating-point number lexemes.
-/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats

inductive PoseNumber where
  | integer (literal : String)
  | float (literal : String)
  deriving DecidableEq, Repr

inductive PoseAtom where
  | symbol (name : String)
  | string (value : String)
  | number (value : PoseNumber)
  deriving DecidableEq, Repr

abbrev Pose := SExp PoseAtom
abbrev PoseDocument := List Pose

namespace Pose

def lower (c : Char) : Bool := decide ('a' ≤ c ∧ c ≤ 'z')
def digit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

def punctFirst (c : Char) : Bool :=
  c = '!' || c = '$' || c = '&' || c = '*' || c = '+' || c = '-' ||
  c = '/' || c = '<' || c = '=' || c = '>' || c = '_'

def punctCont (c : Char) : Bool :=
  punctFirst c || c = '.' || c = '?' || c = '@'

def wordFirst (c : Char) : Bool := lower c || punctFirst c
def wordCont (c : Char) : Bool := lower c || punctCont c || digit c

def wordSymbol : List Char → Bool
  | first :: rest => wordFirst first && rest.all wordCont
  | [] => false

def signSymbol : List Char → Bool
  | [sign] => sign = '+' || sign = '-'
  | sign :: second :: rest =>
      (sign = '+' || sign = '-') && (lower second || punctCont second) &&
        rest.all wordCont
  | _ => false

/-- POSE's exact symbol grammar, including its restricted single-colon prefix. -/
def validSymbol (value : String) : Bool :=
  match value.toList with
  | ':' :: rest => wordSymbol rest
  | chars => wordSymbol chars || signSymbol chars

def numberRequired : List Char → Bool
  | first :: rest =>
      digit first || ((first = '+' || first = '-') && match rest with
        | second :: _ => digit second
        | [] => false)
  | _ => false

def parseNumber? (value : String) : Option PoseNumber :=
  match RfcJson.parse? value with
  | some (.scalar (some (.number literal))) =>
      if literal.contains fun c => c = '.' || c = 'e' || c = 'E' then
        some (.float literal)
      else some (.integer literal)
  | _ => none

def classify : SExpParser.Lexeme → Option PoseAtom
  | .string value => some (.string value)
  | .symbol value =>
      if numberRequired value.toList then .number <$> parseNumber? value
      else if validSymbol value then some (.symbol value) else none

def traverse : Nat → SExp SExpParser.Lexeme → Option Pose
  | 0, _ => none
  | _ + 1, .atom value => .atom <$> classify value
  | fuel + 1, .list _ children => do
      let children ← (List.ofFn children).mapM (traverse fuel)
      some (SExp.ofList children)

/-- Parse all expressions in a POSE document. -/
def parseDocument? (text : String) : Option PoseDocument := do
  let values ← SExpParser.parsePoseLexemes? text
  values.mapM (traverse (text.length + 1))

/-- Parse a POSE document containing exactly one expression. -/
def parse? (text : String) : Option Pose := do
  let values ← parseDocument? text
  match values with
  | [value] => some value
  | _ => none

example : (parse? "(Foo)").isNone = true := by cbv

example : (parse? "(01)").isNone = true := by cbv

example : (parse? "(a . b)").isNone = true := by cbv

attribute [local cbv_eval] String.contains_bool_eq in
example : (parse? "(foo :bar -12 1.5e2 \"a\\\\b\\\"c\")").isSome = true := by
  cbv


end Pose
end Silmaril.Formats
