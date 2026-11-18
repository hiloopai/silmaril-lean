module

public import Silmaril.Formats.Json.Fast.Wire.Defs
public import Silmaril.Formats.JsonWire.Grammar.Defs

/-! Interfaces for proving semantic, not merely token-kind, agreement with the wire reader. -/

@[expose] public section
namespace Silmaril.Formats.Json.Fast.Parser

open JsonWire Internal

def Follows (suffix : List Char) : Prop := ∀ char ∈ suffix.head?, delimiter .rfc8259 char = true

/-- An exact lexer prefix; unrelated or malformed remaining input need not lex successfully. -/
def LexedPrefix (input suffix : List Char) (tokens : List Token) : Prop :=
  tokensOf input = (tokensOf suffix).map (tokens ++ ·)

/-- Ordered tokens and the corresponding items from a nonempty container tail. -/
inductive WireTail {Item : Type} (close : Token) (Accept : List Token → Item → Prop) :
    List Token → List Item → Prop where
  | last {tokens : List Token} {item : Item} : Accept tokens item → WireTail close Accept (tokens ++ [close]) [item]
  | next {tokens tail : List Token} {item : Item} {items : List Item} :
    Accept tokens item → WireTail close Accept tail items →
    WireTail close Accept (tokens ++ .comma :: tail) (item :: items)

def liftScalar : Scalar Decimal → Scalar Number
  | none => none
  | some (.bool flag) => some (.bool flag)
  | some (.string units) => some (.string units)
  | some (.number decimal) => some (.number (.finite decimal))

def ReadsValue (tokens : List Token) (ast : Ast Decimal) : Prop :=
  ∀ fuel, tokens.length < fuel → ∀ suffix,
    value? .rfc8259 fuel (tokens ++ suffix) = some (ast.mapScalar liftScalar, suffix)

def MatchesValue (depth : Nat) (tokens : List Token) (value : Value) : Prop :=
  ∃ ast, value.toWire? depth = some ast ∧ ReadsValue tokens ast

def MatchesMember (depth : Nat) (tokens : List Token) (entry : String × Value) : Prop :=
  ∃ child, tokens = .string (stringUnits entry.1) :: .colon :: child ∧ MatchesValue depth child entry.2

end Silmaril.Formats.Json.Fast.Parser
