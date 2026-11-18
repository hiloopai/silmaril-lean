module

public import Silmaril.Formats.Json.Fast.Parser.Trace.Defs
public import Silmaril.Formats.Json.Fast.Wire.Defs
public import Silmaril.Formats.JsonWire.Grammar.Defs
import Silmaril.Proofs.Formats.Json.Fast.Parser
import Silmaril.Prelude.ChunkSeq.Thms
import Silmaril.Formats.Json.Fast.Thms

/-! Verified components of the production parser, not an independent parser or a
source certificate. All results concern successful computations. -/

public section
namespace Silmaril.Formats.Json.Fast.Parser

open JsonWire

theorem whitespace_consumes (offset : Nat) (input : List Char) :
    ∃ consumed, input = consumed ++ (whitespace offset input).rest ∧ White consumed :=
  Proofs.Json.Fast.Parser.whitespace_consumes offset input

theorem literal_consumes {literalChars : List Char} {pos stop : Pos}
    (result : literal literalChars pos = .ok stop) : pos.rest = literalChars ++ stop.rest :=
  Proofs.Json.Fast.Parser.literal_consumes result

/-- Same exact decimal (including its sign and scale), not merely the number token kind. -/
theorem numberLoop_sound {start stop : Pos} {fuel : Nat} {value : Value}
    (result : numberLoop start fuel start [] = .ok (value, stop)) :
    ∃ read decimal, start.rest = read ++ stop.rest ∧ value = .number decimal ∧
      Internal.NumberChars read ∧ Internal.decimal? .rfc8259 read = some (.finite decimal) :=
  Proofs.Json.Fast.Parser.numberLoop_sound result

theorem hex_sound {count acc decoded : Nat} {pos stop : Pos}
    (result : hex count pos acc = .ok (decoded, stop)) :
    ∃ code, Internal.hexes? count pos.rest = some (code, stop.rest) ∧ decoded = acc * 16 ^ count + code :=
  Proofs.Json.Fast.Parser.hex_sound result

/-- Successful production escapes consume one wire escape or one adjacent surrogate pair. -/
theorem unicodeEscape_sound {start stop : Pos} {char : Char}
    (parsed : unicodeEscape start = .ok (char, stop)) :
    ∃ units : Units, charUnits char = units ∧ unitsChars? units = some [char] ∧
      ((∃ unit, Internal.hexes? 4 start.rest = some (unit, stop.rest) ∧ units = [UInt16.ofNat unit]) ∨
        ∃ high low middle, Internal.hexes? 4 start.rest = some (high, '\\' :: 'u' :: middle) ∧
          Internal.hexes? 4 middle = some (low, stop.rest) ∧
          units = [UInt16.ofNat high, UInt16.ofNat low]) :=
  Proofs.Json.Fast.Parser.unicodeEscape_sound parsed

/-- Exact string payload and suffix of the independent RFC lexer, including paired escapes. -/
theorem quoted_tokens {size : Nat} {pos stop : Pos} {text : String}
    (ok : quoted size pos = .ok (text, stop)) :
    Internal.tokensOf pos.rest = (Internal.tokensOf stop.rest).map (.string (stringUnits text) :: ·) :=
  Proofs.Json.Fast.Parser.quoted_tokens ok

/-- Every pushed item is accounted for, in source order, under the item parser contract. -/
theorem more_sound {Item : Type} {close : Char} {Accept : List Char → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)} (closeNotSentinel : close ≠ Char.ofNat 0)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) →
      ∃ lexeme, pos.rest = lexeme ++ stop.rest ∧ Accept lexeme item)
    {fuel : Nat} {pos stop : Pos} {acc output : Array Item}
    (result : more close parseItem fuel pos acc = .ok (output, stop)) :
    ∃ span items, pos.rest = span ++ stop.rest ∧
      output.toList = acc.toList ++ items ∧ Tail close Accept span items :=
  Proofs.Json.Fast.Parser.more_sound closeNotSentinel soundItem result

/-- The exact span after the opening delimiter, including the closing delimiter. -/
theorem series_sound {Item : Type} {close : Char} {Accept : List Char → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)} (closeNotSentinel : close ≠ Char.ofNat 0)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) →
      ∃ lexeme, pos.rest = lexeme ++ stop.rest ∧ Accept lexeme item)
    {size : Nat} {pos stop : Pos} {output : Array Item}
    (result : series size close parseItem pos = .ok (output, stop)) :
    ∃ left span, pos.rest = left ++ span ++ stop.rest ∧ White left ∧
      ((span = [close] ∧ output.toList = []) ∨ Tail close Accept span output.toList) :=
  Proofs.Json.Fast.Parser.series_sound closeNotSentinel soundItem result

end Silmaril.Formats.Json.Fast.Parser

namespace Silmaril.Formats.Json.Fast.Value

/-- A successful indexed lookup selects a real ordered member. This is not a
first-occurrence or completeness theorem for the hash index. -/
theorem member?_ofObject_sound {entries : Array (String × Value)} {key : String} {child : Value}
    (found : (ofObject entries).member? key = some child) : (key, child) ∈ entries.toList := by
  have member := Value.member?_sound (ChunkSeq.wellSized_ofArray entries) found
  simpa only [ChunkSeq.toList_ofArray] using member

theorem toWire?_ofArray (depth : Nat) (items : Array Value) :
    (ofArray items).toWire? (depth + 1) = do
      let children ← items.toList.mapM (toWire? depth)
      return .list (children.foldr .cons .nil) :=
  Proofs.Json.Fast.Parser.ofArray_wire depth items

/-- The cache is ignored by the wire projection; every member is retained. -/
theorem toWire?_ofObject (depth : Nat) (entries : Array (String × Value)) :
    (ofObject entries).toWire? (depth + 1) = do
      let children ← entries.toList.mapM fun (key, child) => do
        return (JsonWire.stringUnits key, ← child.toWire? depth)
      return .map (children.foldr (fun (key, child) tail => .objCons key child tail) .objNil) :=
  Proofs.Json.Fast.Parser.ofObject_wire depth entries

end Silmaril.Formats.Json.Fast.Value
