module

public import Silmaril.Formats.JsonWire.Grammar.Defs
public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Formats.Utf8.Defs
import Silmaril.Proofs.Formats.JsonWire.Parser
import Silmaril.Proofs.Formats.JsonWire.Lexer
import Silmaril.Proofs.Formats.JsonWire.Bytes

/-!
# JSON on the wire: each stage of the reader against a declarative grammar

The pieces of the proof that `Silmaril.Formats.JsonWire.parse?` accepts exactly RFC 8259's JSON
texts (`Silmaril.Formats.JsonWire.Thms`, `parse?_isSome_iff`), stated so that other readers and
grammars can reuse them:

* **parser** (`value?`): it reads all of a token list with enough fuel iff the list is a
  `TValue` (`value?_eq_some_nil_iff`); fuel as large as the number of tokens suffices
  (`TValue.complete`), and what it reads is a `TValue` prefix (`value?_sound`);
* **lexer** (`tokensOf`, one `step` at a time): it skips whitespace (`tokensOf_white_append`);
  its tokens are whitespace and lexemes (`lexes_of_tokensOf`); a lexeme followed by a delimiter
  is read as its token (`tokensOf_number`, `tokensOf_string`, …);
* **lexemes**: `quoted?` reads exactly the string bodies `StrBody` (`quoted?_sound`,
  `quoted?_complete`), `decimal?` exactly the numbers `NumberChars`, as finite decimals
  (`decimal?_sound`, `decimal?_complete`);
* **bytes**: the character conditions are the byte expressions of `Silmaril.Formats.JsonBytes`
  read through UTF-8 (`mem_number`, `mem_string`), by the transport lemmas of
  `Silmaril.Formats.Utf8.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire.Internal

/-- **The parser accepts exactly the token grammar**, given at least one fuel per token. -/
theorem value?_eq_some_nil_iff {ts : List Token} {f : Nat} (hf : ts.length ≤ f) :
    (∃ a, value? .rfc8259 f ts = some (a, [])) ↔ TValue ts :=
  Silmaril.Proofs.Formats.JsonWire.Parser.value?_eq_some_nil_iff hf

/-- The parser reads a `TValue` followed by anything, given one fuel per token of the value. -/
theorem TValue.complete {p : List Token} (h : TValue p) (f : Nat) (hf : p.length ≤ f)
    (r : List Token) : ∃ a, value? .rfc8259 f (p ++ r) = some (a, r) :=
  Silmaril.Proofs.Formats.JsonWire.Parser.value_complete h f hf r

/-- What the parser reads is a `TValue` prefix of its input. -/
theorem value?_sound {f : Nat} {ts r : List Token} {a : Ast Number}
    (h : value? .rfc8259 f ts = some (a, r)) : ∃ p, ts = p ++ r ∧ TValue p :=
  (Silmaril.Proofs.Formats.JsonWire.Parser.sound f).1 ts a r h

/-- The lexer's tokens do not depend on its fuel (when it is enough) or its offset. -/
theorem lex_tokens_eq {cs : List Char} {f off : Nat} (hf : cs.length < f) :
    (lex .rfc8259 f off cs).map Lexed.tokens = tokensOf cs :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.lex_tokens_eq cs.length cs f off le_rfl hf

/-- One lexer step on `tokensOf`. -/
theorem tokensOf_cons (c : Char) (cs : List Char) :
    tokensOf (c :: cs) = match step .rfc8259 c cs with
      | none => none
      | some (t, _, rest) =>
        if rest.length < cs.length + 1 then (tokensOf rest).map (t.toList ++ ·) else none :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_cons c cs

/-- Whitespace makes no tokens. -/
theorem tokensOf_white_append {ws : List Char} (hw : ∀ c ∈ ws, white .rfc8259 c = true)
    (r : List Char) : tokensOf (ws ++ r) = tokensOf r :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_white_append hw r

/-- **The lexer is sound**: what it reads is whitespace and lexemes. -/
theorem lexes_of_tokensOf {cs : List Char} {ts : List Token} (h : tokensOf cs = some ts) :
    Lexes cs ts :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.lexes_of_tokensOf cs.length cs ts le_rfl h

/-- A string lexeme is read as a string token. -/
theorem tokensOf_string {b : List Char} (hb : StrBody b) (X : List Char) :
    ∃ u, tokensOf (('"' :: (b ++ ['"'])) ++ X) = (tokensOf X).map (.string u :: ·) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_string hb X

/-- A number lexeme followed by a delimiter (or nothing) is read as a finite number token. -/
theorem tokensOf_number {w : List Char} (hw : NumberChars w) {X : List Char}
    (hX : ∀ c ∈ X.head?, delimiter .rfc8259 c = true) :
    ∃ n, tokensOf (w ++ X) = (tokensOf X).map (.number n :: ·) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_number hw hX

/-- The lexer preserves the exact number payload read by `decimal?`. -/
theorem tokensOf_number_exact {w X : List Char} {number : Number}
    (parsed : decimal? .rfc8259 w = some number)
    (follow : ∀ char ∈ X.head?, delimiter .rfc8259 char = true) :
    tokensOf (w ++ X) = (tokensOf X).map (.number number :: ·) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_number_exact parsed follow

theorem tokensOf_literal {w : List Char} {tok : Token} (word : w = "true".toList ∧ tok = .bool true ∨
    w = "false".toList ∧ tok = .bool false ∨ w = "null".toList ∧ tok = .null) {rest : List Char}
    (follows : ∀ c ∈ rest.head?, delimiter .rfc8259 c = true) :
    tokensOf (w ++ rest) = (tokensOf rest).map (tok :: ·) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_literal word follows

theorem tokensOf_punct {c : Char} {tok : Token} (punct : c = '[' ∧ tok = .arrayOpen ∨
    c = ']' ∧ tok = .arrayClose ∨ c = '{' ∧ tok = .objectOpen ∨ c = '}' ∧ tok = .objectClose ∨
    c = ',' ∧ tok = .comma ∨ c = ':' ∧ tok = .colon) (rest : List Char) :
    tokensOf (c :: rest) = (tokensOf rest).map (tok :: ·) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.tokensOf_punct punct rest

/-- `quoted?` reads a string body up to its closing quote. -/
theorem quoted?_sound {fuel : Nat} {cs rest : List Char} {u : Units}
    (h : quoted? .rfc8259 '"' fuel cs = some (u, rest)) : ∃ b, cs = b ++ '"' :: rest ∧ StrBody b :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.quoted?_sound fuel cs rest u h

/-- `quoted?` reads every string body, given more fuel than characters. -/
theorem quoted?_complete {b : List Char} (hb : StrBody b) {fuel : Nat} (hf : b.length < fuel)
    (rest : List Char) : ∃ u, quoted? .rfc8259 '"' fuel (b ++ '"' :: rest) = some (u, rest) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.quoted?_complete hb fuel hf rest

/-- `decimal?` reads only RFC 8259 numbers, as finite decimals. -/
theorem decimal?_sound {text : List Char} {n : Number} (h : decimal? .rfc8259 text = some n) :
    NumberChars text ∧ ∃ d, n = .finite d :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.decimal?_sound h

/-- `decimal?` reads every RFC 8259 number. -/
theorem decimal?_complete {text : List Char} (h : NumberChars text) :
    ∃ d, decimal? .rfc8259 text = some (.finite d) :=
  Silmaril.Proofs.Formats.JsonWire.Lexer.decimal?_complete h

/-- The characters of a number are the encodings that `JsonBytes.number` matches. -/
theorem mem_number {w : List Char} :
    Silmaril.Formats.Utf8.encode w ∈ Silmaril.Formats.JsonBytes.number.matches' ↔ NumberChars w :=
  Silmaril.Proofs.Formats.JsonWire.Bytes.mem_number

/-- The characters of a string are the encodings that `JsonBytes.string .rfc8259` matches. -/
theorem mem_string {w : List Char} :
    Silmaril.Formats.Utf8.encode w ∈ (Silmaril.Formats.JsonBytes.string .rfc8259).matches' ↔
      ∃ b, w = '"' :: (b ++ ['"']) ∧ StrBody b :=
  Silmaril.Proofs.Formats.JsonWire.Bytes.mem_string

end Silmaril.Formats.JsonWire.Internal

end
