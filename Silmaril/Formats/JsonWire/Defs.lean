module

public import Silmaril.Formats.JsonWire.Concrete.Defs
public import Silmaril.Formats.JsonWire.Ast.Defs
public import Silmaril.Formats.JsonWire.Lexer.Defs
public import Silmaril.Formats.JsonWire.Parser.Defs
public import Silmaril.Formats.JsonWire.Encoding.Defs

/-!
# JSON on the wire: an ordered reader and printer over bytes

A total reader of UTF-8 JSON bytes (RFC 8259, with the JSONC and JSON5 dialects) that keeps
what the wire shows and the extensional reader `Silmaril.Formats.RfcJson.parse?` forgets:

* **the AST** (`Ast N`, `Ast.Defs`): silmaril's indexed raw tree `KeyedRawJson` with UTF-16
  code-unit strings and keys (`Units`), so lone surrogate escapes are retained and object
  members keep their order and their duplicates; numbers are exact decimals (`Decimal`:
  sign, coefficient, exponent, no rounding) or, in JSON5, `Number`;
* **the concrete syntax** (`Cst`, `Concrete.Defs`): every token with its UTF-8 byte span,
  trivia included, certified to partition the input and serialize back to it;
* **the printer** (`encode`, `Encoding.Defs`): a total structural printer that writes every
  string as `\uXXXX` escapes (so lone surrogates survive). It is not a canonicalization.

The pipeline is `String.fromUTF8?`, the lexer (`Internal.lex`, fuel bounded by the character
count) and the recursive-descent parser (`Internal.value?`). Readers by profile:

| reader | dialect | numbers |
|---|---|---|
| `parse?` | RFC 8259 | `Decimal` |
| `parseJsonc?` | RFC 8259 with comments | `Decimal` |
| `parseJson5?` | JSON5 | `Number` (also `±Infinity`, `NaN`, hexadecimal) |
| `parseInteger?` | RFC 8259 | `Int`: only integral decimals (`1e2` is `100`) |
| `parseCst?` | any | the lossless concrete syntax |

Lemmas: `Silmaril.Formats.JsonWire.Thms`. The project format `json.rfc8259` is `parse?` with the
printer `encode` (`Silmaril.Project.Formats.json`). No round-trip theorem relates `encode` and
`parse?`.
-/

@[expose] public section

namespace Silmaril.Formats.JsonWire

/-- Parse a complete UTF-8 JSON or JSON5 document with a lossless CST. -/
def parseCst? (dialect : Dialect) (bytes : Bytes) : Option Cst := do
  let (ast, tokens) ← Internal.decode dialect bytes
  concrete? bytes ast tokens

/-- Full RFC string grammar (including lone surrogate escapes), ordered
members, duplicate names, and exact finite decimal numbers. -/
def parseDecimal? (dialect : Dialect) (bytes : Bytes) : Option (Ast Decimal) := do
  let (ast, _) ← Internal.decode dialect bytes
  mapNumbers? (fun | .finite d => some d | _ => none) ast

def parse? : Bytes → Option (Ast Decimal) := parseDecimal? .rfc8259

def parseJsonc? : Bytes → Option (Ast Decimal) := parseDecimal? .jsonc

def parseJson5? (bytes : Bytes) : Option (Ast Number) :=
  (Internal.decode .json5 bytes).map Prod.fst

/-- A simpler exact-integer model, accepting precisely integral decimal values.
For example `1e2` denotes the same integer as `100`. -/
def parseInteger? (bytes : Bytes) : Option (Ast Int) :=
  (parse? bytes).bind (mapNumbers? Decimal.toInt?)

abbrev IsJsonSlice := IsSlice parse?

/-- Syntactic validity of a CST is separate from its lossless byte partition. -/
def IsCst (dialect : Dialect) (cst : Cst) : Prop :=
  Internal.decode dialect cst.source = some (cst.ast, cst.events)

end Silmaril.Formats.JsonWire

end
