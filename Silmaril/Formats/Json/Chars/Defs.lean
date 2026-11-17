module

public import Silmaril.Formats.Json.Thms

/-!
# JSON from characters: the standard parser without its UTF-8 step

`Json.parseDecimal?` decodes its bytes with `String.fromUTF8?` and then lexes and parses the
characters. The UTF-8 step is cheap when compiled but slow in the kernel (seconds per kilobyte
of `decide +kernel`), while the lexer and parser are fast there. `parseChars?` is the same
lexer and parser on a character list, so a kernel computation can start from characters
(`Thms.parseDecimal?_eq_parseChars?` gives the relation to `parseDecimal?`).

`asciiChars` reads ASCII bytes as characters, structurally, and refuses any byte from `0x80`:
a pinned JSON artifact written with only ASCII bytes (non-ASCII text escaped as `\uXXXX`) is
read by `parseAscii?` without a UTF-8 decoder.
-/

@[expose] public section

namespace Silmaril.Formats.Json

/-- The lexer and parser of `parseDecimal?`, on characters. -/
def parseChars? (dialect : Dialect) (cs : List Char) : Option (Ast Decimal) := do
  let lexed ← Internal.lex dialect (cs.length + 1) 0 cs
  let (ast, rest) ← Internal.value? dialect (2 * lexed.tokens.length + 1) lexed.tokens
  if rest.isEmpty then mapNumbers? (fun | .finite d => some d | _ => none) ast else none

/-- ASCII bytes as characters; `none` if a byte is `0x80` or above. -/
def asciiChars : List UInt8 → Option (List Char)
  | [] => some []
  | b :: bs => if b.toNat < 0x80 then (Char.ofNat b.toNat :: ·) <$> asciiChars bs else none

/-- An RFC 8259 document of ASCII bytes. -/
def parseAscii? (bytes : List UInt8) : Option (Ast Decimal) :=
  (asciiChars bytes).bind (parseChars? .rfc8259)

end Silmaril.Formats.Json

end
