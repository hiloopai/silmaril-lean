module

public import Silmaril.Formats.Json.Chars.Defs

/-! # JSON from characters: relation to the byte parser -/

@[expose] public section

namespace Silmaril.Formats.Json

/-- On bytes that decode to `text`, the byte parser is the character parser on `text`. -/
theorem parseDecimal?_eq_parseChars? {dialect : Dialect} {bytes : Bytes} {text : String}
    (h : String.fromUTF8? bytes.data = some text) :
    parseDecimal? dialect bytes = parseChars? dialect text.toList := by
  simp only [parseDecimal?, parseChars?, Internal.decode, h, Option.bind_eq_bind, Option.bind_some,
    Option.bind_assoc]
  congr 1; funext lexed; congr 1; funext r; split <;> rfl

end Silmaril.Formats.Json

end
