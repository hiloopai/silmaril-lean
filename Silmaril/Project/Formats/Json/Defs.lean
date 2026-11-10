module

public import Silmaril.Project.Defs
public import Silmaril.Formats.JsonWire.Defs

/-!
# The format `json.rfc8259`

RFC 8259 bytes to the ordered wire AST with exact decimals, `Silmaril.Formats.JsonWire.parse?`
(UTF-16 code-unit strings, so lone surrogate escapes are kept; object members in order, with
duplicates; numbers as exact `Decimal`s). Printer: the total structural printer
`Silmaril.Formats.JsonWire.encode`. The family default of `json`.

Gaps: no round-trip theorem relates the printer and the reader, so no law is registered; the
reader is not proved against an independent RFC 8259 grammar. silmaril's extensional reader
`Silmaril.Formats.RfcJson.parse?` (strings, duplicate members rejected) is a different data
model and is not a format here.
-/

@[expose] public section
namespace Silmaril.Project.Formats

/-- RFC 8259 JSON, ordered wire AST with exact decimal numbers. -/
def json : Format blob (Silmaril.Formats.JsonWire.Ast Silmaril.Formats.JsonWire.Decimal) where
  parse := Silmaril.Formats.JsonWire.parse?
  print := some fun v => some (Silmaril.Formats.JsonWire.encode v)

end Silmaril.Project.Formats

silmaril format json.rfc8259 := Silmaril.Project.Formats.json
  (doc := "RFC 8259 JSON to the ordered wire AST with exact decimals (Silmaril.Formats.JsonWire.parse?)")
silmaril format_default json := json.rfc8259
