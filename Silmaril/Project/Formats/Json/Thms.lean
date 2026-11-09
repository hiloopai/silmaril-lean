module

public import Silmaril.Project.Formats.Json.Defs

/-! # The format `json.rfc8259`: examples

Kernel-checked reads of small documents: order and duplicate members are kept, a lone
surrogate escape is kept as its code unit, and a trailing comma is rejected.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Formats.JsonWire

/-- The bytes of a string literal. -/
def jsonText (s : String) : Silmaril.Formats.Bytes := ⟨s.toUTF8⟩

theorem json_example_parses :
    (json.parse (jsonText "{\"b\": [1, -2.5e3], \"a\": true, \"a\": null}")).isSome = true := by
  decide +kernel

/-- The code units of a string document. -/
def jsonUnits? : Ast Decimal → Option Units
  | .scalar (some (.string u)) => some u
  | _ => none

theorem json_example_lone_surrogate :
    (json.parse (jsonText "\"\\ud800\"")).bind jsonUnits? = some [0xD800] := by
  decide +kernel

theorem json_example_trailing_comma : json.parse (jsonText "[1,]") = none := by
  decide +kernel

end Silmaril.Project.Formats
