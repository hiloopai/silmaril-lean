module

public import Silmaril.Formats.Json.Fast.Parser.Defs
public import Silmaril.Formats.Json.Fast.Wire.Defs

/-! The runtime JSON loading API: `Silmaril.Formats.Json.Fast.load`, `parseBytes`, `parseText`,
and `Value.at?`. Import `Silmaril.Formats.Json.Fast.Elab` separately for elaborators and tactics.
Use `Silmaril.Formats.JsonWire.Defs` for lossless syntax or lone-surrogate escapes. -/
