module

public import Silmaril.Project.Formats.SExp.Defs
public import Silmaril.Project.Formats.SExpWat.Defs
public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Project.Formats.Wat.Defs
public import Silmaril.Project.Formats.Elf.Defs
public import Silmaril.Project.Formats.Json.Defs

/-!
# Silmaril projects: the format adapters over silmaril's parsers

S-expressions (`sexp.text`, `sexp.canonical`, `sexp.wat`), WebAssembly (`wasm.binary.core`,
`wat.sexp`), ELF (`elf.elf64le`, `elf.exec-x86`) and JSON (`json.rfc8259`), with the family
defaults `sexp`, `wasm`, `wat`, `elf` and `json`. Their laws and examples are `Silmaril.Project.Formats.Thms`.
-/
