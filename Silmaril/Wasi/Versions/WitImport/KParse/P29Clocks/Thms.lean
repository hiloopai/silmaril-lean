module

public import Silmaril.Wasi.Versions.WitImport.KLex.Thms

@[expose] public section

/-!
# Kernel-checked parsing of `wasi:clocks` (v0.2.9)

For each vendored file, the text the WIT importer parses (`wit_src%`: the file with the header
of its directory and parameter docs demoted, as for `wit_table%`) is accepted by the verified
parser of `Silmaril.Wasm.Wit.Text` (`lex`, then `Parse.document`). The proof evaluates the
fuelled lexer `lexK` in the kernel (`decide +kernel`) and transfers along `parseCharsK_eq`.

Generated per file; see `docs/projects/wasm-wasi.md`, WASI full, http.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit.Text

set_option maxRecDepth 1000000

/-- `specs/wasi/v0.2.9/clocks/monotonic-clock.wit` parses. -/
theorem parse_p29_clocks_monotonic_clock :
    ((lex (wit_src% "../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/v0.2.9/clocks/timezone.wit` parses. -/
theorem parse_p29_clocks_timezone :
    ((lex (wit_src% "../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/v0.2.9/clocks/wall-clock.wit` parses. -/
theorem parse_p29_clocks_wall_clock :
    ((lex (wit_src% "../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/v0.2.9/clocks/world.wit` parses. -/
theorem parse_p29_clocks_world :
    ((lex (wit_src% "../../../../../../specs/wasi/v0.2.9/clocks/world.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

end Silmaril.Wasi.Versions.WitImport
