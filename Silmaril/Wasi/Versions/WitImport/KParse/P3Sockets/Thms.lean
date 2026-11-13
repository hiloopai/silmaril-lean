module

public import Silmaril.Wasi.Versions.WitImport.KLex.Thms

@[expose] public section

/-!
# Kernel-checked parsing of `wasi:sockets` (0.3.2)

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

/-- `specs/wasi/0.3.2/sockets/ip-name-lookup.wit` parses. -/
theorem parse_p3_sockets_ip_name_lookup :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/sockets/types.wit` parses. -/
theorem parse_p3_sockets_types :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/sockets/types.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/sockets/world.wit` parses. -/
theorem parse_p3_sockets_world :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/sockets/world.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

end Silmaril.Wasi.Versions.WitImport
