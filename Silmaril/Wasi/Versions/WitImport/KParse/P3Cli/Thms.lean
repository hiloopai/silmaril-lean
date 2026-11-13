module

public import Silmaril.Wasi.Versions.WitImport.KLex.Thms

@[expose] public section

/-!
# Kernel-checked parsing of `wasi:cli` (0.3.2)

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

/-- `specs/wasi/0.3.2/cli/command.wit` parses. -/
theorem parse_p3_cli_command :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/command.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/environment.wit` parses. -/
theorem parse_p3_cli_environment :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/environment.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/exit.wit` parses. -/
theorem parse_p3_cli_exit :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/exit.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/imports.wit` parses. -/
theorem parse_p3_cli_imports :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/imports.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/run.wit` parses. -/
theorem parse_p3_cli_run :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/run.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/stdio.wit` parses. -/
theorem parse_p3_cli_stdio :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/stdio.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

/-- `specs/wasi/0.3.2/cli/terminal.wit` parses. -/
theorem parse_p3_cli_terminal :
    ((lex (wit_src% "../../../../../../specs/wasi/0.3.2/cli/terminal.wit")).bind Parse.document).isSome = true := by
  rw [← parseCharsK_eq]; decide +kernel

end Silmaril.Wasi.Versions.WitImport
