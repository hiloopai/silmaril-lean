import WasmTools.Types
import WasmTools.ValidateCmd
import WasmTools.Strip
import WasmTools.Objdump
import WasmTools.Dump

/-!
# `wasm-tools` subcommands: Validate group

Subcommands of this group: validate, strip, objdump, dump (core modules; see
`tools/wasm-tools/README.md`). The main dispatch in `WasmTools.lean` consults
the table; a subcommand that no table implements is reported as not implemented.
-/

namespace WasmTools.Validate

/-- The subcommands this group implements. -/
def table : List Subcommand :=
  [⟨"validate", WasmTools.ValidateCmd.run⟩,
   ⟨"strip", WasmTools.Strip.run⟩,
   ⟨"objdump", WasmTools.Objdump.run⟩,
   ⟨"dump", WasmTools.Dump.run⟩]

end WasmTools.Validate
