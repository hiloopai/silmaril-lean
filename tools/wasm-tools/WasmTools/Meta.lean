import WasmTools.Types
import Silmaril.Wasm.Tools.Meta.Main.Defs
import Silmaril.Wasm.Tools.Text.Defs

/-!
# `wasm-tools` subcommands: Meta group

Subcommands of this group: demangle, metadata, addr2line. The commands
themselves are `WasmTools.Meta.subcommands` (`Silmaril.Wasm.Tools.Meta.Main.Defs`); this module
gives them the WAT parser and printer as hooks (`Silmaril.Wasm.Tools.Text`): text
input is assembled by `watToBinary`, and `-t` prints with `binaryToWat` (the wasmprinter-format
printer `Silmaril.Wasm.Tools.Print`, checked; see tools/wasm-tools/README.md).
-/

namespace WasmTools.Meta

/-- The hooks of the main binary. -/
def mainHooks : Hooks where
  parseText := some Silmaril.Wasm.Tools.Text.watToBinary
  printWat := some Silmaril.Wasm.Tools.Text.binaryToWat

/-- The subcommands this group implements. -/
def table : List Subcommand :=
  (subcommands mainHooks).map fun (name, run) => { name, run }

end WasmTools.Meta
