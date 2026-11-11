import Silmaril.Wasm.Binaryen.Driver.Defs
import Silmaril.Cli.Spec.WasmOpt.Defs
import Silmaril.Cli.Clap.Main.Defs

/-! `wasm-opt`: silmaril's `wasm-opt` CLI plus the verified stages.
See `Silmaril.Wasm.Binaryen.Driver` for the command line and
`Silmaril.Wasm.Binaryen.Pipeline.Thms` for the soundness theorems.

Help comes from the grammar: when the reading of `Silmaril.Cli.Spec.WasmOpt.tool` asks for help
(`-h`/`--help` anywhere on the command line), the program prints the derived help of that
grammar (`Silmaril.Cli.Clap.Tool.helpOr`, which meets `WasmOpt.tool.spec` on those command lines:
`Silmaril.Cli.Clap.Tool.helpOr_help`); every other command line goes to the driver, which reads it
itself (`Silmaril.Wasm.Binaryen.DriverSpec` compares that reading with the grammar's). -/

def main : List String → IO UInt32 :=
  Silmaril.Cli.Spec.WasmOpt.tool.helpOr Silmaril.Cli.Host.io Silmaril.Wasm.Binaryen.Driver.runExtraOpt
