import WasmTools.SpecMain
import WasmTools.SpecCore
import WasmTools.Component
import WasmTools.GenTrack
import WasmTools.CompRoute

/-!
# `wasm-tools`: a Lean drop-in for bytecodealliance/wasm-tools 1.262.0

The main entry of the full build: **`WasmTools.specMain run`**, the program
`(WasmTools.toolAt w).main` behind the specification of upstream's command line,
`Silmaril.Cli.Spec.WasmTools.tool` (`WasmTools.SpecMain`): help, versions, `help NAME…`, missing
subcommands and every usage error are the specification's texts, byte-identical to upstream's
(`tools/cli-spec/tests/wasm-tools-surface.sh`); a command line that runs reaches `run`, which
dispatches on the subcommand path of the matches to the body of the subcommand, each reading
its arguments from the matches in one place (`WasmTools.SpecCore.byPath`,
`WasmTools.Component.byPath`, `WasmTools.GenTrack.byPath`). A path of upstream that no group
implements (`wit-dylib`, `component link`) reports `not implemented in this build` (exit 1).

The core build (`WasmToolsCore.lean`, the first release's binary) runs the same core bodies
behind their own readers (`WasmTools.run`). The status of every subcommand, its theorems and
its tests are in `tools/wasm-tools/README.md`.
-/

namespace WasmTools

/-- **The subcommands of the full build** on the specification's matches. -/
def runFull (_hidden _argv : List String) (m : Silmaril.Cli.Matches) : IO UInt32 :=
  match SpecCore.byPath m <|> Component.byPath m <|> GenTrack.byPath m with
  | some act => act
  | none => notImplemented m.path

end WasmTools

def main (args : List String) : IO UInt32 := do
  -- component inputs of the core groups' `print` and `parse` (`WasmTools.CompHook`)
  WasmTools.CompRoute.install
  WasmTools.specMain WasmTools.runFull args
