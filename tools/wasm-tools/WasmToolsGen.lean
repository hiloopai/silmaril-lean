import WasmTools.SpecMain
import WasmTools.GenTrack

/-!
# `wasm-tools-gen`: the generator subcommands as a standalone binary

`wasm-tools-gen SUBCOMMAND ARGS…` is `wasm-tools SUBCOMMAND ARGS…` for `smith`, `mutate`,
`shrink` and `wit-smith` (`WasmTools.GenTrack.byPath`), behind the same specification of the
command line (`WasmTools.specMain`); other subcommands are not in this build. The tests in
`tools/wasm-tools/tests/gen` run it.
-/

def main (args : List String) : IO UInt32 :=
  WasmTools.specMain (fun _ _ m => (WasmTools.GenTrack.byPath m).getD
    (WasmTools.notImplemented m.path)) args
