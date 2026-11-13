import WasmTools.GenSmith
import WasmTools.GenMutate
import WasmTools.GenShrink
import WasmTools.GenWitSmith

/-!
# The gentool track's subcommands

The generator subcommands (`smith`, `mutate`, `shrink`, `wit-smith`) by their path in the
specification `Silmaril.Cli.Spec.WasmTools.tool`, for the dispatch of `tools/wasm-tools/WasmTools.lean`
and of `wasm-tools-gen`: each runs on the specification's matches and returns the exit status.
-/

namespace WasmTools.GenTrack

/-- The subcommands, by their path in the specification, on its matches (`none`: another
group's). -/
def byPath (m : Silmaril.Cli.Matches) : Option (IO UInt32) :=
  match m.path with
  | ["smith"] => some (WasmTools.GenSmith.run m)
  | ["mutate"] => some (WasmTools.GenMutate.run m)
  | ["shrink"] => some (WasmTools.GenShrink.run m)
  | ["wit-smith"] => some (WasmTools.GenWitSmith.run m)
  | _ => none

end WasmTools.GenTrack
