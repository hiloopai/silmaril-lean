import WasmTools.Component.Cmds
import WasmTools.Component.ComposeCmd
import WasmTools.SpecMain

/-!
# `wasm-tools` subcommands: the Component group

The bodies of `component new`, `wit`, `embed`, `targets`, `unbundle`, `semver-check`
(docs/projects/wasm-components.md) and of `compose` (deprecated upstream, mapped to `wasm-wac`), by their
path in the specification `Silmaril.Cli.Spec.WasmTools.tool`. The command line is the
specification's (`WasmTools.specMain`): help, the group help, `help NAME…` and every usage error
are its texts; a body receives the record of the arguments the specification read
(`WasmTools.Component.Opts`: `NewArgs.ofMatches`, …).
`component link` is not implemented (`notImplemented`).

The compval track's `validate`, `print` and `parse` on components (`WasmTools.CompVal`) are
reached from the core groups' bodies, which hand component inputs over after reading the input
(`WasmTools.CompHook`).
-/

namespace WasmTools.Component

open Silmaril.Wasm.Tools.Component

/-- The bodies of the group on the specification's matches, by path: each reads its record. -/
def bodyAt (m : Silmaril.Cli.Matches) : List String → Option (M Unit)
  | ["component", "new"] => some (newBody (NewArgs.ofMatches m))
  | ["component", "wit"] => some (witBody (WitArgs.ofMatches m))
  | ["component", "embed"] => some (embedBody (EmbedArgs.ofMatches m))
  | ["component", "targets"] => some (targetsBody (TargetsArgs.ofMatches m))
  | ["component", "unbundle"] => some (unbundleBody (UnbundleArgs.ofMatches m))
  | ["component", "semver-check"] => some (semverBody (SemverArgs.ofMatches m))
  | ["compose"] => some (composeBody (ComposeArgs.ofMatches m))
  | _ => none

/-- The subcommands of this group on the specification's matches (`none`: another group's). -/
def byPath (m : Silmaril.Cli.Matches) : Option (IO UInt32) :=
  match bodyAt m m.path with
  | some body => some (runM body)
  | none =>
    if m.path == ["component", "link"] then
      some (notImplemented m.path " (see docs/projects/wasm-components.md)")
    else none

end WasmTools.Component
