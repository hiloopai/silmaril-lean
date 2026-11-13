import Silmaril.Cli.Spec.WasmTools.Defs

/-!
# What the subcommands read from the specification's matches

The matches of `Silmaril.Cli.Spec.WasmTools.tool` (`Silmaril.Cli.Matches`: the subcommand path and the
values of every option and positional by `id`, defaults included) in the shapes the subcommand
bodies of `wasm-tools` take. Each subcommand has one `…ofMatches` (here for the generic part,
next to the body for the others); nothing else knows option ids.

* `occs m`: the option values (`id`, the value; `none` for a flag occurrence), every occurrence
  of one `id` in command-line order;
* `positionals m`: the positional words, in the order of the command's positionals.

Values the specification's defaults supply (`--color auto`, `mutate --seed 42`, …) are in the
matches as if given: they are upstream's defaults (clap's `default_value`), which the bodies
also apply when a value is absent.
-/

namespace WasmTools.SpecArgs

open Silmaril.Cli

/-- The command of the specification at a path below the root. -/
def cmdAt (path : List String) : Option Command :=
  Silmaril.Cli.Spec.WasmTools.grammar.walk path

/-- The `id`s of the positionals of the command at `path`, in order. -/
def posIds (path : List String) : List String :=
  ((cmdAt path).map fun c => c.pos.map (·.id)).getD []

/-- A value as the word it was read from (`none` for a flag occurrence). -/
def valueStr : Value → Option String
  | .str s => some s
  | .nat n => some (toString n)
  | .int i => some (toString i)
  | .flag | .off => none

/-- The option occurrences of the matches: `id` and value, by `id`, each `id`'s occurrences in
order. -/
def occs (m : Matches) : List (String × Option String) :=
  let ps := posIds m.path
  m.values.flatMap fun (id, vs) =>
    if ps.contains id then [] else vs.map fun v => (id, valueStr v)

/-- The positional words of the matches, in the order of the command's positionals. -/
def positionals (m : Matches) : List String :=
  (posIds m.path).flatMap fun id => (m.get id).filterMap valueStr

/-- `occs` with the `id`s renamed (the keys a body reads). -/
def occsAs (key : String → String) (m : Matches) : List (String × Option String) :=
  (occs m).map fun (k, v) => (key k, v)

end WasmTools.SpecArgs
