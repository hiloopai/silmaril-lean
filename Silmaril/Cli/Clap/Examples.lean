module

public import Silmaril.Cli.Clap.Thms
public meta import Silmaril.Cli.Clap.Defs

/-!
# The clap dialect: an example

The `greet` example of the API guide (`docs/projects/cli.md`): an args grammar,
read with clap's conventions; the help, usage and corpus come from its derived clap view.
Evaluated (`#guard`) and, for the reading, proved by kernel evaluation (`decide +kernel`).
-/

public section

namespace Silmaril.Cli.Clap.Examples

open Silmaril.Cli

/-- An args grammar. -/
def greetCmd : Command where
  name := "greet"
  about := "Print a greeting"
  pos := [{ id := "name" }]
  opts := [{ id := "times", short := ["n"], arg := some .nat, metavar := "N",
             help := "repeat the greeting" },
           { id := "shout", help := "upper case" },
           Opt.optValOr { id := "lang", arg := some (.enum ["en", "fr"]), help := "the language" } "en",
           { helpOpt with help := "Print help" }]

/-- In the clap dialect (`--lang` may be given bare: it then means `en`). -/
def greet : Tool where
  grammar := greetCmd

theorem greetCmd_wf : greetCmd.WF := by decide

/-! The clap view: usage and help are functions of the grammar. -/

#guard greet.surface.root.usage ["greet"] == "Usage: greet [OPTIONS] <NAME>"

#guard greet.surface.root.help ["greet"] ==
  "Print a greeting\n\nUsage: greet [OPTIONS] <NAME>\n\nArguments:\n  <NAME>\n\nOptions:\n" ++
  "  -n, --times <N>      repeat the greeting\n      --shout          upper case\n" ++
  "      --lang[=<LANG>]  the language [possible values: en, fr]\n" ++
  "  -h, --help           Print help\n"

/-! The reading: clap spellings, then the args parser and resolution. -/

theorem read_cluster :
    greet.read (fun _ => none) ["-n2", "--shout", "ada"] =
      .run [{ cmd := "greet", opts := [("times", .val "2"), ("shout", .on)], args := ["ada"] }]
        { values := [("name", [.str "ada"]), ("times", [.nat 2]), ("shout", [.flag]),
            ("lang", []), ("help", [])] } := by
  decide +kernel

theorem read_bare_lang :
    greet.read (fun _ => none) ["--lang", "ada"] =
      .run [{ cmd := "greet", opts := [("lang", .on)], args := ["ada"] }]
        { values := [("name", [.str "ada"]), ("times", []), ("shout", []),
            ("lang", [.str "en"]), ("help", [])] } := by
  decide +kernel

theorem read_type_error :
    (greet.read (fun _ => none) ["-n", "two", "ada"]).exit greet = some 2 := by
  decide +kernel

theorem read_value_like_option :
    (greet.read (fun _ => none) ["-n", "--shout", "ada"]).exit greet = some 2 := by
  decide +kernel

#guard greet.read (fun _ => none) ["-n", "--shout", "ada"] ==
  .error "a value is required for '--times <N>' but none was supplied"

theorem read_help : greet.read (fun _ => none) ["-h", "--bogus"] = .help ["greet"] := by
  decide +kernel

theorem read_dashdash :
    greet.read (fun _ => none) ["--", "--shout"] =
      .run [{ cmd := "greet", args := ["--shout"] }]
        { values := [("name", [.str "--shout"]), ("times", []), ("shout", []), ("lang", []),
            ("help", [])] } := by
  decide +kernel

/-! The reference reading of the clap view agrees on the derived corpus, except where the
grammar's value types say more (`-n 1` is fine, but the corpus has no non-number for `-n`). -/

#guard disagreements greet == []

/-! ## The clap reading is the args front end (`read_agrees`)

Beyond normal forms: a cluster with an attached value, an optional value given bare. -/

theorem greet_helpFlags : HelpFlags greetCmd := by decide

theorem agrees_cluster :
    (greet.read (fun _ => none) ["-n2", "--lang", "ada"]).Agrees
      (interpret greetCmd (fun _ => none) ["-n2", "--lang", "ada"]) :=
  read_agrees greet _ greet_helpFlags (by decide +kernel)

/-- The args front end reads the bare `--lang` as its missing value, as clap does. -/
theorem interpret_bare_lang :
    interpret greetCmd (fun _ => none) ["--lang", "ada"] =
      .run { values := [("name", [.str "ada"]), ("times", []), ("shout", []),
        ("lang", [.str "en"]), ("help", [])] } := by
  decide +kernel

/-! ## Rules and checks live in the grammar; the args front end enforces them -/

/-- `--shout` and `--lang` exclude each other; `name` is `ada` or `bob` (a `ValueCheck`). -/
def strictCmd : Command :=
  (greetCmd.withRules [([], .conflicts "shout" "lang")]).withChecks
    [("name", .oneOf ["ada", "bob"])]

#guard interpret strictCmd (fun _ => none) ["--shout", "--lang=fr", "ada"] ==
  .error ["greet"] (.conflicts "shout" "lang")
#guard interpret strictCmd (fun _ => none) ["eve"] == .error ["greet"] (.rejected "name" "eve")
#guard (interpret strictCmd (fun _ => none) ["--shout", "bob"]).exitCode? == none

/-! ## Exact tokens and grammar morphisms

Adding an exact token `-O2` keeps every command line's reading (`extends_addFresh`: `O` is no
cluster letter of `greet`); `-n2` would not be fresh, and indeed it changes the meaning of the
cluster `-n2` (the option `-n` with the value `2`). -/

/-- An exact token. -/
def o2 : Opt := { id := "O2", long := [], short := ["O2"], exact := true }

theorem greet_o2 : greetCmd ⊑ greetCmd.addOpt o2 := extends_addFresh _ (by decide)

theorem n2_not_fresh :
    ¬ ({ o2 with id := "n2", short := ["n2"] } : Opt).FreshIn greetCmd.allOpts := by decide

#guard (match scan greetCmd ["-n2", "ada"] with
  | .ok fs => fs == [{ cmd := "greet", opts := [("times", .val "2")], args := ["ada"] }]
  | .error _ => false)
#guard (match scan (greetCmd.addOpt { o2 with id := "n2", short := ["n2"] }) ["-n2", "ada"] with
  | .ok fs => fs == [{ cmd := "greet", opts := [("n2", .on)], args := ["ada"] }]
  | .error _ => false)

end Silmaril.Cli.Clap.Examples
