# Command-line interfaces as specifications

The `Cli` region specifies command-line programs and proves programs against those
specifications. A command line is described once, as data; everything a user sees of the front
end (parsing, help, usage errors, exit codes, the normal form of a command line) is computed
from that description, and is proved to agree with it. What the program then does is a
relation between invocations and observations, with refinement and composition. Programs
written in Lean are proved to refine such relations, and a test harness checks other binaries
against the same relations with decidable checks that are proved sound.

Everything here is a library of definitions and theorems in Lean. Every theorem is proved, and
uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

## Four layers

A CLI is specified in four layers, each a function of the one before.

| Layer | Modules | Key names |
| --- | --- | --- |
| 1. The grammar is data | `Silmaril.Cli.Args`, `Silmaril.Cli.Clap`, `Silmaril.Cli.Getopt`, `Silmaril.Cli.Surface` | `Command`, `Opt`, `Pos`, `flag`, `opt`, `arg`, `Command.WF`, `Extends` (`⊑`), `Clap.Tool`, `Getopt.Tool` |
| 2. The front end is derived | `Silmaril.Cli.Args`, `Silmaril.Cli.Front`, `Silmaril.Cli.Clap.Main` | `scan`, `interpret`, `Outcome`, `render`, `normalize`, `Command.help`, `Command.spec`, `Command.main` |
| 3. The behaviour is a relation | `Silmaril.Cli.Behaviour`, `Files`, `Footprint`, `Check` | `Input`, `Obs`, `Spec`, `≤`, `seq`, `pipe`, `dispatch`, `Spec.Partial`, `Spec.orFail`, `Spec.orRefused`, `Check` |
| 4. Implementations refine the spec | `Silmaril.Cli.Io`, `Silmaril.Cli.Io.Command`, `Silmaril.Cli.Io.Run` | `Prog`, `Prog.Sat`, `Prog.ofCommandCore`, `Prog.toIO`, `Check.Sound`, `checkCases` |

1. **Grammars.** `Command`, `Opt` and `Pos` are structures with defaults. The builders
   (`flag`, `opt`, `arg`) and modifiers (`.withDefault`, `.withEnv`, `.req`, `.many`,
   `.counted`, `.optVal`, `.withNo`, `.inherited`, `.tokens`) cover the usual conventions:
   long and short names, short clusters, attached values, optional values, negatable flags,
   counted flags, exact tokens such as `-O2`, typed values, environment variables, defaults,
   subcommands and global options. `withHelp` and `withVersion` add the conventional flags.
   Well-formedness `c.WF` is decidable. The clap dialect (`Clap.Tool`) reads the same grammar
   with the conventions of Rust's clap, the getopt dialect (`Getopt.Tool`) with those of C's
   `getopt` and `getopt_long`, and `Surface` renders clap's `-h` layout.
2. **The derived front end.** `interpret c env argv` parses (`scan`), resolves each value
   (command line, then environment, then default) and gives an `Outcome`: `.run m` with typed
   `Matches`, `.help path`, `.version v` or `.error path e`, with its exit code. The parser is
   sound and complete for every grammar, the normal form printed by `render` reads back, and
   the help text lists every declared item. `Command.spec c body` is the front end as a
   behaviour specification: exactly the derived text and exit code on help, version and usage
   errors, and `body m` when the arguments resolve to `m`.
3. **Behaviour.** `Spec := Input → Obs → Prop`. An `Input` is what a command-line program is
   given: program name, arguments, environment, stdin, and declared roots (preopened
   directories) with their files. An `Obs` is what can be seen of a terminating run: stdout,
   stderr, exit code, the stdin bytes consumed, the files read, the files after the run, a log
   of file events, and whether the environment refused something. Specs form a complete lattice:
   `S ≤ T` is refinement. Specs compose sequentially (`seq`, `andThen`, `orElse`), through
   pipes (`pipe`, `pipeSeq`) and by subcommand (`case`, `dispatch`), and every composition is
   monotone, so refinement is a congruence. `Files` gives the common shape of a file
   transformer, `Footprint` the conditions under which a pipe behaves as its sequential
   schedule, and `Check` the decidable checks of recorded runs.
4. **Implementations.** `Prog` is a free monad over the CLI effects (arguments, environment,
   stdin, stdout and stderr writes, whole-file reads and writes, exit). `Prog.exec` reads a
   program in the behaviour model, so `Prog.Sat p S` is refinement; `Prog.ofCommandCore c core`
   puts a pure core behind the derived front end, and `sat_ofCommandCore_iff` reduces the whole
   program to the core. `Prog.toIO` and `Prog.main` run a program with Lean's `IO`.
   `runBinary` and `checkCases` run any binary on test cases in a fresh directory and apply a
   `Check`; `Check.Sound` says a passing run is one the spec allows.

Components compiled to WebAssembly and run under WASI (`wasi:cli/command`) are the next kind
of implementation: the model is built for them (an invocation is what `wasi:cli` gives a
component, an observation what it can do), and their bridges will be published with the
WebAssembly tools.

## The CLI institution

`Silmaril.Cli.Institution` makes the behaviour model an institution, in the sense of
`Silmaril.Logic.Institution` (it is built as a functor into `Room`, with its classic
presentation `classic`):

* a **signature** (`Sig`) is an interface: the inputs `In` and the observations `Out`;
* a **sentence** (`Sen A`) is a specification `In → Out → Prop`;
* a **model** (`Model A`) is a program semantics: the observations of its terminating runs;
* **satisfaction** `M.Sat φ` is partial correctness, `M.Run ≤ φ`;
* a **morphism** `A ⟶ B` relates inputs of `B` to inputs of `A` and projects observations of
  `B` to `A`; sentences translate forwards, models reduce backwards, and the satisfaction
  condition holds (`Hom.sat_sen_iff`).

The standard interfaces form a chain of **observation levels**:

| Level | Input | Observation |
| --- | --- | --- |
| `L0` (`status`) | nothing | the exit code |
| `L1` (`stream`) | stdin | stdout and exit code |
| `L2` (`command`) | program name, arguments, stdin | stdout, stderr, exit code |
| `L3` (`full`) | `Silmaril.Cli.Input` | `Silmaril.Cli.Obs` |

`Level.lift φ` states a sentence of a lower level as a full `Spec`, by default expansion of the
input (`Level.hom`); `Level.liftAll φ` states it for every extension (`Level.homAll`).
`sat_lift_iff`: a full model satisfies the lift iff its reduct at the level satisfies the
sentence. The standard sentences are `Sen.exits`, `Sen.filter`, `Sen.prints`, `Sen.command`
and `Sen.judge`, with named instances in `Silmaril.Cli.Institution.Std` (`hello`, `cat`,
`sha256Stdin`) and judged stdin-to-stdout problems (`Problem`).
`Silmaril.Cli.Spec.Sha256sum` states GNU `sha256sum` at levels `L1`, `L2` and `L3` from the
reference behaviour `Silmaril.Apps.Sha256sum.sha256sum`, and relates the levels.

## Relation to `Silmaril.Process.CLI`

`Silmaril.Process.CLI` specifies Linux processes at the level of system calls: a `CliSpec` is a
pair of predicates on the event lists of runs and on finished runs with their exit status, and
`Agrees`, `Covered`, `Halts` and `Bounded` are statements about a binary image at a machine
model. `Silmaril.Cli` specifies command-line programs at the level of what a user sees, independently
of any machine or implementation language. The two are meant to meet: a behaviour specification
`S` translates to a process specification whose prefixes are partial views of runs `S` allows and
whose finished runs `S` allows, on the process inputs that represent an invocation, and
refinement of behaviour specifications is refinement of process specifications. That
translation, and a common observation type for both, are left to a later release; nothing here
depends on `Silmaril.Process`.

## Example

The guide below is compiled: `Silmaril/Cli/Guide/{Defs,Thms}.lean`, namespace `Silmaril.Cli.Guide`,
with `open Silmaril.Cli Silmaril.Cli.Io`. Every `#guard` is evaluated and every theorem is proved.

**The grammar is data.**

```lean
def greetCmd : Command :=
  Command.withVersion (Command.withHelp
    { name := "greet", about := "Greet someone",
      opts := [flag "shout" ["s"] "Print in capitals",
               ((opt "greeting" (help := "The greeting")).withDefault "hello").withEnv "GREETING"],
      pos := [arg "name" (help := "Who to greet")],
      exits := [(0, "success"), (2, "usage error")] }) "1.0.0"

theorem greetCmd_wf : greetCmd.WF := by decide
```

**The front end is derived.**

```lean
#guard match interpret greetCmd (fun _ => none) ["-s", "ada"] with
  | .run m => m.flag "shout" && m.str? "greeting" == some "hello" && m.strs "name" == ["ada"]
  | _ => false
#guard (interpret greetCmd (fun _ => none) ["--bogus", "ada"]).exitCode? == some 2
#guard normalize greetCmd ["-s", "--greeting=hey", "ada"] ==
  .ok ["--shout", "--greeting", "hey", "ada"]
#guard greetCmd.help ["greet"] == "\n".intercalate [
  "Greet someone", "", "Usage: greet [OPTIONS] <NAME>", "", "Arguments:",
  "  <NAME>  Who to greet", "", "Options:",
  "  -s, --shout         Print in capitals",
  "  --greeting <VALUE>  The greeting [default: hello] [env: GREETING]",
  "  -h, --help          Print help", "  -V, --version       Print version", "",
  "Exit status:", "  0  success", "  2  usage error"]
```

**The behaviour is a relation**, built from the same grammar: on help, version and usage errors
exactly the derived text and exit code; otherwise print the line, read nothing, change no file,
exit 0.

```lean
def greetLine (m : Matches) : Bytes :=
  let s := (m.str? "greeting").getD "hello" ++ ", " ++ " ".intercalate (m.strs "name") ++ "\n"
  utf8 (if m.flag "shout" then s.toUpper else s)

def greetSpec : Spec := greetCmd.spec fun m => Spec.pure fun _ => { stdout := greetLine m }
```

**A Lean program refines it, and a harness check is sound for it.**

```lean
def greetProg : Prog ExitCode := Prog.ofCommandCore greetCmd fun m _ => { stdout := greetLine m }
theorem greet_sat : greetProg.Sat greetSpec

def greetCheck : Check := greetCmd.check fun m _ s =>
  s.exit == 0 && s.stdout == greetLine m && s.stderr.isEmpty && s.files.isEmpty
theorem greetCheck_sound : greetCheck.Sound greetSpec
```

**Growing the CLI** is a grammar morphism `c ⊑ c'`: every old command line parses the same.

```lean
def quiet : Opt := flag "quiet" ["q"] "Print nothing"
theorem greet_quiet : greetCmd ⊑ greetCmd.addOpt quiet := extends_addOpt _ (by decide)
theorem greet_quiet_scan (h : scan greetCmd argv = .ok fs) :
    scan (greetCmd.addOpt quiet) argv = .ok fs := scan_extends greet_quiet h
```

More examples: `Silmaril.Cli.Io.Echon` (a grammar with an environment default, its program, spec
and check), `Silmaril.Cli.Io.Examples` (`echo`, `cat` and a file copy, the latter with
`Spec.orRefused`), `Silmaril.Cli.Clap.Examples` (the clap dialect),
`Silmaril.Cli.Behaviour.Examples` (pipes, `&&` and dispatch) and `Silmaril.Cli.Footprint.Examples`
(a pipe whose log is not the sequential one).

## The getopt dialect

Most C programs, and so most ELF binaries one verifies, read their arguments with POSIX
`getopt(3)` or GNU `getopt_long(3)`. `Silmaril.Cli.Getopt` models both, and relates them to
args grammars the way the clap dialect does.

**Tables as data.** A `Getopt.Table` is what a C program hands to the library: the optstring
(`shorts`: a character with no argument, `x:` a required one, `x::` an optional one; a leading
`+`; GNU's `W;`) and the longopts array (`longs`: a name, its argument, the key it reports).
`Table.ofOptstring "+n:c:qv"` reads an optstring and `Table.optstring` prints one;
`Table.ofCommand c` derives the table from an args `Command` (one-letter single-dash names
become optstring characters, long names become longopts entries, keyed by option `id`).

**The reading.** `parse t ord argv` follows getopt's conventions: clusters `-abc`; a required
argument attached (`-n5`) or in the next token, taken verbatim even when it starts with `-`
(`-n -5`); an optional argument only attached (`-n5`, `--name=v`); `--name`, `--name=v`,
`--name v`; any unambiguous prefix of a long name (`resolveLong`: an exact name wins, and
prefixes of several names that mean one option, like GNU grep's `--color` and `--colour`, are
not ambiguous); `-W name` as `--name` with `W;`; `--` ends the options; `-` is an operand
(standard input by convention). The first usage error ends the reading, as in programs that
print their usage and exit 2.

**Ordering depends on the environment.** POSIX getopt stops at the first operand
(`Order.requireOrder`). GNU getopt permutes (`Order.permute`): options may follow operands,
unless the optstring starts with `+` or `POSIXLY_CORRECT` is set. So a `Getopt.Tool` (a grammar
plus `gnu`, `plus`, `wLong`) is read as a function of the arguments **and** the environment:
`Tool.order env`, `Tool.parse env argv`, `Tool.read env argv`. On a full invocation
(`Silmaril.Cli.Getopt.Front`) `Tool.envVars` lists the variables read (`POSIXLY_CORRECT`, then
the grammar's), `Tool.outcome i` reads them from `i : Input`, and `Tool.spec S` is the
behaviour specification, as `Command.spec` is for the args dialect.

```lean
open Silmaril.Cli Silmaril.Cli.Getopt

def head : Tool := { grammar := {
  name := "head"
  opts := [{ id := "lines", long := ["lines"], short := ["n"], arg := some .str }]
  pos := [{ id := "file", arity := .many }] } }

#guard head.table.optstring == "n:"
-- GNU order: `-n 3` after a file is still an option.
#guard ((head.parse (fun _ => none) ["a", "-n", "3"]).toOption.map (·.operands)) == some ["a"]
-- With POSIXLY_CORRECT set, `-n` and `3` are files.
#guard ((head.parse (fun v => if v == "POSIXLY_CORRECT" then some "" else none)
    ["a", "-n", "3"]).toOption.map (·.operands)) == some ["a", "-n", "3"]
```

**Against the args front end.** `Tool.read` hands what getopt read to the same checks as
`interpret` (`afterScan`: help, version, types, defaults, environment variables, positionals,
value checks, rules). The pre-pass `Tool.pre env argv` names the first token where the two
readings may differ (`Diverge`): an abbreviated long name, `-W`, an attached argument starting
with `=` (`sort -t=` gives getopt the separator `=`; the args dialect reads `-t=x` as `x`), and,
in POSIX order, an option-like token after the first operand. Where it passes, `read_agrees`
proves that the getopt reading and `interpret` agree. `parse_permuted` proves that the GNU
reading of an argument vector is the POSIX reading of its permuted vector (option tokens first,
as glibc leaves `argv`).

`Silmaril.Cli.Getopt.Examples` checks option tables of `head`, `wc`, `grep`, `sort` and `cut`
against the behaviour POSIX and GNU document for them: clusters (`wc -lwc`), attached and
separate arguments (`cut -d, -f1,3`, `cut -f 2 -d ' '`), arguments that start with `-`
(`grep -e -v`), optional arguments (`grep --color` versus `--color=always`), unique and
ambiguous prefixes (`--col`, `--in`), `--`, `-`, and the two orderings.

## Known limitations

* **Partial correctness.** `Obs` describes terminating runs only; a spec says nothing about runs
  that do not end, and `⊥` refines everything. `Total S` states that a spec allows some
  observation on every input. The institution's satisfaction is partial correctness too.
* **Normal form.** The round trip holds modulo the normal form printed by `render`: first long
  names, values as separate tokens, options before positionals.
* **Two front ends.** `Clap.Tool.read` puts clap's pre-pass in front of the derived parser.
  Where the pre-pass stops early (help before a bad option, a value that looks like an option,
  no `--no-x` negation) the two readings can differ by design; `read_agrees` assumes the
  pre-pass passes, and compares outcome classes, not message texts. The clap help layout of
  `Surface` and the comparison of its reference reading with `Clap.Tool.read` are checked by
  evaluation, not proved.
* **getopt.** The model ends at the first usage error (getopt reports it and goes on; programs
  conventionally exit). GNU's third ordering (an optstring starting with `-`), `getopt_long_only`
  and the obsolete `head -5` style (parsed by programs before getopt) are not modelled; `-W name`
  takes an argument only as `-W name=value`. `read_agrees` needs a grammar getopt can express
  (`Fits`: no subcommands, no exact multi-letter tokens, no `--no-x` negation) and compares
  outcome classes, not message texts. That the pre-pass passes the args normal form is still
  open (`Task.pre_render`; `read_render_of` is conditional on it).
* **Program bodies.** `Command.main` and `Clap.Tool.main` are proved to refine their front-end
  specifications given that the program run on each `Matches` refines its part
  (`main_refines`); what the body does is the user's obligation.
* **Failures.** Under `Spec.orFail` stderr is unconstrained, and stdin consumption and the files
  read are lower bounds in partial observations.
* **Pipes.** `pipe S T ≤ relog (pipeSeq S T)` needs framed specs with separate footprints; the
  file transformer `Files.transform` is not yet proved framed. The plain `pipe ≤ pipeSeq` is
  false (`not_pipe_le_pipeSeq`).
* **Trusted `IO` reading.** `Prog.toIO`, `Command.main` and `Clap.Tool.main` run with Lean's
  `IO`; that `IO` performs each operation as the model reads it is trusted, as for every `IO`
  program. The harness cannot choose `argv[0]`, so a check used with it must not depend on the
  program name.

## Theorem index

All theorems below are proved from the standard axioms only.

**Grammars and the derived front end** (`Silmaril.Cli.Args.Thms`, proofs in
`Silmaril/Proofs/Cli/Args/`):

* the parser is the grammar: `scanAux_eq_ok_iff`, `scan_eq_ok_iff` (sound and complete
  against the rule system `Scans`), `Scans.deterministic`; `findLong_eq_some_iff`,
  `findShort_eq_some_iff`, `findSub_eq_some_iff` in well-formed grammars; `scan_valid`;
* round trip: `scan_render`, `scan_render_scan`, `normalize_idem`;
* grammar morphisms: `Extends.refl`, `Extends.trans`, `extends_addOpt`, `extends_addFresh`,
  `extends_appendOpts`, `extends_withHelp`, `extends_withGlobal`, `extends_withVersion`,
  `extends_addSub`; compatibility `scan_extends`; resolution along extensions
  `resolvesLike_addOpt`, `resolvesLike_addSub`, `resolvesLike_subs`;
* help and outcomes: `helpLines_opt`, `helpLines_pos`, `helpLines_sub`, `helpLines_exit`,
  `synopsis_long`, `synopsis_short`, `synopsis_no`, `interpret_scan_error`, `scan_errorText`,
  `interpret_help`, `interpret_version`;
* resolution: `resolveOpt_cmdline`, `resolveOpt_env`, `resolveOpt_default`,
  `resolveOpt_absent`; values: `parse_show`, `bindPos_eq_ok_iff`.

**The front end as a spec** (`Silmaril.Cli.Front.Thms`): `main_refines`, `spec_eq_modelMain`,
`spec_usageError`, `spec_of_help`, `spec_of_version`, `spec_of_error`, `spec_of_run`.

**The clap dialect** (`Silmaril.Cli.Clap.Thms`, `Silmaril.Cli.Clap.Main.Thms`): `read_agrees`,
`pre_render`, `read_render`, `read_run_valid`, `read_run_render`; `Tool.main_refines`,
`Tool.main_refines_front`, `Tool.frontCheck_sound`, `Tool.spec_usageError`, `Tool.helpOr_help`.

**The getopt dialect** (`Silmaril.Cli.Getopt.Thms`, `Getopt.Front.Thms`, proofs in
`Silmaril/Proofs/Cli/Getopt/`): `read_agrees`, `parse_scan`, `readTok_readOpt`;
`parse_permuted`, `Tool.parse_permuted`; `resolveLong_exact`, `resolveLong_ok`,
`resolveLong_unique`; `order_posixly`, `order_plus`, `order_posix`, `order_gnu`, `order_envOf`;
`outcome_agrees`, `spec_run`, `spec_usage`; `read_render_of` takes the open
`Task.pre_render` as a hypothesis.

**Behaviour** (`Silmaril.Cli.Behaviour.Thms`, `Files.Thms`, `Footprint.Thms`, `Check.Thms`):
`det_le_iff`; monotonicity of every composition (`seq_mono`, `pipe_mono`, `dispatch_mono`, …);
`seq_assoc`, `pipeO_assoc`, `pipeline_assoc`, `pipeSeq_assoc`, `pipeSeq_le_pipe`;
`case_unique`, `dispatch_cons_of_ne`, `dispatch_cons_self`; `orRefused_inf_reliable`,
`orFail_orFail`; `partial_seen`, `Partial.ended`; `transform_le_confined`, `pipe_filter`;
`Fs.replay_interleave`, `pipe_le_pipeSeq`, `relog_pipe_eq`, `pipe_le_of_pipeSeq`;
`Check.decides_prints`, `Decides.orFail`, `Decides.orRefused`.

**Lean programs and the harness** (`Silmaril.Cli.Io.Thms`, `Io.Command.Thms`, `Io.Surface.Thms`):
`sat_ofCore_iff`, `sat_ofTool_iff`, `Prog.sat_iff_det_le`, `Prog.Sat.mono`;
`obs_ofCommand`, `sat_ofCommand_iff`, `sat_ofCommandCore_iff`, `Command.spec_mono`,
`Command.check_sound`; `Tool.check_sound`.

**The institution** (`Silmaril.Cli.Institution.Thms`, `Std.Thms`): `Hom.sat_sen_iff`, the
functor `inst` and `classic`; `hom_comp`, `toSig`, `sat_lift_iff`, `sat_liftAll_iff`,
`liftAll_le_lift`, `lift_hom`, `lift_filter_iff`, `lift_prints_iff`; `Model.Sat.mono`,
`Model.Sat.anti`; `Sen.filter_agree` and its instances.

**sha256sum** (`Silmaril.Cli.Spec.Sha256sum.Thms`): `spec_anti`, `spec_le_lift_stdin`,
`spec_le_lift_cmd`, `spec_le_lift_cmdOn`.

**Examples** (`Silmaril.Cli.Guide.Thms`, `Io.Examples.Thms`, `Io.Check.Thms`, `Io.Echon.Thms`):
`greet_sat`, `greetCheck_sound`, `greet_quiet_scan`; `echo_sat`, `cat_sat`, `copy_sat`;
`echoCheck_sound`, `catCheck_sound`, `copyCheck_sound`; `echon_sat`, `echonCheck_sound`.

## Building

```sh
lake build Silmaril.Cli
```

builds the region root and every module above.
