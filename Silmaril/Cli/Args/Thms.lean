module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Proofs.Cli.Args.Scan
public import Silmaril.Proofs.Cli.Args.Morph
public import Silmaril.Proofs.Cli.Args.Help
public import Silmaril.Proofs.Cli.Args.Resolve
public import Silmaril.Proofs.Cli.Args.Values
public import Silmaril.Proofs.Cli.Args.Complete

/-!
# Argument grammars: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Cli.Args.*`, namespace `Silmaril.Cli`), for every
grammar `c : Command`:

**The parser is the grammar** (`Scan`):

* `scanAux_sound`, `scanAux_complete`, `scanAux_eq_ok_iff`: `scanAux c argv = .ok r ↔
  Scans c argv r`, where `Scans` has one rule per convention (no well-formedness needed);
  `scan_eq_ok_iff` for `scan`; `Scans.deterministic`;
* `findLong_eq_some_iff`, `findShort_eq_some_iff`, `findSub_eq_some_iff`: in a well-formed
  grammar (`c.WF`, decidable; `Command.WF.good` gives `Good`, well-formedness of the tree the
  parser sees, inherited options included) a name finds exactly the option or subcommand that
  declares it;
* `readOpt_mem`, `scan_valid`: what a grammar parses is `Valid`; `scan_error_walk`: errors are
  located at a subcommand path of the grammar;
* the spellings of the normal form read back: `readOpt_on` (flags, `--name` of an optional
  value), `readOpt_val` (a value in the next token), `readOpt_valEq` (`--name=V`),
  `readOpt_off` (`--no-name`);
* **round trip** `scan_render`: `scan c (render c fs) = .ok fs` for every valid invocation;
  `scan_render_scan` (parse, render, parse) and `normalize_idem` (the normal form is stable).

**Grammar morphisms** (`Morph`): `Extends` (`c ⊑ c'`) is a preorder (`Extends.refl`,
`Extends.trans`); `readOpt_append_fresh`: appending options fresh in the table (`Opt.FreshIn`:
long names not `no-…`; single-dash names of one letter, or exact tokens such as `-O2` whose
first letter is no cluster letter of the table) keeps every reading of an option token
(clusters, attached values and `--no-` included), `readOpt_append` for `Plain` options;
`walk_allOpts` (every level's options are declared in the grammar, `Command.allOpts`);
`extends_appendFresh`, `extends_addFresh` (fresh in `c.allOpts`, decidable),
`extends_appendOpts`, `extends_addOpt`,
`extends_withHelp`, `extends_withGlobal` (global options reach every level below),
`extends_withVersion`, `extends_addSub` (when the command already has subcommands) are
morphisms; **compatibility** `scans_extends`, `scanAux_extends`, `scan_extends`: along a
morphism every command line keeps its parse.

**Help and outcome** (`Help`): `helpLines_opt`, `helpLines_pos`, `helpLines_sub`,
`helpLines_exit`, `helpLines_usage` (every declared item has a help line), `synopsis_long`,
`synopsis_short`, `synopsis_no` (every name shown parses as its option), `interpret_scan_error`
(exit 2, stderr), `scan_errorText` (**per-subcommand usage** in error messages),
`interpret_help`, `interpret_version` (exit 0).

**Resolution** (`Resolve`): `resolveOpt_cmdline`, `resolveOpt_env`, `resolveOpt_default`,
`resolveOpt_absent` (command line, else environment, else default, else required error or no
value), `resolveOpt_flag`, `count_flag` (counted flags); `Matches.Equiv`, `ResolvesLike`
(a preorder, monotone in the invocations considered); **compatibility of resolution along
extensions at any depth**: `resolve_addOpt`, `resolvesLike_addOpt` (a fresh option, local or
global, at any level), `resolvesLike_addSub` (a subcommand), and the congruence
`resolvesLike_subs`; `noId_of_valid` (a parsed invocation mentions only declared identifiers).

**Values and positionals** (`Values`): `parseNat_toString`, `parseInt_toString`,
**`parse_show`** (every value of every `ArgType` parses back from `Value.show`), `parse_has`;
`Binds` (one rule per arity) and **`bindPos_eq_ok_iff`**: positional binding is sound and
complete for every arity and type.

The front end as a behaviour specification (`Command.spec`, `Command.main` refines it) is in
`Silmaril.Cli.Front`.
-/
