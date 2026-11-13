module

public import Silmaril.Cli.Info.Defs
public import Silmaril.Cli.Front.Thms
public import Silmaril.Proofs.Cli.Info.Basic
public import Silmaril.Proofs.Cli.Info.Args
public import Silmaril.Proofs.Cli.Info.Clap

/-!
# Standard problems `--help` and `--version`: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Cli.Info.*`, namespace
`Silmaril.Cli.Info`):

**The lattice** (`Basic`): `HelpVariant.Le` (stricter than) is reflexive and transitive
(`Le.refl`, `Le.trans`), and a stricter variant's sentences imply the looser one's
(`HelpVariant.sen2_mono`, `HelpVariant.sen_mono`; `VersionVariant.sen2_mono`,
`VersionVariant.sen_mono`). Below: the named variants, in order.

**Levels and models** (`Basic`): the `L3` sentence implies the `L2` sentence on every extension
of the input (`sen_le_liftAll`), and is its uniform lift without `quiet` (`sen_eq_liftAll`); a
full model meeting it has an `L2` reduct meeting the `L2` sentence (`sat_reduct`). A Lean
program meets a sentence as a model iff as a program (`Io.Prog.model_sat_iff`); a spec read as
a model meets it iff it refines it (`ofSpec_sat_iff`); any model with a morphism from the full
interface meets the translated sentence iff its reduct meets the sentence (`sat_via_iff`).

**Derived front ends** (`Args`, `Clap`): `spec_help`, `spec_version` (args dialect) and
`Clap.spec_help`, `Clap.spec_version` (clap dialect): a front end that answers the requests of a
variant (`Command.helpTriggers`, …), with texts that fit, has a spec refining the variant's
sentence, whatever the program does on its matches; `helpTriggers_of_wf`,
`versionTriggers_of_wf` and `Clap.helpTriggers_everywhere`: grammars built with `withHelp`,
`withVersion` and `helpEverywhere` answer them. The headline forms are restated below.
-/

@[expose] public section

namespace Silmaril.Cli.Info

open Silmaril.Cli Silmaril.Cli.Institution

/-! ## Named variants, strictest first -/

theorem wins_le_basicShort : HelpVariant.wins.Le HelpVariant.basicShort := by decide
theorem either_le_basicShort : HelpVariant.either.Le HelpVariant.basicShort := by decide
theorem basicShort_le_basic : HelpVariant.basicShort.Le HelpVariant.basic := by decide
theorem basic_le_loose : HelpVariant.basic.Le HelpVariant.loose := by decide
/-- Help wins over everything: also over operands, and help or a usage error. -/
theorem wins_le_either : HelpVariant.wins.Le HelpVariant.either := by decide

theorem subcommands_le_basicShort (ps : List (List String)) :
    (HelpVariant.subcommands ps).Le HelpVariant.basicShort :=
  ⟨id, id, id, by simp [HelpVariant.basicShort], .refl _, .refl _, by simp [HelpVariant.basicShort],
    id⟩

theorem version_basicShort_le_basic : VersionVariant.basicShort.Le VersionVariant.basic :=
  ⟨id, fun h => by simp [VersionVariant.basic] at h, .refl _, by simp [VersionVariant.basic], id⟩

theorem version_pinned_le_basic (ver : String) :
    (VersionVariant.pinned ver).Le VersionVariant.basic :=
  ⟨id, id, .refl _, by simp [VersionVariant.basic], id⟩

/-! ## Grammars with the conventional flags (args dialect) -/

/-- The root path, for a variant without subcommand paths. -/
theorem rootOnly {v : HelpVariant} (hv : v.paths = []) (c : Command)
    (hx : v.extra = .winsOperands → c.subs.isEmpty = true) :
    ∀ p ∈ v.roots, ∃ d, c.pathLevel p = some d ∧
      (v.extra = .winsOperands → d.subs.isEmpty = true) := by
  intro p hp
  simp only [HelpVariant.roots, hv, List.mem_singleton] at hp
  subst hp
  exact ⟨c, rfl, hx⟩

/-- **Every well-formed grammar with the conventional help flag meets the help variants the
args dialect can**: the derived front end's spec `c.spec S` refines the sentence of every
variant without required substrings or pinned texts, without a `help` word, with an
extra-argument claim the dialect meets (`argsExtra`: none, help over operands at levels
without subcommands, help or a usage error), at paths its words select. -/
theorem _root_.Silmaril.Cli.Command.spec_le_help {c : Command} (hwf : c.WF)
    (hh : helpOpt ∈ c.opts) {v : HelpVariant} (hm : v.reply.mentions = []) (ht : v.texts = [])
    (hw : v.word = false) (hx : argsExtra v.extra = true)
    (hp : ∀ p ∈ v.roots, ∃ d, c.pathLevel p = some d ∧
      (v.extra = .winsOperands → d.subs.isEmpty = true))
    (S : Matches → Spec) : c.spec S ≤ v.sen :=
  spec_help (helpTriggers_of_wf hwf hh hw hx hp) (fun p _ => HelpVariant.fits_line hm ht p _) S

/-- **Every well-formed grammar with the conventional version flag and a version meets every
version variant** whose substrings are the program name or the version, and whose version is
the grammar's. -/
theorem _root_.Silmaril.Cli.Command.spec_le_version {c : Command} (hwf : c.WF)
    (hv : versionOpt ∈ c.opts) {ver : String} (hver : c.version = some ver) {v : VersionVariant}
    (hm : ∀ m ∈ v.reply.mentions, m = c.name ∨ m = ver) (hvv : ∀ x ∈ v.version?, x = ver)
    (S : Matches → Spec) : c.spec S ≤ v.sen := by
  refine spec_version (versionTriggers_of_wf hwf hv (by simp [hver]) v) ?_ S
  have : c.versionBytes = utf8 (c.name ++ " " ++ ver ++ "\n") := by
    simp [Command.versionBytes, hver]
  rw [this]
  exact VersionVariant.fits_versionLine hm hvv

theorem versionOpt_mem_withVersion (c : Command) (ver : String) :
    versionOpt ∈ (c.withVersion ver).opts := by
  show versionOpt ∈ c.opts ++ [versionOpt]
  simp

/-! ## Programs behind a derived front end -/

/-- **Every Lean program behind a derived args front end** that answers the requests of a
variant, with texts that fit, meets the variant, whatever its body does. -/
theorem _root_.Silmaril.Cli.Io.Prog.ofCommand_sat_help {c : Command} {v : HelpVariant}
    (h : c.helpTriggers v = true) (hfit : ∀ p ∈ v.roots, v.Fits p (c.helpBytes p))
    (body : Matches → Io.Prog ExitCode) : (Io.Prog.ofCommand c body).Sat v.sen :=
  ((Io.Prog.sat_ofCommand_iff c body fun _ => ⊤).mpr fun _ _ _ => trivial).mono
    (spec_help h hfit _)

theorem _root_.Silmaril.Cli.Io.Prog.ofCommand_sat_version {c : Command} {v : VersionVariant}
    (h : c.versionTriggers v = true) (hfit : v.Fits c.versionBytes)
    (body : Matches → Io.Prog ExitCode) : (Io.Prog.ofCommand c body).Sat v.sen :=
  ((Io.Prog.sat_ofCommand_iff c body fun _ => ⊤).mpr fun _ _ _ => trivial).mono
    (spec_version h hfit _)

/-- `Command.main`, read in the behaviour model, meets every variant its front end answers. -/
theorem _root_.Silmaril.Cli.Command.modelMain_help {c : Command} {v : HelpVariant}
    (h : c.helpTriggers v = true) (hfit : ∀ p ∈ v.roots, v.Fits p (c.helpBytes p))
    (run : Matches → Beh UInt32) : (ofSpec (Beh.toSpec (c.modelMain run))).Sat v.sen :=
  (ofSpec_sat_iff _ _).mpr ((main_refines c fun _ => le_top).trans (spec_help h hfit _))

/-! ## Clap front ends -/

/-- **Every well-formed clap grammar with help on every command** (`helpEverywhere`) meets
every help variant without required substrings, pinned texts or a usage-error claim, at paths
its words select (a `help` word needs clap's `help` subcommand and subcommands). -/
theorem _root_.Silmaril.Cli.Clap.Tool.spec_le_help {t : Clap.Tool} {c : Command}
    (hpres : t.present = none) (hc : t.grammar = c.helpEverywhere) (hwf : t.grammar.WF)
    {v : HelpVariant}
    (hm : v.reply.mentions = []) (ht : v.texts = []) (hx : v.extra ≠ .error)
    (hw : v.word = true → t.helpSub = true ∧ t.grammar.subs.isEmpty = false)
    (hp : ∀ p ∈ v.roots, (Clap.pathLevel t t.grammar p).isSome = true)
    (S : Matches → Spec) : t.spec S ≤ v.sen :=
  Clap.spec_help hpres (Clap.helpTriggers_everywhere hc hwf hx hw hp)
    (fun p _ => HelpVariant.fits_line hm ht p _) S

/-- `Tool.main`, read in the behaviour model, meets every variant its front end answers. -/
theorem _root_.Silmaril.Cli.Clap.Tool.modelMain_help {t : Clap.Tool} {v : HelpVariant}
    (hpres : t.present = none) (h : Clap.helpTriggers t v = true)
    (hfit : ∀ p ∈ v.roots, v.Fits p (Clap.helpBytes t (t.grammar.pathNames p)))
    (run : Matches → Beh UInt32) : (ofSpec (Beh.toSpec (t.modelMain run))).Sat v.sen :=
  (ofSpec_sat_iff _ _).mpr ((t.main_refines_front run).trans (Clap.spec_help hpres h hfit _))

end Silmaril.Cli.Info
