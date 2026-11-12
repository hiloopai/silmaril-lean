module

public import Silmaril.Project.Shapes.Cli.Defs
public import Silmaril.Cli.Info.Thms

/-! # Standard problem shapes: command-line programs (transfer lemmas)

* `Help.of_sat`, `Version.of_sat`: a Lean program meeting a variant fills the row with its
  model (`Io.Prog.model`);
* `Help.ofCommand`, `Version.ofCommand`: every Lean program behind a derived front end that
  answers the variant's requests fills it, whatever its body does;
* `Help.mono`, `Version.mono`: a row of a stricter variant gives the row of a looser one;
* `help_via_iff`, `version_via_iff`: a model at another interface `A`, with a morphism from the
  full interface (how an ELF or WASI model plugs in), satisfies the translated sentence iff its
  reduct fills the row.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Cli

open Silmaril.Cli Silmaril.Cli.Info Silmaril.Cli.Institution

theorem Help.of_sat {p : Io.Prog ExitCode} {v : HelpVariant} (h : p.Sat v.sen) :
    Help p.model v :=
  (Io.Prog.model_sat_iff p _).mpr h

theorem Version.of_sat {p : Io.Prog ExitCode} {v : VersionVariant} (h : p.Sat v.sen) :
    Version p.model v :=
  (Io.Prog.model_sat_iff p _).mpr h

theorem Help.ofCommand {c : Command} {v : HelpVariant} (h : c.helpTriggers v = true)
    (hfit : ∀ p ∈ v.roots, v.Fits p (c.helpBytes p)) (body : Matches → Io.Prog ExitCode) :
    Help (Io.Prog.ofCommand c body).model v :=
  Help.of_sat (Io.Prog.ofCommand_sat_help h hfit body)

theorem Version.ofCommand {c : Command} {v : VersionVariant} (h : c.versionTriggers v = true)
    (hfit : v.Fits c.versionBytes) (body : Matches → Io.Prog ExitCode) :
    Version (Io.Prog.ofCommand c body).model v :=
  Version.of_sat (Io.Prog.ofCommand_sat_version h hfit body)

theorem Help.mono {M : Silmaril.Cli.Institution.Model Level.full.sig} {v w : HelpVariant}
    (hvw : v.Le w) (h : Help M v) : Help M w :=
  Model.Sat.mono h (HelpVariant.sen_mono hvw)

theorem Version.mono {M : Silmaril.Cli.Institution.Model Level.full.sig} {v w : VersionVariant}
    (hvw : v.Le w) (h : Version M v) : Version M w :=
  Model.Sat.mono h (VersionVariant.sen_mono hvw)

theorem help_via_iff {A : Sig} (h : Level.full.sig ⟶ A) (M : Silmaril.Cli.Institution.Model A)
    (v : HelpVariant) : M.Sat (Hom.sen h v.sen) ↔ Help (Hom.mod h M) v :=
  sat_via_iff h M v.sen

theorem version_via_iff {A : Sig} (h : Level.full.sig ⟶ A)
    (M : Silmaril.Cli.Institution.Model A) (v : VersionVariant) :
    M.Sat (Hom.sen h v.sen) ↔ Version (Hom.mod h M) v :=
  sat_via_iff h M v.sen

end Silmaril.Project.Shapes.Cli
