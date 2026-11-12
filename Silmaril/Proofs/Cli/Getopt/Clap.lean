module

public import Silmaril.Cli.Getopt.Defs
public import Silmaril.Cli.Clap.Defs

/-!
# Proofs: the getopt and clap readings

* `agrees_clap`: a clap outcome that agrees with an args outcome agrees with every getopt
  outcome that agrees with it (`Agrees`: equal, or usage errors on both sides).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Cli.Getopt

open Silmaril.Cli Silmaril.Cli.Getopt

theorem agrees_clap {co : Clap.Outcome} {g i : Outcome} (h1 : co.Agrees i) (h2 : Agrees g i) :
    co.Agrees g := by
  cases g with
  | run m => simp only [Agrees] at h2; subst h2; exact h1
  | help p => simp only [Agrees] at h2; subst h2; exact h1
  | version v => simp only [Agrees] at h2; subst h2; exact h1
  | error p e =>
    cases i with
    | error p' e' => cases co <;> simp_all [Clap.Outcome.Agrees]
    | run m => simp [Agrees] at h2
    | help q => simp [Agrees] at h2
    | version v => simp [Agrees] at h2

end Silmaril.Proofs.Cli.Getopt
