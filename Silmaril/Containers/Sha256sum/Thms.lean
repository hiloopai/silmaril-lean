module

public import Silmaril.Containers.Sha256sum.Defs
public import Silmaril.Elf.LpsCli.Thms
public import Silmaril.Process.Thms
import Silmaril.Proofs.Containers.Sha256sum.Basic

public section
namespace Silmaril.Containers.Sha256sum
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Problems

/-- All finite messages, flag oracles, refusal configurations, budgets and admissible stdin-tier
launches. The stronger total execution theorem supplies error freedom and modeledness. -/
theorem gnu_noUB (o : Nat → Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (message : List Byte)
    (ha : GnuSha256sum.Admissible o en inp message) (r : Report)
    (hr : r.Occurs (GnuSha256sum.behaviour o refusals limit en inp)) : r.observe.NoUB :=
  Silmaril.Proofs.Containers.Sha256sum.reports_noUB _
    (Silmaril.Process.gnuSha256sum_lpsTotal o refusals limit en inp message trivial ha).safety.errorFree
    (Silmaril.Process.gnuSha256sum_lpsTotal o refusals limit en inp message trivial ha).safety.modeled r hr

/-- An ended report has the original GNU stdin specification's output and exits zero. -/
theorem gnu_output (o : Nat → Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (message : List Byte)
    (ha : GnuSha256sum.Admissible o en inp message) {tr : List Event}
    {out : Silmaril.Cli.Institution.Out1}
    (hr : (Report.ended tr out).Occurs (GnuSha256sum.behaviour o refusals limit en inp)) :
    out = { stdout := Silmaril.Elf.LpsCli.cliBytes (GnuSha256sum.expected message), exit := 0 } :=
  Silmaril.Elf.LpsCli.out1Of_of_prefix
    ((Silmaril.Process.gnuSha256sum_lpsTotal o refusals limit en inp message trivial ha).safety.safe _ hr.1) hr.2

/-- Nonvacuity for every admissible launch: the existing theorem's complete trace gives an
actual ended report. No new hashing proof or OCI layout evaluation. -/
theorem gnu_complete (o : Nat → Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (message : List Byte)
    (ha : GnuSha256sum.Admissible o en inp message) :
    (Report.ended (GnuSha256sum.idealTrace message inp.fs)
      { stdout := Silmaril.Elf.LpsCli.cliBytes (GnuSha256sum.expected message), exit := 0 }).Occurs
      (GnuSha256sum.behaviour o refusals limit en inp) :=
  ⟨(Silmaril.Process.gnuSha256sum_lpsTotal o refusals limit en inp message trivial ha).complete,
    Silmaril.Elf.LpsCli.out1Of_filterTrace _ _ _⟩

/-- The smaller 2368-byte filter uses its own existing total execution theorem. -/
theorem filter_noUB (o : Nat → Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (message : List Byte)
    (ha : Sha256Cli.Admissible o en inp message) (r : Report)
    (hr : r.Occurs (Sha256Cli.behaviour o refusals limit en inp)) : r.observe.NoUB :=
  Silmaril.Proofs.Containers.Sha256sum.reports_noUB _
    (Silmaril.Process.sha256Cli_total o refusals limit en inp message trivial ha).safety.errorFree
    (Silmaril.Process.sha256Cli_total o refusals limit en inp message trivial ha).safety.modeled r hr

end Silmaril.Containers.Sha256sum
