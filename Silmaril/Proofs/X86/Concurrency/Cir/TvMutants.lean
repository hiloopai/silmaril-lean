module

public import Silmaril.X86.Concurrency.Cir.Tv.Mutants.Defs

/-!
# Translation validation mutants: kernel checks

`decide +kernel` that every mutant of
`Cir.Tv.Mutants.all` gets the expected answer from `tvCheck`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvMutants

open Silmaril.X86.Concurrency.Cir.Tv

set_option maxRecDepth 100000

theorem all_ok : Mutants.all.all Mutants.Mutant.ok = true := by decide +kernel

theorem test_ok : Mutants.testMutants.all (fun m => m.2.1.tvOk == m.2.2) = true := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.TvMutants
