module

public import Silmaril.X86.Concurrency.Cir.Litmus.Defs

/-!
# CIR litmus tests: per-test kernel checks

One `decide +kernel` per test and per Boolean check. What they give is stated in
`Silmaril.X86.Concurrency.Cir.Litmus.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Litmus

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Lit

set_option maxRecDepth 100000

/-! ## Verdict checks -/

theorem check_sb : sb.check = true := by decide +kernel
theorem check_sbMfences : sbMfences.check = true := by decide +kernel
theorem check_mp : mp.check = true := by decide +kernel
theorem check_mpMfences : mpMfences.check = true := by decide +kernel
theorem check_lb : lb.check = true := by decide +kernel
theorem check_iriw : iriw.check = true := by decide +kernel
theorem check_w22 : w22.check = true := by decide +kernel
theorem check_n6 : n6.check = true := by decide +kernel
theorem check_rmwXadds : rmwXadds.check = true := by decide +kernel
theorem check_sbCas : sbCas.check = true := by decide +kernel
theorem check_mpSpawn : mpSpawn.check = true := by decide +kernel
theorem check_mpJoin : mpJoin.check = true := by decide +kernel
theorem check_mpFutex : mpFutex.check = true := by decide +kernel
theorem check_mpLocal : mpLocal.check = true := by decide +kernel
theorem check_mpNt : mpNt.check = true := by decide +kernel

/-! ## Translation validation against the bytes -/

theorem matches_sb : sb.matchesX86 = true := by decide +kernel
theorem matches_sbMfences : sbMfences.matchesX86 = true := by decide +kernel
theorem matches_mp : mp.matchesX86 = true := by decide +kernel
theorem matches_mpMfences : mpMfences.matchesX86 = true := by decide +kernel
theorem matches_lb : lb.matchesX86 = true := by decide +kernel
theorem matches_iriw : iriw.matchesX86 = true := by decide +kernel
theorem matches_w22 : w22.matchesX86 = true := by decide +kernel
theorem matches_n6 : n6.matchesX86 = true := by decide +kernel
theorem matches_rmwXadds : rmwXadds.matchesX86 = true := by decide +kernel
theorem matches_sbCas : sbCas.matchesX86 = true := by decide +kernel

/-! ## Uniformity and closed domains -/

theorem uniform_closed :
    [sb, sbMfences, mp, mpMfences, lb, iriw, w22, n6, sbCas, mpSpawn, mpJoin, mpFutex,
      mpLocal].all (fun c => c.prog.uniformB && c.prog.preClosedB c.domain) = true := by
  decide +kernel

theorem rmwXadds_uniform : rmwXadds.prog.uniformB = true := by decide +kernel

/-- The `RMW+lock-xadds` domain is not closed (an increment of `2` writes `3`). -/
theorem rmwXadds_not_closed : rmwXadds.prog.closedB rmwXadds.domain = false := by decide +kernel

/-- Nor is it closed under partial runs. -/
theorem rmwXadds_not_preClosed : rmwXadds.prog.preClosedB rmwXadds.domain = false := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Litmus
