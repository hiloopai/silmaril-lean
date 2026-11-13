module

public import Silmaril.X86.Concurrency.Cir.C11.Mutants.Defs

/-!
# C11 tests on CIR: the mutants are rejected

PROVED by kernel `decide`: `check` rejects every
mutant of `Cir.C11.Mutants.all`, and accepts the unmutated `MP+ra@gcc` (a control; the corpus
proves the others).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11.Mutants

set_option maxRecDepth 100000

theorem scStoreMov_rejected : scStoreMov.check = false := by decide +kernel
theorem relLoad_rejected : relLoad.check = false := by decide +kernel
theorem mpRaRlx_rejected : mpRaRlx.check = false := by decide +kernel
theorem sbScAllowed_rejected : sbScAllowed.check = false := by decide +kernel
theorem mpRlxNotStronger_rejected : mpRlxNotStronger.check = false := by decide +kernel
theorem sbFencesPlain_rejected : sbFencesPlain.check = false := by decide +kernel

/-- The `MP+ra@gcc` mutant passes TV and the mapping check: only RC11 rejects it. -/
theorem mpRaRlx_tv : (mpRaRlx.tv.tvOk && mpRaRlx.modesOk) = true := by decide +kernel

/-- The control. -/
theorem mpRa_accepted : Corpus.«MP+ra@gcc».check = true := by decide +kernel

/-- **Every mutant is rejected.** -/
theorem mutants_rejected : ∀ c ∈ all, c.check = false := by
  intro c hc
  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact scStoreMov_rejected
  · exact relLoad_rejected
  · exact mpRaRlx_rejected
  · exact sbScAllowed_rejected
  · exact mpRlxNotStronger_rejected
  · exact sbFencesPlain_rejected

end Silmaril.X86.Concurrency.Cir.C11.Mutants
