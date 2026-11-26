module

public import Silmaril.X86.Concurrency.Cir.Tv.Mutants.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.TvMutants

/-!
# Translation validation mutants: what is proved

PROVED by kernel `decide`: `tvCheck` rejects every mutant of
`Mutants.all` that must be rejected (a dropped `mfence` in the bytes or in the CIR program, a
dropped `lock` prefix on `xadd`, `cmpxchg` and `inc`, swapped stores in the bytes or in the CIR
program, a changed stored value, a non-temporal flavour for a plain store, a `cmpxchg` whose CIR
destination is not `rax`) and accepts the two controls (the unchanged certificate, and every mode
changed to `sc`). Further mutants: a scratch register that is later stored (clobber set `K`)
and a 32-bit `cmpxchg` whose `rax` does not fit in 32 bits (fitting set `Z`) are rejected, each
with an accepted control; at test level (`test_mutants_ok`), a scratch register the condition
observes is rejected by `tvOk`, with an accepted control.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.Mutants

/-- **Every mutant gets the expected answer.** -/
theorem mutants_ok : ∀ m ∈ all, tvCheck m.thread m.cert = m.accept := by
  intro m hm
  have := List.all_eq_true.mp Silmaril.Proofs.X86.Concurrency.Cir.TvMutants.all_ok m hm
  simpa [Mutant.ok] using this

/-- **Every test-level mutant gets the expected answer**: a clobbered scratch register
that the condition observes is rejected by `TvTest.tvOk`. -/
theorem test_mutants_ok : ∀ m ∈ testMutants, m.2.1.tvOk = m.2.2 := by
  intro m hm
  have := List.all_eq_true.mp Silmaril.Proofs.X86.Concurrency.Cir.TvMutants.test_ok m hm
  simpa using this

end Silmaril.X86.Concurrency.Cir.Tv.Mutants
