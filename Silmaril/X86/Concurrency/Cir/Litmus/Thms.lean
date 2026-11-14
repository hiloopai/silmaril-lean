module

public import Silmaril.X86.Concurrency.Cir.Litmus.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
public import Silmaril.X86.Concurrency.Cir.Domain.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Litmus

/-!
# CIR litmus tests: verdict theorems

PROVED (standard axioms only):

* `verdicts_of_check`: a passing `CTest.check` gives `CTest.Verdicts`: for each of SC, TSO and
  XL the recorded verdict holds for the program's behaviours over the test's domain
  (`BehavIn`), some SC behaviour exists, every `allowed` verdict holds for all behaviours
  (`Behav`), and every `forbidden` verdict holds for all behaviours if the program is uniform
  with a domain closed under partial runs (`preClosedB`) and closed local blocks (by
  `cirDomain`);
* `corpus_verdicts`: the ten re-expressed corpus tests (`SB`, `SB+mfences`, `MP`,
  `MP+mfences`, `LB`, `IRIW` = `amd6`, `2+2W`, `n6`, `RMW+lock-xadds`, `SB+lock-cmpxchgs`)
  have their recorded verdicts;
* `cir_verdicts`: the CIR-only tests `MP+spawn`, `MP+join`, `MP+futex`, `MP+local` are
  forbidden under SC, TSO and XL, and `MP+nt` is allowed under XL and forbidden under TSO and SC;
* `corpus_matches_x86`: the CIR threads of the ten corpus tests have the same memory actions
  (with flavours) and observed registers as the traces the extractor extracts from the tests' bytes;
* `uniform_closed`: every test except `RMW+lock-xadds` is uniform with a domain closed under
  partial runs, so its `forbidden` verdicts hold for all behaviours (`forbidden_behav_all`,
  unconditional, as `Task.cirDomain` is proved; their local blocks are closed,
  `blocksClosed`).
  `RMW+lock-xadds`' verdict is relative to its domain, as in
  the corpus.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- CIR behaviours over a domain are `AxReach` for the test, over the CIR traces. -/
theorem CTest.behavIn_iff (c : CTest) (dom : List Nat) (M : Exec → Prop) (f : Final) :
    BehavIn c.prog dom M f ↔ AxReach c.test (c.prog.traces dom) M f := Iff.rfl

/-- What a CIR litmus test's verdict theorem states. -/
structure CTest.Verdicts (c : CTest) : Prop where
  /-- The recorded verdict of each model holds over the test's domain. -/
  holds : ∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.domain M.Holds)
  /-- Some SC behaviour exists, so no verdict is vacuous. -/
  sc_some : ∃ f, BehavIn c.prog c.domain Exec.Sc f
  /-- `allowed` verdicts hold for all behaviours. -/
  allowed : ∀ M : Model, c.verdict M = .allowed →
    Verdict.allowed.Holds c.test (Behav c.prog M.Holds)
  /-- `forbidden` verdicts hold for all behaviours, for a uniform program with a domain closed
  under partial runs and closed blocks (domain closure, `cirDomain`). -/
  forbidden : c.prog.uniformB = true → c.prog.preClosedB c.domain = true →
    c.prog.BlocksClosed c.domain → ∀ M : Model, c.verdict M = .forbidden →
      Verdict.forbidden.Holds c.test (Behav c.prog M.Holds)

/-- **A passing check gives the verdict theorem.** -/
theorem verdicts_of_check {c : CTest} (h : c.check = true) : c.Verdicts := by
  unfold CTest.check at h
  split at h
  · rename_i js hjs
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hsc, htso⟩, hxl⟩, hne⟩ := h
    have hv : ∀ M : Model, c.verdict M = c.test.verdictOf (outsBy js M.sel) := by
      intro M; cases M
      · exact hsc
      · exact htso
      · exact hxl
    have hold : ∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.domain M.Holds) := by
      intro M
      rw [hv M]
      exact verdictOf_holds fun o => axJudge_spec hjs M o
    refine ⟨hold, ?_, ?_, ?_⟩
    · obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
      obtain ⟨f, hf, _⟩ := (axJudge_spec hjs Model.sc o).mp ho
      exact ⟨f, hf⟩
    · intro M hM
      have := hold M
      rw [hM] at this
      exact allowed_mono (fun _ hf => behavIn_behav hf) this
    · intro hU hC hB M hM
      have := hold M
      rw [hM] at this
      exact forbidden_anti (fun f hf => cirDomain c.prog c.domain hU hC hB M f hf) this
  · cases h

open Silmaril.Proofs.X86.Concurrency.Cir.Litmus in
/-- **The re-expressed corpus tests have their recorded verdicts.** -/
theorem corpus_verdicts : ∀ c ∈ Lit.corpusTests, c.Verdicts := by
  intro c hc
  simp only [Lit.corpusTests, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verdicts_of_check check_sb
  · exact verdicts_of_check check_sbMfences
  · exact verdicts_of_check check_mp
  · exact verdicts_of_check check_mpMfences
  · exact verdicts_of_check check_lb
  · exact verdicts_of_check check_iriw
  · exact verdicts_of_check check_w22
  · exact verdicts_of_check check_n6
  · exact verdicts_of_check check_rmwXadds
  · exact verdicts_of_check check_sbCas

open Silmaril.Proofs.X86.Concurrency.Cir.Litmus in
/-- **The CIR-only tests have their intended verdicts.** -/
theorem cir_verdicts : ∀ c ∈ Lit.cirTests, c.Verdicts := by
  intro c hc
  simp only [Lit.cirTests, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact verdicts_of_check check_mpSpawn
  · exact verdicts_of_check check_mpJoin
  · exact verdicts_of_check check_mpFutex
  · exact verdicts_of_check check_mpLocal
  · exact verdicts_of_check check_mpNt

open Silmaril.Proofs.X86.Concurrency.Cir.Litmus in
/-- **The CIR programs match the bytes**: per thread, the same memory actions and observed
registers as the extraction. -/
theorem corpus_matches_x86 : ∀ c ∈ Lit.corpusTests, c.matchesX86 = true := by
  intro c hc
  simp only [Lit.corpusTests, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact matches_sb
  · exact matches_sbMfences
  · exact matches_mp
  · exact matches_mpMfences
  · exact matches_lb
  · exact matches_iriw
  · exact matches_w22
  · exact matches_n6
  · exact matches_rmwXadds
  · exact matches_sbCas

/-- Every test but `RMW+lock-xadds` is uniform with a domain closed under partial runs. -/
theorem uniform_closed :
    ∀ c ∈ [Lit.sb, Lit.sbMfences, Lit.mp, Lit.mpMfences, Lit.lb, Lit.iriw, Lit.w22, Lit.n6,
      Lit.sbCas, Lit.mpSpawn, Lit.mpJoin, Lit.mpFutex, Lit.mpLocal],
      c.prog.uniformB = true ∧ c.prog.preClosedB c.domain = true := by
  intro c hc
  have h := Silmaril.Proofs.X86.Concurrency.Cir.Litmus.uniform_closed
  rw [List.all_eq_true] at h
  simpa using h c hc

/-- The local blocks of the thirteen tests are closed over their domains (only `MP+local` has
blocks: `put1` outputs `1`, which is in its domain, and `getx` outputs its input). -/
theorem blocksClosed :
    ∀ c ∈ [Lit.sb, Lit.sbMfences, Lit.mp, Lit.mpMfences, Lit.lb, Lit.iriw, Lit.w22, Lit.n6,
      Lit.sbCas, Lit.mpSpawn, Lit.mpJoin, Lit.mpFutex, Lit.mpLocal],
      c.prog.BlocksClosed c.domain := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact blocksClosed_of_noBlocks (by decide +kernel) _
  intro th hth b hb rv iv o hrv hiv hs v hv
  have hblk : th.body.blocks = [Lit.putOne] ∨ th.body.blocks = [Lit.getX] := by
    simp only [CTest.prog, Lit.mpLocal, List.mem_cons, List.not_mem_nil, or_false] at hth
    rcases hth with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  rcases hblk with h | h <;> rw [h, List.mem_singleton] at hb <;> subst hb
  · change o = [1] at hs
    subst hs
    rw [List.mem_singleton] at hv
    subst hv
    decide +kernel
  · change o = rv ++ iv at hs
    have : rv = [] := List.eq_nil_of_length_eq_zero hrv
    subst this hs
    exact hiv v hv

open Silmaril.Proofs.X86.Concurrency.Cir.Litmus in
/-- **Forbidden for all behaviours**: for every test but `RMW+lock-xadds`, each `forbidden`
verdict holds for all behaviours (any value domain), by domain closure (`cirDomain`). -/
theorem forbidden_behav_all :
    ∀ c ∈ [Lit.sb, Lit.sbMfences, Lit.mp, Lit.mpMfences, Lit.lb, Lit.iriw, Lit.w22, Lit.n6,
      Lit.sbCas, Lit.mpSpawn, Lit.mpJoin, Lit.mpFutex, Lit.mpLocal],
      ∀ M : Model, c.verdict M = .forbidden →
        Verdict.forbidden.Holds c.test (Behav c.prog M.Holds) := by
  intro c hc M hM
  have hv : c.Verdicts := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact verdicts_of_check check_sb
    · exact verdicts_of_check check_sbMfences
    · exact verdicts_of_check check_mp
    · exact verdicts_of_check check_mpMfences
    · exact verdicts_of_check check_lb
    · exact verdicts_of_check check_iriw
    · exact verdicts_of_check check_w22
    · exact verdicts_of_check check_n6
    · exact verdicts_of_check check_sbCas
    · exact verdicts_of_check check_mpSpawn
    · exact verdicts_of_check check_mpJoin
    · exact verdicts_of_check check_mpFutex
    · exact verdicts_of_check check_mpLocal
  obtain ⟨hU, hC⟩ := uniform_closed c hc
  exact hv.forbidden hU hC (blocksClosed c hc) M hM

end Silmaril.X86.Concurrency.Cir
