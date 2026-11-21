module

public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvCorpus

/-!
# The translation-validated corpus: what is proved

All statements are PROVED (standard axioms only; the per-test checks
are kernel `decide`s in `Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean`):

* `corpus_covers`: the validated tests are exactly the 60 x86-TSO-covered tests, in
  corpus order;
* `corpus_all_ok`: each passes `TvTest.allOk`: every thread's certificate checks against its
  bytes, the domain hypothesis holds, the CIR verdicts over the x86 test's own domain are the
  recorded ones, and the bytes extract;
* `corpus_transfer`: so each has `TvTest.Transfer`: x86 behaviours refine CIR behaviours, the
  CIR program has the recorded SC/TSO/XL verdicts, and every `forbidden` verdict is transferred
  from CIR to the bytes;
* `corpus_agree`: for every test and model, the CIR verdict and the x86 verdict (see
  `corpus_tso_verdicts`) are both the recorded verdict.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.Corpus

open Silmaril.X86.MemoryModel.Litmus (AxReach Model Coverage)

/-- The validated tests are the x86-TSO-covered tests. -/
theorem corpus_covers :
    all.map (·.test.name) =
      (Silmaril.X86.MemoryModel.Litmus.Corpus.all.filter (·.coverage == .tso)).map (·.name) := by
  decide +kernel

/-- Every validated test passes its check. -/
theorem corpus_all_ok : ∀ c ∈ all, c.allOk = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCorpus.all_ok

/-- **Every validated test transfers** (`TvTest.Transfer`). -/
theorem corpus_transfer : ∀ c ∈ all, c.Transfer :=
  fun c hc => TvTest.transfer_of_allOk (corpus_all_ok c hc)

theorem corpus_shape :
    all.all (fun c => c.test.coverage == .tso && c.test.sc.isSome && c.test.tso.isSome) = true := by
  decide +kernel

/-- **The CIR verdict is the x86 verdict**: for every validated test and model, the recorded
verdict holds for the CIR program (over the test's domain) and for the x86 bytes. -/
theorem corpus_agree : ∀ c ∈ all, ∃ T, c.test.traces = some T ∧ ∀ M : Model,
    (c.verdict M).Holds c.test (BehavIn c.prog c.test.domain M.Holds) ∧
      (c.verdict M).Holds c.test (AxReach c.test T M.Holds) := by
  intro c hc
  have hs := List.all_eq_true.mp corpus_shape c hc
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hs
  obtain ⟨⟨hcov, vs, hvs⟩, vt, hvt⟩ := hs
  have hmem := Silmaril.Proofs.X86.Concurrency.Cir.TvCorpus.all_mem c hc
  obtain ⟨T, hT, hv⟩ := Silmaril.X86.MemoryModel.Litmus.corpus_tso_verdicts c.test hmem hcov
  refine ⟨T, hT, fun M => ⟨(corpus_transfer c hc).cir M, ?_⟩⟩
  cases M
  · simp only [TvTest.verdict, hvs, Option.getD_some]
    exact hv.sc_ax vs hvs
  · simp only [TvTest.verdict, hvt, Option.getD_some]
    exact hv.tso_ax vt hvt
  · exact hv.xl_ax

/-- **Non-vacuity**: the CIR program validated from SB's bytes is genuinely weak. Under
TSO its store-buffering outcome (both loads read 0) is reachable, under SC it is not; the same
holds for the x86 bytes. -/
theorem sb_cir_weak :
    «SB».test.Allowed (BehavIn «SB».prog «SB».test.domain Model.tso.Holds) ∧
      ¬ «SB».test.Allowed (BehavIn «SB».prog «SB».test.domain Model.sc.Holds) ∧
      ∃ T, «SB».test.traces = some T ∧ «SB».test.Allowed (AxReach «SB».test T Model.tso.Holds) := by
  have h := corpus_agree «SB» List.mem_cons_self
  obtain ⟨T, hT, hv⟩ := h
  exact ⟨(hv .tso).1, (hv .sc).1, T, hT, (hv .tso).2⟩

end Silmaril.X86.Concurrency.Cir.Tv.Corpus
