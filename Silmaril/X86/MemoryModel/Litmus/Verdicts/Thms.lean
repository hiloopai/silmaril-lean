module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Thms
import Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.All

/-!
# Litmus verdicts: theorems for the whole corpus

PROVED (standard axioms only; each per-test check is a kernel `decide` in
`Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.*`, the rest is `Models.Thms`):

* `corpus_tso_verdicts`: for every x86-TSO-covered test (60), with the traces extracted from
  its bytes: the operational TSO outcomes (store-buffer machine `Tso.XStep`/`Tso.XFlush`) equal
  the axiomatic TSO outcomes (`Exec.Tso`); the recorded TSO verdict (herd7 output, the
  x86-TSO paper, or the checker) holds in both; the recorded SC verdict holds in axiomatic SC;
  the recorded XL verdict holds in XL; some SC execution exists, so no verdict is vacuous;
* `corpus_relied_xl_forbidden`: every TSO-covered test whose TSO verdict is forbidden (the
  outcomes programs rely on: SB+mfences, MP, MP+fences, 2+2W, IRIW+mfences, the RMW atomicity
  tests, the n-series forbidden tests, ...) is forbidden by XL too;
* `corpus_sc_tso_xl`: per test, SC ⊆ TSO ⊆ XL for the axiomatic final states, and every
  operational TSO outcome is an XL outcome;
* `corpus_loose_xl`: every loose corner (8) has its recorded XL verdict, axiomatic TSO and SC
  forbid its witness, and some SC execution exists; where XL allows, this is loose **by
  design** (XL allows mixed-size and misaligned tearing, and orders non-temporal and string
  stores only by fences and locked instructions);
* `msHalves_plain`, `misStraddle_plain`: for the two plain loose corners, operational and
  axiomatic TSO have the same outcomes and forbid the witness, SC forbids it, while XL allows it.

The traces are relative to each test's value domain (`Test.domain`; see
`Silmaril.X86.MemoryModel.Litmus.Closure` for when that domain is closed). Now every
loose corner's traces come from its bytes too: the six `movnti`/`rep stosb` tests are extracted
over `Weak9` (`Test.looseTraces`, `Test.wtraces`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- Every x86-TSO-covered corpus test passes its check (kernel `decide`, one per test). -/
theorem corpus_tso_checks : ∀ t ∈ Corpus.all, t.coverage = .tso → t.checkTsoBytes = true :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.all_tso

/-- Every loose corner passes its XL check. -/
theorem corpus_xl_checks : ∀ t ∈ Corpus.all, t.coverage = .xl → t.checkXlLoose = true :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.all_xl

/-- **The verdicts of every x86-TSO-covered test** (see `TsoVerdicts`), on the traces of its
bytes. -/
theorem corpus_tso_verdicts :
    ∀ t ∈ Corpus.all, t.coverage = .tso → ∃ T, t.traces = some T ∧ TsoVerdicts t T :=
  fun t ht hc => tsoVerdicts_of_checkBytes (corpus_tso_checks t ht hc)

/-- **XL forbids every outcome x86-TSO forbids on the covered tests**; the test has SC and
operational TSO executions, so this is not vacuous. -/
theorem corpus_relied_xl_forbidden :
    ∀ t ∈ Corpus.all, t.coverage = .tso → t.tso = some .forbidden →
      ∃ T, t.traces = some T ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Xl) ∧
        Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
        Verdict.forbidden.Holds t (OpReach t T) ∧
        (∃ f, AxReach t T Exec.Sc f) ∧ (∃ f, OpReach t T f) := by
  intro t ht hc hf
  obtain ⟨T, hT, hv⟩ := corpus_tso_verdicts t ht hc
  have hxl : t.xl = .forbidden := Corpus.xl_eq_tso t ht _ hf
  refine ⟨T, hT, ?_, hv.tso_ax _ hf, hv.tso_op _ hf, hv.sc_some, hv.op_some⟩
  have := hv.xl_ax
  rwa [hxl] at this

/-- **SC ⊆ TSO ⊆ XL per test**, and operational TSO outcomes are XL outcomes. -/
theorem corpus_sc_tso_xl :
    ∀ t ∈ Corpus.all, t.coverage = .tso → ∃ T, t.traces = some T ∧
      (∀ f, AxReach t T Exec.Sc f → AxReach t T Exec.Tso f) ∧
      (∀ f, AxReach t T Exec.Tso f → AxReach t T Exec.Xl f) ∧
      (∀ f, OpReach t T f → ∃ g, AxReach t T Exec.Xl g ∧ t.outcome g = t.outcome f) := by
  intro t ht hc
  obtain ⟨T, hT, hv⟩ := corpus_tso_verdicts t ht hc
  refine ⟨T, hT, fun _ => axReach_sc_tso, fun _ => axReach_tso_xl, ?_⟩
  intro f hf
  obtain ⟨g, hg, ho⟩ := (hv.op_eq_ax _).mp ⟨f, hf, rfl⟩
  exact ⟨g, axReach_tso_xl hg, ho⟩

/-- **Every loose corner has its recorded XL verdict** (loose by design), while axiomatic TSO
and SC forbid its witness and some SC execution exists. -/
theorem corpus_loose_xl :
    ∀ t ∈ Corpus.all, t.coverage = .xl →
      ∃ T, t.looseTraces = some T ∧ t.xl.Holds t (AxReach t T Exec.Xl) ∧
        Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
        Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧ ∃ f, AxReach t T Exec.Sc f := by
  intro t ht hc
  have h := corpus_xl_checks t ht hc
  unfold Test.checkXlLoose at h
  split at h
  · rename_i T hT; exact ⟨T, hT, loose_of_check h⟩
  · cases h

theorem plain_of_bytes {t : Test} (h : t.checkPlainLooseBytes = true) :
    ∃ T, t.traces = some T ∧
      (∀ o, (∃ f, OpReach t T f ∧ t.outcome f = o) ↔
        (∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o)) ∧
      Verdict.forbidden.Holds t (OpReach t T) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
      t.xl.Holds t (AxReach t T Exec.Xl) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧
      ∃ f, AxReach t T Exec.Sc f := by
  unfold Test.checkPlainLooseBytes at h
  split at h
  · rename_i T hT; exact ⟨T, hT, plainLoose_of_check h⟩
  · cases h

/-- `MS+halves`: TSO (operational = axiomatic) forbids the torn read, XL allows it. -/
theorem msHalves_plain :
    ∃ T, Corpus.«MS+halves».traces = some T ∧
      (∀ o, (∃ f, OpReach Corpus.«MS+halves» T f ∧ Corpus.«MS+halves».outcome f = o) ↔
        (∃ f, AxReach Corpus.«MS+halves» T Exec.Tso f ∧ Corpus.«MS+halves».outcome f = o)) ∧
      Verdict.forbidden.Holds Corpus.«MS+halves» (OpReach Corpus.«MS+halves» T) ∧
      Verdict.forbidden.Holds Corpus.«MS+halves» (AxReach Corpus.«MS+halves» T Exec.Tso) ∧
      Verdict.allowed.Holds Corpus.«MS+halves» (AxReach Corpus.«MS+halves» T Exec.Xl) ∧
      Verdict.forbidden.Holds Corpus.«MS+halves» (AxReach Corpus.«MS+halves» T Exec.Sc) ∧
      ∃ f, AxReach Corpus.«MS+halves» T Exec.Sc f :=
  plain_of_bytes Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.«plain_MS+halves»

/-- `MIS+straddle`: TSO (operational = axiomatic) forbids the torn read, XL allows it. -/
theorem misStraddle_plain :
    ∃ T, Corpus.«MIS+straddle».traces = some T ∧
      (∀ o, (∃ f, OpReach Corpus.«MIS+straddle» T f ∧ Corpus.«MIS+straddle».outcome f = o) ↔
        (∃ f, AxReach Corpus.«MIS+straddle» T Exec.Tso f ∧ Corpus.«MIS+straddle».outcome f = o)) ∧
      Verdict.forbidden.Holds Corpus.«MIS+straddle» (OpReach Corpus.«MIS+straddle» T) ∧
      Verdict.forbidden.Holds Corpus.«MIS+straddle» (AxReach Corpus.«MIS+straddle» T Exec.Tso) ∧
      Verdict.allowed.Holds Corpus.«MIS+straddle» (AxReach Corpus.«MIS+straddle» T Exec.Xl) ∧
      Verdict.forbidden.Holds Corpus.«MIS+straddle» (AxReach Corpus.«MIS+straddle» T Exec.Sc) ∧
      ∃ f, AxReach Corpus.«MIS+straddle» T Exec.Sc f :=
  plain_of_bytes Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.«plain_MIS+straddle»

end Silmaril.X86.MemoryModel.Litmus
