module

public import Silmaril.X86.MemoryModel.Litmus.Closure.Defs
public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms
import Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.Main
import Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.Corpus

/-!
# Value-domain closure of the litmus trace sets: what is proved

PROVED (standard axioms; proofs in
`Silmaril/Proofs/X86/MemoryModel/Litmus/Closure/`):

* `closure_of_cert`: if a test passes `Test.closureCert`, then for every model `M` contained in
  XL (in particular SC, x86-TSO and XL), every final state reachable over traces extracted with
  **any** value domain (`AxReachAny`) is reachable over `Test.traces`, by the same choice of
  traces and the same candidate execution. The proof is the rank argument described in
  `Closure/Defs.lean` (`Rank.lean`), with the skeleton, restriction and prefix lemmas of
  `Silmaril.X86.Litmus.Domain`.
* `axReachAny_iff`: so, for such tests, `AxReachAny t M` and `AxReach t T M` (with
  `t.traces = some T`) are the same set of final states.
* `corpus_closure_certs` (one kernel `decide`): all 60 x86-TSO-covered corpus tests pass the
  certificate. The 8 loose corners do not (they tear, or need `Weak9`), and are not covered.
* `corpus_tso_verdicts_any_domain`: for those 60 tests the recorded SC, TSO and XL verdicts hold
  for the axiomatic final states over **every** value domain, not only `Test.domain`. This
  discharges, for the corpus, the informal argument that the bounded domain iteration suffices
  (which the five `xadd`/`inc` tests relied on).

Not covered: the **operational** TSO machine (`OpReach`) is still stated over `Test.traces`;
its outcomes equal axiomatic TSO's over those traces (`TsoVerdicts.op_eq_ax`), but there is no
`OpReachAny` closure theorem.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- **Domain closure.** A test that passes the closure certificate loses no final state of any
model contained in XL by fixing its value domain to `Test.domain`. -/
theorem closure_of_cert {t : Test} (hc : t.closureCert = true) {M : Exec → Prop}
    (hM : ∀ x, M x → x.Xl) {f : Final} (h : AxReachAny t M f) :
    ∃ T, t.traces = some T ∧ AxReach t T M f :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.closure_of_cert hc hM h

/-- Over `Test.domain` is over some domain. -/
theorem axReachAny_of_traces {t : Test} {T : List (List XTrace)} (hT : t.traces = some T)
    {M : Exec → Prop} {f : Final} (h : AxReach t T M f) : AxReachAny t M f :=
  ⟨t.domain, T, hT, h⟩

/-- **For a certified test the domain does not matter.** -/
theorem axReachAny_iff {t : Test} (hc : t.closureCert = true) {T : List (List XTrace)}
    (hT : t.traces = some T) {M : Exec → Prop} (hM : ∀ x, M x → x.Xl) (f : Final) :
    AxReachAny t M f ↔ AxReach t T M f := by
  refine ⟨fun h => ?_, axReachAny_of_traces hT⟩
  obtain ⟨T', hT', h'⟩ := closure_of_cert hc hM h
  rw [hT] at hT'
  cases hT'
  exact h'

/-- SC, x86-TSO and XL are contained in XL. -/
theorem sc_sub_xl : ∀ x : Exec, x.Sc → x.Xl := fun x h => x.xl_of_tso (x.tso_of_sc h)

theorem tso_sub_xl : ∀ x : Exec, x.Tso → x.Xl := fun x h => x.xl_of_tso h

theorem xl_sub_xl : ∀ x : Exec, x.Xl → x.Xl := fun _ h => h

/-- **Every x86-TSO-covered corpus test passes the closure certificate.** -/
theorem corpus_closure_certs : ∀ t ∈ Corpus.all, t.coverage = .tso → t.closureCert = true :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.corpus_certs

/-- **The verdicts hold over every value domain**: for every x86-TSO-covered corpus test, the
recorded TSO, SC and XL verdicts hold for the axiomatic final states over traces extracted with
any value domain, and some SC execution exists. -/
theorem corpus_tso_verdicts_any_domain :
    ∀ t ∈ Corpus.all, t.coverage = .tso →
      (∀ v, t.tso = some v → v.Holds t (AxReachAny t Exec.Tso)) ∧
      (∀ v, t.sc = some v → v.Holds t (AxReachAny t Exec.Sc)) ∧
      t.xl.Holds t (AxReachAny t Exec.Xl) ∧ (∃ f, AxReachAny t Exec.Sc f) := by
  intro t ht hc
  obtain ⟨T, hT, hv⟩ := corpus_tso_verdicts t ht hc
  have hcert := corpus_closure_certs t ht hc
  have eTso : AxReachAny t Exec.Tso = AxReach t T Exec.Tso :=
    funext fun f => propext (axReachAny_iff hcert hT tso_sub_xl f)
  have eSc : AxReachAny t Exec.Sc = AxReach t T Exec.Sc :=
    funext fun f => propext (axReachAny_iff hcert hT sc_sub_xl f)
  have eXl : AxReachAny t Exec.Xl = AxReach t T Exec.Xl :=
    funext fun f => propext (axReachAny_iff hcert hT xl_sub_xl f)
  rw [eTso, eSc, eXl]
  exact ⟨hv.tso_ax, hv.sc_ax, hv.xl_ax, hv.sc_some⟩

end Silmaril.X86.MemoryModel.Litmus
