module

public import Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs
public import Silmaril.X86.Concurrency.Cir.C11.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus

/-!
# C11 litmus objects on CIR: theorems

PROVED (standard axioms only; one kernel `decide` per test in
`Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus`):

* `corpus_holds`: every one of the 63 validated objects of `examples/litmus-c` (8 shapes × 4
  variants × 2 compilers, less `Counter+na@gcc`) satisfies `C11Test.Holds`. In particular, for
  each object: its x86 behaviours refine its CIR program's; every XL-consistent execution of the
  CIR program is RC11-consistent with the C11 modes of the source; its RC11 verdict is the one
  recorded by hand (now computed); and a forbidden RC11 verdict holds for the x86 bytes.
* `corpus_stronger`: the tests on which x86 is strictly stronger than RC11 (XL forbids a witness
  that an RC11-consistent execution satisfies) are exactly the listed ones: MP+rlx, IRIW+rlx/ra and
  2+2W+rlx/ra, and the racy plain variants of MP, IRIW and 2+2W (undefined behaviour in C11).
* `corpus_mapOk`, `corpus_x86_rc11`: every object's CIR program is `c11MapOk`, so
  the general mapping theorem (`C11Test.x86_rc11`, not the per-test enumeration) gives that every
  tame XL behaviour of its bytes has the witness value of an RC11 behaviour.
* `cirTsoRc11_nonvacuous`, `sbSc_forbidden_x86`: the general theorem on a weak
  behaviour and on a forbidden one. On `SB+rlx@gcc` a TSO-consistent candidate meeting every
  hypothesis of `Task.cirTsoRc11` has the store-buffering outcome `r0 = r1 = 0` (which SC
  forbids), and the theorem makes it RC11-consistent; on `SB+sc@gcc` RC11 forbids that outcome,
  so the general `C11Test.forbidden_x86` forbids it for the bytes under tame XL.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11.Corpus

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (XTrace AxReach Final Verdict units rmwPairs finalAx)

/-- **Every validated C11 object satisfies its statement.** -/
theorem corpus_holds : ∀ c ∈ all, c.Holds := fun c hc =>
  C11Test.holds_of_check (Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus.all_ok c hc)

/-- **Where x86 is strictly stronger than RC11** (XL forbids the witness, RC11 allows it). -/
theorem corpus_stronger :
    (all.filter (·.stronger)).map (·.tv.test.name) =
      ["MP+na@gcc", "MP+na@clang", "MP+rlx@gcc", "MP+rlx@clang", "IRIW+na@gcc",
        "IRIW+na@clang", "IRIW+rlx@gcc", "IRIW+rlx@clang", "IRIW+ra@gcc", "IRIW+ra@clang",
        "2+2W+na@gcc", "2+2W+na@clang", "2+2W+rlx@gcc", "2+2W+rlx@clang", "2+2W+ra@gcc",
        "2+2W+ra@clang"] := by
  decide

/-- Every object's CIR program is in the fragment and respects the mapping. -/
theorem corpus_mapOk : ∀ c ∈ all, c.prog.c11MapOk = true :=
  List.all_eq_true.mp (by decide)

/-- **The general mapping theorem on the corpus**: every tame XL behaviour of an object's bytes
has the witness value of an RC11 behaviour of its CIR program. -/
theorem corpus_x86_rc11 {c : C11Test} (hc : c ∈ all) {T : List (List XTrace)}
    (hT : c.tv.test.traces = some T) {f : Final}
    (hf : AxReach c.tv.test T (fun x => x.Xl ∧ x.Tame) f) :
    ∃ f', c.Rc f' ∧ c.tv.test.witness.eval f' = c.tv.test.witness.eval f := by
  have h := Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus.all_ok c hc
  simp only [C11Test.check, Bool.and_eq_true] at h
  exact C11Test.x86_rc11 h.1.1.1.1.1 h.1.1.1.1.2 (corpus_mapOk c hc) hT hf

/-- `SB+rlx@gcc` is in the corpus. -/
theorem sbRlx_mem : «SB+rlx@gcc» ∈ all :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- `SB+sc@gcc` is in the corpus. -/
theorem sbSc_mem : «SB+sc@gcc» ∈ all := by
  repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)

/-- **The hypotheses of `Task.cirTsoRc11` meet a weak behaviour**: `SB+rlx@gcc` is `c11MapOk`
and has a well-formed TSO-consistent candidate over its units with the store-buffering outcome
`r0 = r1 = 0` (forbidden under SC); `cirTsoRc11` makes it RC11-consistent. -/
theorem cirTsoRc11_nonvacuous :
    «SB+rlx@gcc».prog.c11MapOk = true ∧
    ∃ trs, List.Forall₂ (· ∈ ·) trs («SB+rlx@gcc».prog.traces «SB+rlx@gcc».dom) ∧ ∃ x : Exec,
      x.evs = (units trs).map Prod.fst ∧ x.rmw = rmwPairs ((units trs).map Prod.fst) ∧
      x.Wf = true ∧ x.Tso ∧ «SB+rlx@gcc».prog.Rc11 x ∧
      «SB+rlx@gcc».tv.test.witness.eval (finalAx «SB+rlx@gcc».prog.memTest trs x) = true := by
  have hm := corpus_mapOk _ sbRlx_mem
  obtain ⟨f, hf, hw⟩ := (corpus_holds _ sbRlx_mem).cir_tso .allowed rfl
  obtain ⟨trs, htr, x, hx, hr, hwf, _, ht, rfl⟩ := hf
  exact ⟨hm, trs, htr, x, hx, hr, hwf, ht, cirTsoRc11 _ _ hm trs htr x hx hr hwf ht, hw⟩

/-- **A negative instance of the general theorem**: RC11 forbids `r0 = r1 = 0` for `SB+sc`, so
`C11Test.forbidden_x86` forbids it for the `SB+sc@gcc` bytes under tame XL. -/
theorem sbSc_forbidden_x86 : ∃ T, «SB+sc@gcc».tv.test.traces = some T ∧
    Verdict.forbidden.Holds «SB+sc@gcc».tv.test
      (AxReach «SB+sc@gcc».tv.test T (fun x => x.Xl ∧ x.Tame)) := by
  have h := Silmaril.Proofs.X86.Concurrency.Cir.C11Corpus.all_ok _ sbSc_mem
  simp only [C11Test.check, Bool.and_eq_true] at h
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp h.1.1.1.2
  have hr : CVerdict.forbidden.Holds «SB+sc@gcc» := (corpus_holds _ sbSc_mem).rc11
  exact ⟨T, hT, C11Test.forbidden_x86 h.1.1.1.1.1 h.1.1.1.1.2 (corpus_mapOk _ sbSc_mem) hT hr.2⟩

end Silmaril.X86.Concurrency.Cir.C11.Corpus
