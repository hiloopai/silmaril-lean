module

public import Silmaril.X86.Concurrency.Cir.Tv.Marked.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvMarked

/-!
# Translation validation of marked C threads: what is proved

All statements are PROVED with the standard axioms. The proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/TvMarked.lean`.

* `mtvRun_sound`: **trace refinement per marked thread.** Suppose `mtvRun th st c = some K`.
  Take any domain whose values fit in 32 bits (needed only if the certificate reads memory),
  any fuel and any x86 trace of the marked thread (`CThread.traces`: the segments run by the
  extractor, with each marker call as its control event and, for a spawned thread, its start
  and end events). Then there is a CIR run of `c.body` over the same domain such that:
  * the trace's actions, up to `normActs`, are the CIR thread's lowered actions (`Thread.acts`,
    start and end included);
  * the final registers are equal outside `K`.
* `CTest.refines`: **refinement per test.** Every x86 behaviour of a C test, under any
  axiomatic model, is a CIR behaviour over the test's domain with the same witness value.
* `CTest.transfer_of_allOk`: the Boolean `CTest.allOk` gives `CTest.Transfer`:
  * the refinement;
  * the recorded SC, TSO and XL verdicts for the CIR program;
  * the recorded TSO verdict under operational TSO (`OpBehavIn`, control bytes mapped);
  * a nonempty SC behaviour set;
  * every `forbidden` verdict transferred to the x86 code.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86.Litmus (Trace)

/-- **A marked thread is sound** (trace refinement per thread). -/
theorem mtvRun_sound {th : CThread} {st : Stubs} {c : MCert} {K : List Reg}
    (h : mtvRun th st c = some K) {dom : List Nat} (hdom : c.reads = true → ∀ v ∈ dom, v < 2 ^ 32)
    {i fuel : Nat} {trs : List Trace} (hx : th.traces st i dom fuel = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (c.body (th.marks st)) Regs.zero,
      normActs tr.acts = (⟨c.body (th.marks st), th.spawned⟩ : Thread).acts i p.1 ∧
        ∀ r, r ∉ K → tr.final.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvMarked.mtvRun_sound h hdom hx

/-- **Refinement of a validated C test.** -/
theorem CTest.refines {c : CTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : c.XBehav M f) :
    ∃ f', BehavIn c.prog c.dom M f' ∧ c.test.witness.eval f' = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvMarked.CTest.refines h hd hf

/-- **Everything a validated C test gives.** -/
theorem CTest.transfer_of_allOk {c : CTest} (h : c.allOk = true) : c.Transfer :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvMarked.CTest.transfer_of_allOk h

end Silmaril.X86.Concurrency.Cir.Tv
