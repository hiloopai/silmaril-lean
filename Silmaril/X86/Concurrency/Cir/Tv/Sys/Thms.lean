module

public import Silmaril.X86.Concurrency.Cir.Tv.Sys.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvSys

/-!
# Bounded trace-inclusion translation validation: what is proved

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/TvSys.lean`):

* `FTest.refines`: if `tvOk`, every bounded x86 behaviour of a futex C test (under **any**
  `M : Exec → Prop`) is a CIR behaviour with the same final memory and witness value.
* `FTest.cbehav_iff`: the CIR behaviours are `BBehavIn` (with blocking) or `BehavIn`.
* `FTest.transfer_of_allOk`: `allOk` gives `FTest.Transfer` (refinement, the recorded CIR
  verdicts, an SC behaviour, and every `forbidden` verdict for the x86 code).
* `FTest.witness_allowed`: `witnessOk ks` (one trace combination) gives the witness as a CIR
  behaviour under SC, and so under TSO and XL. `FTest.sched_allowed`: the same from
  `schedOk ks sch` (one combination and a schedule, no enumeration).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86.MemoryModel.Litmus (Final)

/-- **Refinement of a futex C test** (bounded x86 behaviours ⊆ CIR behaviours). -/
theorem FTest.refines {c : FTest} (h : c.tvOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : c.XBehav M f) :
    ∃ f', c.CBehav M f' ∧ f'.mem = f.mem ∧ c.test.witness.eval f' = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSys.refines h hf

/-- **The converse**: if `coverOk`, every CIR behaviour of a futex C test
(under any `M`) is a bounded x86 behaviour with the same final memory and witness value. -/
theorem FTest.realizes {c : FTest} (h : c.coverOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : c.CBehav M f) :
    ∃ f', c.XBehav M f' ∧ f'.mem = f.mem ∧ c.test.witness.eval f' = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSys.realizes h hf

/-- With `coverOk`, an `allowed` CIR verdict holds for the x86 code. -/
theorem FTest.x86_allowed {c : FTest} (h : c.coverOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} (ha : c.test.Allowed (c.CBehav M)) :
    c.test.Allowed (c.XBehav M) := by
  obtain ⟨f, hf, hw⟩ := ha
  obtain ⟨f', hx, -, he⟩ := FTest.realizes h hf
  exact ⟨f', hx, he ▸ hw⟩

/-- The CIR behaviours of a validated futex C test are the program's (blocking) behaviours. -/
theorem FTest.cbehav_iff {c : FTest} (h : c.tvOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} :
    c.CBehav M f ↔ if c.blk then BBehavIn c.prog c.dom M f else BehavIn c.prog c.dom M f :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSys.cbehav_iff h

/-- **Everything a validated futex C test gives.** -/
theorem FTest.transfer_of_allOk {c : FTest} (h : c.allOk = true) : c.Transfer :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSys.transfer_of_allOk h

/-- **A witness combination gives an `allowed` verdict** under every model (SC ⊑ TSO ⊑ XL). -/
theorem FTest.witness_allowed {c : FTest} {ks : List Nat} (h : c.witnessOk ks = true)
    (M : Silmaril.X86.MemoryModel.Litmus.Model) : c.test.Allowed (c.CBehav M.Holds) := by
  obtain ⟨f, hf, hw⟩ := Silmaril.Proofs.X86.Concurrency.Cir.TvSys.witness_sc h
  refine ⟨f, Silmaril.X86.MemoryModel.Litmus.axReach_mono (fun x hx => ?_) hf, hw⟩
  cases M
  · exact hx
  · exact sc_le_tso x hx
  · exact tso_le_xl x (sc_le_tso x hx)

/-- **A schedule witness gives an `allowed` verdict** under every model (SC ⊑ TSO ⊑ XL). -/
theorem FTest.sched_allowed {c : FTest} {ks sch : List Nat} (h : c.schedOk ks sch = true)
    (M : Silmaril.X86.MemoryModel.Litmus.Model) : c.test.Allowed (c.CBehav M.Holds) := by
  obtain ⟨f, hf, hw⟩ := Silmaril.Proofs.X86.Concurrency.Cir.TvSys.sched_sc h
  refine ⟨f, Silmaril.X86.MemoryModel.Litmus.axReach_mono (fun x hx => ?_) hf, hw⟩
  cases M
  · exact hx
  · exact sc_le_tso x hx
  · exact tso_le_xl x (sc_le_tso x hx)

end Silmaril.X86.Concurrency.Cir.Tv
