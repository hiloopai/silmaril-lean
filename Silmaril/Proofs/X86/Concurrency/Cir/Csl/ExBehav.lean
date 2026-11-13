module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Litmus.Thms

/-!
# CSL over CIR: the example has axiomatic behaviours

`Csl.Ex.xl_behav` says every axiomatic XL behaviour of
`Csl.Ex.prog` ends with the owned cells at `1` and `2`; that is vacuous unless such behaviours
exist. The axiomatic enumerator, run on the example as a CIR litmus test, finds an SC (hence
TSO and XL) behaviour (`exAll_check`, the `sc_some` part of `CTest.check`), and independently
agrees with the bridge: an unwritten owned cell (`exLost`) and a lost counter increment
(`exCtr`) are forbidden under every model over the test's domain.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.ExBehav

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Lit (shell)

/-- The example with the expected final state, `allowed` under SC, TSO and XL. -/
def exAll : CTest :=
  ⟨{ shell "Csl.Ex" "owned cells next to a lock xadd counter"
      (.and (.atom (.mem 0 8 1)) (.and (.atom (.mem 8 8 2)) (.atom (.mem 16 8 2)))) .allowed with
      locs := Csl.Ex.prog.locs },
    Csl.Ex.prog.threads⟩

/-- Thread 0's owned cell left at `0`: forbidden. -/
def exLost : CTest :=
  ⟨{ shell "Csl.Ex+lost" "an owned cell not written" (.atom (.mem 0 8 0)) .forbidden with
      locs := Csl.Ex.prog.locs },
    Csl.Ex.prog.threads⟩

/-- The counter at `1` (a lost `lock xadd`): forbidden. -/
def exCtr : CTest :=
  ⟨{ shell "Csl.Ex+ctr1" "a lost counter increment" (.atom (.mem 16 8 1)) .forbidden with
      locs := Csl.Ex.prog.locs },
    Csl.Ex.prog.threads⟩

theorem exAll_prog : exAll.prog = Csl.Ex.prog := rfl

theorem exAll_check : exAll.check = true := by decide +kernel

theorem exLost_check : exLost.check = true := by decide +kernel

theorem exCtr_check : exCtr.check = true := by decide +kernel

/-- `Csl.Ex.prog` has an axiomatic SC behaviour. -/
theorem some_sc : ∃ f, Behav Csl.Ex.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f := by
  obtain ⟨f, hf⟩ := (verdicts_of_check exAll_check).sc_some
  exact ⟨f, behavIn_behav hf⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.ExBehav
