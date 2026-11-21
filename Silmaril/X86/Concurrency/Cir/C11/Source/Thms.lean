module

public import Silmaril.X86.Concurrency.Cir.C11.Source.Defs
public import Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs
public import Silmaril.X86.Concurrency.Cir.C11.Mutants.Defs

/-!
# C11 tests on CIR: the modes are the source variant's (theorems)

PROVED by kernel `decide`:

* `corpus_srcModes`: every mode of every one of the 63 CIR programs is the one its C source's
  variant fixes (`C11Test.srcModesOk`), so the RC11 verdicts of `corpus_holds` are about the
  source's modes, independently of the sidecar and matcher (still not about the C program
  itself).
* Two mislabellings that `C11Test.check` **accepts** (the RC11 verdict and every recorded flag
  are unchanged) and `srcModesOk` rejects: `CoRR+ra@gcc` with its acquire loads labelled `sc`
  (`corrRaSc`), and `MP+ra@gcc` with a result-slot store labelled `rlx` (`mpRaSlotRlx`). They
  show the gap that `srcModesOk` closes: `check` constrains modes only through implementability and
  the verdict.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11

open Silmaril.X86.Concurrency.Cir

/-- **Every CIR program carries its source variant's modes.** -/
theorem Corpus.corpus_srcModes : ∀ c ∈ Corpus.all, c.srcModesOk = true := by
  decide +kernel

namespace Mutants

/-- `CoRR+ra@gcc` with both acquire loads labelled `sc`. -/
def corrRaSc : C11Test :=
  setOps (setOps Corpus.«CoRR+ra@gcc» 1 0 [.load .rax .sc 4 .wb (.lit 0x10000)]) 1 2
    [.load .rax .sc 4 .wb (.lit 0x10000)]

/-- `MP+ra@gcc` with the store of `r0` labelled `rlx`. -/
def mpRaSlotRlx : C11Test :=
  setOps Corpus.«MP+ra@gcc» 1 1 [.store .rlx 4 .wb (.lit 0x10080) (.reg .rax)]

set_option maxRecDepth 100000 in
/-- `check` accepts the `sc` mislabelling of `CoRR+ra@gcc`. -/
theorem corrRaSc_check : corrRaSc.check = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `check` accepts the `rlx` mislabelling of `MP+ra@gcc`'s result store. -/
theorem mpRaSlotRlx_check : mpRaSlotRlx.check = true := by decide +kernel

/-- **The source-mode check rejects both.** -/
theorem srcModes_rejects : corrRaSc.srcModesOk = false ∧ mpRaSlotRlx.srcModesOk = false := by
  decide +kernel

end Mutants

end Silmaril.X86.Concurrency.Cir.C11
