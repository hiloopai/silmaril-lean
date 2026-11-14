module

public import Silmaril.X86.Concurrency.Cir.C11.Corpus.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# Proofs: the litmus byte check on the compiled SB+ra objects

The C11 objects of `examples/litmus-c` are not in the corpus of `Silmaril.X86.MemoryModel`, so
`corpus_tso_checks`
does not cover them. Their x86 tests (`C11Test.tv.test`) still pass the litmus byte-level check
`Test.checkTsoBytes` (extract the traces from the bytes, enumerate candidate executions, compare
with the recorded TSO, SC and XL verdicts); the kernel evaluates it here. `Story.C11` uses this to
state the *allowed* SB+ra verdict on the compiled bytes, which no CIR theorem can give (an
allowed verdict does not transfer from CIR to the bytes). `allowed_checks` runs the same check on
every object whose x86 verdict is `allowed`, so every C11 object has an x86 verdict
on its bytes in both directions.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Story

open Silmaril.X86.Concurrency.Cir

set_option maxRecDepth 100000

theorem sbRa_gcc_checkTsoBytes : C11.Corpus.«SB+ra@gcc».tv.test.checkTsoBytes = true := by
  decide +kernel

theorem sbRa_clang_checkTsoBytes : C11.Corpus.«SB+ra@clang».tv.test.checkTsoBytes = true := by
  decide +kernel

open Silmaril.X86.MemoryModel.Litmus (Verdict) in
/-- **Every x86-allowed object passes the byte check**: each of the 63 objects whose
recorded XL verdict is `allowed` (SB with `na`, `rlx` and `ra` accesses for both compilers,
`LB+na@gcc` and `Counter+na@clang`, eight in all) also has the TSO verdict `allowed` and passes
`checkTsoBytes`. One kernel evaluation over the corpus (about 13 s); the forbidden objects are
skipped by the `||`. -/
theorem allowed_checks : (C11.Corpus.all.all fun c => c.tv.test.xl != Verdict.allowed ||
    (c.tv.test.tso == some Verdict.allowed && c.tv.test.checkTsoBytes)) = true := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Story
