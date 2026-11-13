module

public import Silmaril.X86.MemoryModel.Litmus.Closure.Defs
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs

/-!
# Domain closure: the corpus certificates

One kernel `decide` (`decide +kernel`) over the 60 x86-TSO-covered corpus
tests: each passes `Test.closureCert`. For `Silmaril/X86/MemoryModel/Litmus/Closure/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Closure

open Silmaril.X86.MemoryModel.Litmus

set_option maxRecDepth 100000 in
theorem tso_certs : (Corpus.all.filter (·.coverage == .tso)).all Test.closureCert = true := by
  decide +kernel

theorem corpus_certs : ∀ t ∈ Corpus.all, t.coverage = .tso → t.closureCert = true := by
  intro t ht hc
  exact List.all_eq_true.mp tso_certs t (List.mem_filter.mpr ⟨ht, by simp [hc]⟩)

end Silmaril.Proofs.X86.MemoryModel.Litmus.Closure
