module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs

/-!
# `CondInit` is checkable and holds on the corpus

`condInit_of`: the Boolean check `condInitB` implies `CondInit`.
`corpus_condInit`: every test of the translation-validated corpus passes it (19 of them have
memory atoms in their condition), so the hypothesis `Task.tsoRunCir` gained is not vacuous.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86.MemoryModel.Litmus (Test)
open Silmaril.X86.Concurrency.Bridge

theorem condInit_of {t : Test} (h : condInitB t = true) : CondInit t := by
  intro a n v hm j hj
  have := List.all_eq_true.mp h _ hm
  simpa using List.all_eq_true.mp this j (List.mem_range.mpr hj)

theorem corpus_condInit :
    ∀ c ∈ Silmaril.X86.Concurrency.Cir.Tv.Corpus.all, CondInit c.test := by
  have h : Silmaril.X86.Concurrency.Cir.Tv.Corpus.all.all (fun c => condInitB c.test) = true := by
    decide +kernel
  intro c hc
  exact condInit_of (List.all_eq_true.mp h c hc)

end Silmaril.Proofs.X86.Concurrency.Bridge
