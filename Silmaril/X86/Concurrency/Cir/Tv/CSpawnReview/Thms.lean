module

public import Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.CSpawn.Thms
public import Silmaril.X86.Concurrency.Cir.Litmus.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview

/-!
# Spawn/join: what is proved

All PROVED with the standard axioms; the proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/TvCSpawnReview.lean`.

* `mutants_ok`: every C-test mutant of `CSpawnReview.mutants` gets the expected answer. A
  dropped or shifted marker cut, or a certificate checked against another program's bytes, is
  rejected by `tvOk`. A relabelled stub, a child not marked spawned, or a control given the
  forbidden verdict is rejected by `allOk`. Swapped spawn/join stubs pass `tvOk` (the marks are
  trusted) and are rejected by `allOk`.
* `sbKids_verdicts`, `sbKidsJoin_verdicts`: SB between two spawned children is allowed under
  TSO and XL, for all behaviours, and forbidden under SC over the domain. Spawn and join do not
  make the program SC.
* `swHb_nonempty`: some execution has a `swHb` edge, so `Exec.swHb_*` and `Exec.*S_iff` are
  not about an empty relation.
* `end_finished_satisfiable`: the hypotheses of `end_finished` hold for the events of
  `MP+join`, with an initial end byte `0`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview

open Silmaril.X86.Concurrency.Cir

/-- **Every mutant gets the expected answer.** -/
theorem mutants_ok : ∀ m ∈ mutants, m.ok = true :=
  fun m hm => List.all_eq_true.mp Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.mutants_ok m hm

/-- **SB between spawned children**: TSO- and XL-allowed, SC-forbidden. -/
theorem sbKids_verdicts : sbKids.Verdicts :=
  verdicts_of_check Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.sbKids_check

/-- **SB between spawned children, then joined**: TSO- and XL-allowed, SC-forbidden. -/
theorem sbKidsJoin_verdicts : sbKidsJoin.Verdicts :=
  verdicts_of_check Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.sbKidsJoin_check

/-- **`swHb` is not empty.** -/
theorem swHb_nonempty : ∃ a b, swEx.swHb a b = true :=
  ⟨_, _, Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.swEx_swHb⟩

/-- **The hypotheses of `end_finished` are satisfiable.** -/
theorem end_finished_satisfiable :
    CtlOk esJoin 1 ∧ Silmaril.X86.MemoryModel.OpAx.ThreadsOk esJoin ∧
      (fun _ => some 0 : Silmaril.X86.MemoryModel.Tso.Mem) (endAddr 1) ≠ some 1 :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.esJoin_ctlOk,
    Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview.esJoin_threadsOk, by simp⟩

end Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview
