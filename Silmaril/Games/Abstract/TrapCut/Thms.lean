module

public import Silmaril.Games.Abstract.TrapCut.Defs
import Silmaril.Proofs.Games.Abstract.TrapCut.Basic

/-!
# Trap ≈ divergence with trap moves: theorems

* `firstCut_eq_none_iff`, `firstCut_eq_some`: `firstCut T s` is the prefix of
  `s` before its first `T` move, if any.
* `cut_false`, `cutEquiv_false_iff`: with no trap moves, the cut is the
  collapse of `Silmaril.Games.Abstract.Outcome`, and cut equivalence is coarse
  equivalence.
* `TagEquiv.cut`: the sensitive (tagged) equivalence implies the trap ≈
  divergence one.
* `exists_cut_not_tag`: a call answered by a trap move, against a call on
  which the component loops silently. They are cut-equivalent but not
  tag-equivalent.
-/

public section

namespace Silmaril.Games.Abstract

universe u

/-- No trap move: no cut. -/
theorem firstCut_eq_none_iff {M : Type u} {T : M → Prop} {s : List M} :
    firstCut T s = none ↔ ∀ m ∈ s, ¬ T m :=
  Silmaril.Proofs.Games.Abstract.TrapCut.firstCut_eq_none_iff

/-- The cut is the prefix before the first trap move. -/
theorem firstCut_eq_some {M : Type u} {T : M → Prop} {s p : List M}
    (h : firstCut T s = some p) : ∃ m rest, s = p ++ m :: rest ∧ T m ∧ ∀ x ∈ p, ¬ T x :=
  Silmaril.Proofs.Games.Abstract.TrapCut.firstCut_eq_some h

/-- With no trap moves, the cut is the collapse. -/
theorem cut_false {G : Game.{u}} {R : Type u} :
    Obs.cut (G := G) (R := R) (fun _ => False) = Obs.collapse :=
  Silmaril.Proofs.Games.Abstract.TrapCut.cut_false

namespace OMachine

variable {G : Game.{u}} {R : Type u} {M N : OMachine G R}

/-- With no trap moves, cut equivalence is coarse equivalence. -/
theorem cutEquiv_false_iff : M.CutEquiv (fun _ => False) N ↔ M.CoarseEquiv N := by
  simp only [CutEquiv, cobsCut, CoarseEquiv, cobs, cut_false]

/-- The sensitive equivalence implies the trap ≈ divergence one. -/
theorem TagEquiv.cut (T : G.Move → Prop) (h : M.TagEquiv N) : M.CutEquiv T N := by
  unfold CutEquiv cobsCut; rw [h]

open Silmaril.Proofs.Games.Abstract.TrapCut in
/-- A trapping answer and a silent loop: cut-equivalent, not tag-equivalent. -/
theorem exists_cut_not_tag :
    ∃ (G : Game.{0}) (T : G.Move → Prop) (M N : OMachine G PUnit),
      M.CutEquiv T N ∧ ¬ M.TagEquiv N :=
  ⟨Gt, Silmaril.Proofs.Games.Abstract.TrapCut.T, trapM, loopM, trap_loop_cut, trap_loop_not_tag⟩

end OMachine

end Silmaril.Games.Abstract
