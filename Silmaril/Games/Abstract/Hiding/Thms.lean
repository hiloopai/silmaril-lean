module

public import Silmaril.Games.Abstract.Hiding.Defs
public import Silmaril.Games.Abstract.Game.Thms
import Silmaril.Proofs.Games.Abstract.Hiding.Basic

/-!
# Partial game morphisms: theorems

* `gc_hide_pull`: hiding is left adjoint to pulling back. Hence `hide` is
  monotone and preserves joins, and `pull` preserves meets.
* `pull_toPHom`: along a total morphism, pulling back is `comap`.
-/

public section

namespace Silmaril.Games.Abstract.TraceModel

universe u v

variable {G : Game.{u}} {H : Game.{v}}

/-- Membership in a pullback along a partial morphism. -/
theorem mem_pull {f : G.PHom H} {T : TraceModel H} {s : List G.Move} :
    s ∈ pull f T ↔ s ∈ G.Legal ∧ s.filterMap f.map ∈ T := Iff.rfl

/-- The visible part of a play of `T` is a play of `hide f T`. -/
theorem filterMap_mem_hide {f : G.PHom H} {T : TraceModel G} {s : List G.Move} (hs : s ∈ T) :
    s.filterMap f.map ∈ hide f T :=
  subset_generate ⟨s, hs, rfl⟩ (f.legal (T.closed.legal hs))

/-- Hiding is left adjoint to pulling back. -/
theorem gc_hide_pull (f : G.PHom H) : GaloisConnection (hide f) (pull f) :=
  Silmaril.Proofs.Games.Abstract.Hiding.gc_hide_pull f

/-- Hiding is monotone. -/
theorem hide_mono (f : G.PHom H) : Monotone (hide f) := (gc_hide_pull f).monotone_l

/-- Pulling back is monotone. -/
theorem pull_mono (f : G.PHom H) : Monotone (pull f) := (gc_hide_pull f).monotone_u

/-- Hiding preserves joins. -/
theorem hide_sSup (f : G.PHom H) (S : Set (TraceModel G)) :
    hide f (sSup S) = ⨆ T ∈ S, hide f T := (gc_hide_pull f).l_sSup

/-- Along a total morphism, pulling back is `comap`. -/
theorem pull_toPHom (f : G.Hom H) (T : TraceModel H) : pull f.toPHom T = comap f T :=
  Silmaril.Proofs.Games.Abstract.Hiding.pull_toPHom f T

end Silmaril.Games.Abstract.TraceModel
