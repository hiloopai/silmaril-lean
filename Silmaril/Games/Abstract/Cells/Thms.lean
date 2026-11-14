module

public import Silmaril.Games.Abstract.Cells.Defs
public import Silmaril.Games.Abstract.Hiding.Thms
public import Silmaril.Games.Abstract.Game.Thms
import Silmaril.Proofs.Games.Abstract.Cells.Basic

/-!
# Exported state: theorems

* `map_ops_injective`, `map_ops_le_iff`: function-only models embed into models
  with exported cells, reflecting refinement. This holds because `Hom.ops` is
  injective on moves and reflects Opponent polarity.
* `hide_map_ops`: hiding the cell moves of an embedded function-only model
  gives it back. The square "function-only → with cells → function-only"
  commutes.
* `exists_hide_eq_ne`: observing exported state is strictly finer than
  function-only observation. Two components whose exported cell reads differ
  have the same function-only observation. So exporting a memory, global or
  table changes which programs are equivalent, and equivalence results for
  function-only modules do not transfer to modules with exported state
  without a hypothesis about the cells.
-/

public section

namespace Silmaril.Games.Abstract.TraceModel

universe u

variable {G : Game.{u}} {N : Type u} {V : N → Type u}

theorem ops_injective : Function.Injective (Game.Hom.ops (G := G) (N := N) (V := V)).map :=
  fun _ _ h => CMove.op.inj h

/-- Function-only models embed. -/
theorem map_ops_injective : Function.Injective (map (Game.Hom.ops (G := G) (N := N) (V := V))) :=
  map_injective _ ops_injective fun _ h => h

/-- The embedding reflects refinement. -/
theorem map_ops_le_iff {T U : TraceModel G} :
    map (Game.Hom.ops (N := N) (V := V)) T ≤ map Game.Hom.ops U ↔ T ≤ U :=
  map_le_map_iff _ ops_injective fun _ h => h

/-- Hiding the cells of an embedded function-only model gives it back. -/
theorem hide_map_ops (T : TraceModel G) :
    hide Game.PHom.hideCells (map (Game.Hom.ops (N := N) (V := V)) T) = T :=
  Silmaril.Proofs.Games.Abstract.Cells.hide_map_ops T

/-- Observing exported state is strictly finer than function-only
observation. -/
theorem exists_hide_eq_ne :
    ∃ (G : Game.{0}) (N : Type) (V : N → Type) (T U : TraceModel (G.withCells N V)),
      hide Game.PHom.hideCells T = hide Game.PHom.hideCells U ∧ T ≠ U :=
  open Silmaril.Proofs.Games.Abstract.Cells in
  ⟨G₀, Unit, fun _ => Bool, readsAs true, readsAs false, hide_readsAs_eq, readsAs_ne⟩

end Silmaril.Games.Abstract.TraceModel
