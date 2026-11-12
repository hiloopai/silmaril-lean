module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.YCheck19

/-!
# Round 8, REH route 2: the clause check on the whole script

The twenty kernel slices `YCheck00`–`YCheck19` (50 top-level definitions each) give
`yItems_fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (eq_flatten_slices fixed_length_le)

theorem yItems_append : ∀ a b : List Def, yItems (a ++ b) = (yItems a && yItems b)
  | [], _ => by simp [yItems]
  | d :: a, b => by simp only [List.cons_append, yItems, yItems_append a b, Bool.and_assoc]

theorem yItems_flatten : ∀ L : List (List Def), yItems L.flatten = (L.map yItems).all id
  | [] => by simp [yItems]
  | a :: L => by
    rw [List.flatten_cons, yItems_append, yItems_flatten L, List.map_cons, List.all_cons, id]

/-- **Every reachable clause passes the clause check, and every `gdE` definition has a parameter
entry.** -/
theorem yItems_fixed : yItems fixed = true := by
  rw [eq_flatten_slices 50 20 fixed fixed_length_le, yItems_flatten]
  simp only [show List.range 20 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
      18, 19] from rfl, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul,
    Nat.mul_zero, id, y00, y01, y02, y03, y04, y05, y06, y07, y08, y09, y10, y11, y12, y13, y14,
    y15, y16, y17, y18, y19, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
