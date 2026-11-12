module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.AuxCheck09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxFlow.SigCheck

/-!
# Round 7, REH route 2: the side conditions on the whole script

The ten kernel slices `AuxCheck00`–`AuxCheck09` (100 top-level definitions each) give
`auxItems_fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (eq_flatten_slices fixed_length_le)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (TSig tsigFixed)

theorem auxItems_append (T : TSig) :
    ∀ a b : List Def, auxItems T (a ++ b) = (auxItems T a && auxItems T b)
  | [], _ => by simp [auxItems]
  | d :: a, b => by
    simp only [List.cons_append, auxItems, auxItems_append T a b, Bool.and_assoc]

theorem auxItems_flatten (T : TSig) :
    ∀ L : List (List Def), auxItems T L.flatten = (L.map (auxItems T)).all id
  | [] => by simp [auxItems]
  | a :: L => by
    rw [List.flatten_cons, auxItems_append, auxItems_flatten T L, List.map_cons,
      List.all_cons, id]

theorem fixed_length_le100 : fixed.length ≤ 100 * 10 := by
  have := fixed_length_le
  omega

/-- **The whole script passes the side conditions.** -/
theorem auxItems_fixed : auxItems tsigFixed fixed = true := by
  rw [eq_flatten_slices 100 10 fixed fixed_length_le100, auxItems_flatten]
  simp only [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul, Nat.mul_zero, id, aux00, aux01,
    aux02, aux03, aux04, aux05, aux06, aux07, aux08, aux09, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
