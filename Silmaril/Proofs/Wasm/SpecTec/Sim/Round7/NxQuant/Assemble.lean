module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.Check09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxQuant.AliasCheck

/-!
# Round 7, REH route 2: the type side conditions on the whole script

The ten kernel slices `Check00`–`Check09` (100 top-level definitions each) give
`typVtItems_fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (Sig eq_flatten_slices fixed_length_le)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (sigX)

theorem typVtItems_append (S : Sig) :
    ∀ a b : List Def, typVtItems S (a ++ b) = (typVtItems S a && typVtItems S b)
  | [], _ => by simp [typVtItems]
  | d :: a, b => by
    simp only [List.cons_append, typVtItems, typVtItems_append S a b, Bool.and_assoc]

theorem typVtItems_flatten (S : Sig) :
    ∀ L : List (List Def), typVtItems S L.flatten = (L.map (typVtItems S)).all id
  | [] => by simp [typVtItems]
  | a :: L => by
    rw [List.flatten_cons, typVtItems_append, typVtItems_flatten S L, List.map_cons,
      List.all_cons, id]

theorem fixed_length_le100' : fixed.length ≤ 100 * 10 := by
  have := fixed_length_le
  omega

/-- **The whole script passes the type side conditions.** -/
theorem typVtItems_fixed : typVtItems sigX fixed = true := by
  rw [eq_flatten_slices 100 10 fixed fixed_length_le100', typVtItems_flatten]
  simp only [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul, Nat.mul_zero, id, vt00, vt01,
    vt02, vt03, vt04, vt05, vt06, vt07, vt08, vt09, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
