module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxErase.XCheck19

/-!
# Round 7, REH route 2: the side conditions of the erasure copy on the whole script

The twenty kernel slices `XCheck00`–`XCheck19` (50 top-level definitions each) give
`xItems_fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (eq_flatten_slices fixed_length_le)

theorem xItems_append : ∀ a b : List Def, xItems (a ++ b) = (xItems a && xItems b)
  | [], _ => by simp [xItems]
  | d :: a, b => by simp only [List.cons_append, xItems, xItems_append a b, Bool.and_assoc]

theorem xItems_flatten : ∀ L : List (List Def), xItems L.flatten = (L.map xItems).all id
  | [] => by simp [xItems]
  | a :: L => by
    rw [List.flatten_cons, xItems_append, xItems_flatten L, List.map_cons, List.all_cons, id]

/-- **Every reachable clause and rule passes the side conditions of the copy.** -/
theorem xItems_fixed : xItems fixed = true := by
  rw [eq_flatten_slices 50 20 fixed fixed_length_le, xItems_flatten]
  simp only [show List.range 20 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
      18, 19] from rfl, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul,
    Nat.mul_zero, id, x00, x01, x02, x03, x04, x05, x06, x07, x08, x09, x10, x11, x12, x13, x14,
    x15, x16, x17, x18, x19, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
