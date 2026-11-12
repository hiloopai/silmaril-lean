module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Check19

/-!
# Round 7, REH route 2: the site check on the whole script

The twenty kernel slices `Check00`–`Check19` cover the fixed wasm-3.0 script (976 top-level
definitions, `fixed_length_le`). Put together:

* `itemsOk_fixed`: every top-level definition passes `itemOk sigFixed`. So every signature entry
  agrees with the script, every `good` type is export-free given the others, and every
  definition, relation and type reachable from `Step` has no failing site outside the binding
  sites of rules.
* `bindSites_fixed`: the binding sites are exactly six, all in rules of `Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- The script has at most `20 * 50` top-level definitions. -/
theorem fixed_length_le : fixed.length ≤ 50 * 20 := by
  decide +kernel

/-- A list is the concatenation of its slices of length `n`. -/
theorem eq_flatten_slices {α : Type} (n : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ n * k →
      l = ((List.range k).map fun i => (l.drop (n * i)).take n).flatten
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    simp [this]
  | k + 1, l, h => by
    have hk : (l.drop n).length ≤ n * k := by
      rw [List.length_drop, Nat.mul_succ] at *
      omega
    have ih := eq_flatten_slices n k (l.drop n) hk
    rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
    conv_lhs => rw [← List.take_append_drop n l]
    congr 1
    conv_lhs => rw [ih]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-- `bindSitesL` distributes over concatenation. -/
theorem bindSitesL_append (S : Sig) :
    ∀ a b : List Def, bindSitesL S (a ++ b) = bindSitesL S a ++ bindSitesL S b
  | [], _ => by simp [bindSitesL]
  | d :: a, b => by
    simp only [List.cons_append, bindSitesL, bindSitesL_append S a b, List.append_assoc]

/-- `bindSitesL` of a concatenation of lists. -/
theorem bindSitesL_flatten (S : Sig) :
    ∀ L : List (List Def), bindSitesL S L.flatten = (L.map (bindSitesL S)).flatten
  | [] => by simp [bindSitesL]
  | a :: L => by
    rw [List.flatten_cons, bindSitesL_append, bindSitesL_flatten S L, List.map_cons,
      List.flatten_cons]

/-- The twenty slices of the script. -/
theorem range20 : List.range 20 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    18, 19] := rfl

/-- **Every top-level definition of the script passes the site check.** -/
theorem itemsOk_fixed : fixed.all (itemOk sigFixed) = true := by
  rw [eq_flatten_slices 50 20 fixed fixed_length_le, List.all_flatten, range20]
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul,
    check00.1, check01.1, check02.1, check03.1, check04.1, check05.1, check06.1, check07.1,
    check08.1, check09.1, check10.1, check11.1, check12.1, check13.1, check14.1, check15.1,
    check16.1, check17.1, check18.1, check19.1, Bool.and_self, Nat.mul_zero]

/-- **The binding sites of the script**: six top-level positive premises, in the three
`call_ref` rules of `Step` that call a function instance. -/
theorem bindSites_fixed :
    bindSitesL sigFixed fixed =
      [("Step", "call_ref-func", 3), ("Step", "call_ref-hostfunc-res", 2),
        ("Step", "call_ref-hostfunc-div", 1)] := by
  rw [eq_flatten_slices 50 20 fixed fixed_length_le, bindSitesL_flatten, range20]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Nat.reduceMul,
    check00.2, check01.2, check02.2, check03.2, check04.2, check05.2, check06.2, check07.2,
    check08.2, check09.2, check10.2, check11.2, check12.2, check13.2, check14.2, check15.2,
    check16.2, check17.2, check18.2, check19.2, List.nil_append, List.append_nil, Nat.mul_zero]

/-- **The reachable types that may hold a module record**: the reachable type names outside
`sigFixed.good`. (The type parameter `X` of `list` is in `good`.) -/
theorem reachBad_fixed :
    (Script.stepReach.filter fun p => p.1 == 2 && !sigFixed.good.contains p.2).map (·.2) =
      ["config", "expr", "frame", "funccode", "funcinst", "hostcallresult", "instr",
        "moduleinst", "state", "store"] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
