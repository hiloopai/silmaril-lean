module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check19
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check20
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check21
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check22
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check23
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check24
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check25
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check26
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check27
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check28
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check29
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check30
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check31
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check32
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check33
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check34
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check35
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check36
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check37
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check38
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Check39

/-!
# Round 7, REH route 2: the flow check on the whole script

The forty kernel slices `Check00`–`Check39` cover the fixed wasm-3.0 script (976 top-level
definitions, at most `25 * 40`). Put together:

* `typItemsOk_fixed`: every alias, field and case entry of `sigExtra` agrees with the type
  definitions of the script (with `NxSites.itemsOk_fixed` for `sigFixed`, every entry of `sigX`
  does);
* `flowItems_fixed`: every definition and relation reachable from `Step` passes the flow check
  `NxTyped.flowItems sigX tsigFixed`, and the entries of `tsigFixed` agree with the script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (Sig eq_flatten_slices fixed_length_le)

/-- `typItemsOk` distributes over concatenation. -/
theorem typItemsOk_append (E : Sig) (names : List String) :
    ∀ a b : List Def, typItemsOk E names (a ++ b) = (typItemsOk E names a && typItemsOk E names b)
  | [], _ => by simp [typItemsOk]
  | d :: a, b => by
    simp only [List.cons_append, typItemsOk, typItemsOk_append E names a b, Bool.and_assoc]

/-- `typItemsOk` of a concatenation of lists. -/
theorem typItemsOk_flatten (E : Sig) (names : List String) :
    ∀ L : List (List Def), typItemsOk E names L.flatten = (L.map (typItemsOk E names)).all id
  | [] => by simp [typItemsOk]
  | a :: L => by
    rw [List.flatten_cons, typItemsOk_append, typItemsOk_flatten E names L, List.map_cons,
      List.all_cons, id]

/-- `flowItems` distributes over concatenation. -/
theorem flowItems_append (S : Sig) (T : TSig) :
    ∀ a b : List Def, flowItems S T (a ++ b) = flowItems S T a + flowItems S T b
  | [], _ => by simp [flowItems]
  | d :: a, b => by
    simp only [List.cons_append, flowItems, flowItems_append S T a b, Nat.add_assoc]

/-- `flowItems` of a concatenation of lists. -/
theorem flowItems_flatten (S : Sig) (T : TSig) :
    ∀ L : List (List Def), flowItems S T L.flatten = (L.map (flowItems S T)).sum
  | [] => by simp [flowItems]
  | a :: L => by
    rw [List.flatten_cons, flowItems_append, flowItems_flatten S T L, List.map_cons,
      List.sum_cons]

/-- The script has at most `25 * 40` top-level definitions. -/
theorem fixed_length_le' : fixed.length ≤ 25 * 40 := by
  have := fixed_length_le
  omega

/-- The forty slices of the script. -/
theorem range40 : List.range 40 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] := rfl

/-- **The type entries of `sigExtra` agree with the script.** -/
theorem typItemsOk_fixed : typItemsOk sigExtra extraNames fixed = true := by
  rw [eq_flatten_slices 25 40 fixed fixed_length_le', typItemsOk_flatten, range40]
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Nat.reduceMul, id,
    check00.1, check01.1, check02.1, check03.1, check04.1, check05.1, check06.1, check07.1,
    check08.1, check09.1, check10.1, check11.1, check12.1, check13.1, check14.1, check15.1,
    check16.1, check17.1, check18.1, check19.1, check20.1, check21.1, check22.1, check23.1,
    check24.1, check25.1, check26.1, check27.1, check28.1, check29.1, check30.1, check31.1,
    check32.1, check33.1, check34.1, check35.1, check36.1, check37.1, check38.1, check39.1,
    Bool.and_self, Nat.mul_zero]

/-- **The whole script passes the flow check.** -/
theorem flowItems_fixed : flowItems sigX tsigFixed fixed = 0 := by
  rw [eq_flatten_slices 25 40 fixed fixed_length_le', flowItems_flatten, range40]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceMul,
    check00.2, check01.2, check02.2, check03.2, check04.2, check05.2, check06.2, check07.2,
    check08.2, check09.2, check10.2, check11.2, check12.2, check13.2, check14.2, check15.2,
    check16.2, check17.2, check18.2, check19.2, check20.2, check21.2, check22.2, check23.2,
    check24.2, check25.2, check26.2, check27.2, check28.2, check29.2, check30.2, check31.2,
    check32.2, check33.2, check34.2, check35.2, check36.2, check37.2, check38.2, check39.2,
    Nat.add_zero, Nat.mul_zero]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
