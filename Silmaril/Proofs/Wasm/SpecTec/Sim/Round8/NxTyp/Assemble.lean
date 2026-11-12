module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckTyp0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckTyp1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckTyp2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckQuant0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckQuant1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.CheckQuant2

/-!
# Round 8, typing across erasure without a swap set: the checks on the whole script

The three slices of each check give `nTypMap_fixed` and `nRelQuants_fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.Wasm.SpecTec.Sim
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

theorem all_three {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (h₀ : (l.take k).all p = true) (h₁ : ((l.drop k).take k).all p = true)
    (h₂ : (l.drop (2 * k)).all p = true) : l.all p = true := by
  have e : l = l.take k ++ ((l.drop k).take k ++ l.drop (2 * k)) := by
    rw [two_mul, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  rw [e, List.all_append, List.all_append, h₀, h₁, h₂]
  rfl

/-- **Every type over `tyB` is checked.** -/
theorem nTypMap_fixed : nTypMap Round7.TypAgree.tyB (typsOfDefs fixed) = true :=
  all_three _ _ 70 nTypMap_s0 nTypMap_s1 nTypMap_s2

/-- **Every quantifier type of a rule `Step` reaches is checked.** -/
theorem nRelQuants_fixed : nRelQuants Round7.TypAgree.tyB (relsOfDefs fixed) = true :=
  all_three _ _ 42 nRelQuants_s0 nRelQuants_s1 nRelQuants_s2

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
