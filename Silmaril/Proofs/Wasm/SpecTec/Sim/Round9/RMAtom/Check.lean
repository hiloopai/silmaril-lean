module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.Defs

/-!
# Round 9, rm: which rules are flat (kernel checks)

On the fixed wasm-3.0 script, in every `simEnv B`:

* `pureAtoms`: every rule of `Step_pure` outside `structPure` is `atomPure`;
* `readAtoms`: every rule of `Step_read` outside `structRead` and the memory SIMD rules 42–51 is
  `atomCfg`;
* `stepAtoms`: every rule of `Step` from 6 on outside 22–25 is `atomCfg` (rules 7–9 included).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The indices of `rules` outside `skip` all pass `f`. -/
def allBut (skip : List Nat) (f : Rule → Bool) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i =>
    skip.contains i || match rules[i]? with
      | some r => f r
      | none => false

set_option maxRecDepth 100000 in
/-- **Every rule of `Step_pure` outside `structPure` is flat.** -/
theorem pureAtoms (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      allBut structPure atomPure rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- **Every rule of `Step_read` outside `structRead` and 42–51 is flat.** -/
theorem readAtoms (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      allBut (structRead ++ Round7.MemSimd.msReadRules) atomCfg rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` from 6 on outside 22–25 is flat.** -/
theorem stepAtoms (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
      allBut ([0, 1, 2, 3, 4, 5] ++ Round7.MemSimd.stepMSRules) atomCfg rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom
