module

public import Silmaril.Wasm.Auto2.VCLib2.Defs
public import Silmaril.Wasm.Auto2.VCLib.Thms
public import Silmaril.Wasm.Auto2.VCCheck.Thms
public import Silmaril.Wasm.Auto2.VCSort.Thms
public import Silmaril.Wasm.Auto2.VCBTree.Thms

/-!
# Contracts with memory and callees (VC library, pass 2): conditions and entries

The conditions of `double` (with the callee `add`) and `load2` (memory), computed by `vcgen4` and
closed; the proved contracts `doubleEntry`, `load2Entry`; the library `entriesM` that
`wasm-check vc` searches (pass 1's contracts through `VcEntry.toM`, then these); and the
kernel-checked checks of the demonstration modules.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib2

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen Silmaril.Wasm.Auto2.VCBridge Silmaril.Wasm.Auto2.VCCheck
open Silmaril.Wasm.Auto2.VCLib (libFuel addSpec)

set_option maxRecDepth 100000 in
/-- The conditions of `double` (one call to `add`). -/
theorem double_vcs : AllValid {} (genFunc (doubleSpecC addFunc') doubleFunc libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of the callee `add` of `doubleProg`. -/
theorem add'_vcs : AllValid {} (genFunc addSpec addFunc' libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `load2`: two bounds checks and the result. -/
theorem load2_vcs : AllValid {} (genFunc load2Spec load2Func libFuel) := by
  vcgen4
  all_goals (intros; dsimp only [IntType.width] at *)
  all_goals (try simp_all)
  all_goals omega

/-- `double x = x + x` with the callee `add` (any code meeting `addSpec`). -/
def doubleEntry : VcEntryM where
  name := "double"
  F := {}
  S := doubleSpec
  fuel := libFuel
  conds := genFunc (doubleSpecC addFunc') doubleFunc libFuel
  valid := double_vcs
  total := rfl
  calls := [(0, addSpec, genFunc addSpec addFunc' libFuel)]
  callsOK := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, rfl, add'_vcs⟩

/-- `load2 p = mem[p] + mem[p + 4]` (memory). -/
def load2Entry : VcEntryM where
  name := "load2"
  F := {}
  S := load2Spec
  fuel := libFuel
  conds := genFunc load2Spec load2Func libFuel
  valid := load2_vcs
  total := rfl

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `bump` (globals). -/
theorem bump_vcs : AllValid {} (genFunc bumpSpec bumpProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
/-- The conditions of `addn` (a global written in a loop): entry, exit, invariant step, variant. -/
theorem addn_vcs : AllValid {} (genFunc addnSpec addnProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; try dsimp only [IntType.width] at *)
  all_goals (try simp_all)
  all_goals bv_omega

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `frame` (the stack pointer is restored). -/
theorem frame_vcs : AllValid {} (genFunc frameSpec frameProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

/-- `bump x`: the result and the final global are `g + x`. -/
def bumpEntry : VcEntryM where
  name := "bump"
  F := {}
  S := bumpSpec
  fuel := libFuel
  conds := genFunc bumpSpec bumpProg.funcs[0] libFuel
  valid := bump_vcs
  total := rfl

/-- `addn n`: the global `acc` grows by `n`. -/
def addnEntry : VcEntryM where
  name := "addn"
  F := {}
  S := addnSpec
  fuel := libFuel
  conds := genFunc addnSpec addnProg.funcs[0] libFuel
  valid := addn_vcs
  total := rfl

/-- `frame x = x + 1`, the stack pointer restored. -/
def frameEntry : VcEntryM where
  name := "frame"
  F := {}
  S := frameSpec
  fuel := libFuel
  conds := genFunc frameSpec frameProg.funcs[0] libFuel
  valid := frame_vcs
  total := rfl

/-- Insertion sort (two-memory invariants, `Silmaril.Wasm.Auto2.VCSort`). -/
def isortEntry : VcEntryM where
  name := "isort"
  F := VCSort.sortFns
  S := VCSort.sortSpecV
  fuel := VCSort.sortFuel
  conds := genFunc VCSort.sortSpecV Silmaril.WasmSpec.InsertionSort.sortFunc VCSort.sortFuel
  valid := VCSort.sort_vcs
  total := rfl

/-- `oba_get` of the B-tree library (`Silmaril.Wasm.Auto2.VCBTree`). -/
def obaGetEntry : VcEntryM where
  name := "oba_get"
  F := VCBTree.btFns
  S := VCBTree.getSpecV
  fuel := VCBTree.btFuel
  conds := genFunc VCBTree.getSpecV Silmaril.WasmSpec.BTree.getFunc VCBTree.btFuel
  valid := VCBTree.get_vcs
  total := rfl

/-- `oba_find` of the B-tree library (`Silmaril.Wasm.Auto2.VCBTree`). -/
def obaFindEntry : VcEntryM where
  name := "oba_find"
  F := VCBTree.btFns
  S := VCBTree.findSpecV
  fuel := VCBTree.btFuel
  conds := genFunc VCBTree.findSpecV Silmaril.WasmSpec.BTree.findFunc VCBTree.btFuel
  valid := VCBTree.find_vcs
  total := rfl

/-- The contracts of `wasm-check vc`. -/
def entriesM : List VcEntryM :=
  VCLib.entries.map VcEntry.toM ++
    [doubleEntry, load2Entry, bumpEntry, addnEntry, frameEntry, isortEntry, obaGetEntry,
      obaFindEntry]

/-- The contract named `n` (`sum` if there is none). -/
def entryM (n : String) : VcEntryM := (entriesM.find? (·.name == n)).getD VCLib.sumEntry.toM

/-! ## Kernel-checked checks of the demonstration modules -/

/-- `double` calling `add`: proved. -/
theorem double_spec (P : Numerics.Profile) : ModTSpecM P doubleEntry doubleProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `double` whose callee computes `y + x`: its callee's condition is accepted by normalisation. -/
theorem doubleSwap_spec (P : Numerics.Profile) : ModTSpecM P doubleEntry doubleSwapProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `load2`: proved (memory). -/
theorem load2_spec (P : Numerics.Profile) : ModTSpecM P load2Entry load2Prog 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `load2` adding in the other order: accepted by normalisation. -/
theorem load2Swap_spec (P : Numerics.Profile) : ModTSpecM P load2Entry load2SwapProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `max` with `select` (front-end benchmark `max-select`): accepted by normalisation (its one
condition is `x = x`). -/
theorem maxSelect_spec (P : Numerics.Profile) :
    ModTSpecM P VCLib.maxEntry.toM Silmaril.Wasm.Auto.FrontBench.maxSelect 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `add` with swapped operands (front-end benchmark `add-swap`): accepted by normalisation. -/
theorem addSwap_spec (P : Numerics.Profile) :
    ModTSpecM P VCLib.addEntry.toM Silmaril.Wasm.Auto.FrontBench.addSwap 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `bump` (globals): proved. -/
theorem bump_spec (P : Numerics.Profile) : ModTSpecM P bumpEntry bumpProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `addn` (a global written in a loop): proved. -/
theorem addn_spec (P : Numerics.Profile) : ModTSpecM P addnEntry addnProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- `frame` (a stack pointer restored): proved. -/
theorem frame_spec (P : Numerics.Profile) : ModTSpecM P frameEntry frameProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- Insertion sort, checked at the specification library's module. -/
theorem isort_spec (P : Numerics.Profile) :
    ModTSpecM P isortEntry Silmaril.WasmSpec.InsertionSort.program 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

example : vcCheckM isortEntry isortUnsignedProg 0 = false := by decide +kernel

/-- `oba_get` and `oba_find` (exports `0` and `1`), checked at the B-tree library's module. -/
theorem obaGet_spec (P : Numerics.Profile) :
    ModTSpecM P obaGetEntry Silmaril.WasmSpec.BTree.program 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem obaFind_spec (P : Numerics.Profile) :
    ModTSpecM P obaFindEntry Silmaril.WasmSpec.BTree.program 1 :=
  modTSpecM_of_vcCheckM (by decide +kernel)
example : vcCheckM bumpEntry bumpLostProg 0 = false := by decide +kernel
example : vcCheckM frameEntry frameLeakProg 0 = false := by decide +kernel

/-- The mutants are not accepted. -/
example : vcCheckM doubleEntry doubleSubProg 0 = false := by decide +kernel
example : vcCheckM load2Entry load2OffProg 0 = false := by decide +kernel
example : vcCheckM VCLib.addEntry.toM Silmaril.Wasm.Auto.FrontBench.addSub 0 = false := by
  decide +kernel

end Silmaril.Wasm.Auto2.VCLib2
