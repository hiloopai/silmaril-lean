module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeExit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeCover
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeBits

/-!
# Vector code under labels and frames, with exits and traps, at `simEnv20V (vecNB P)`

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecTree`; see `docs/projects/spectec/README.md`, "vec".

* `VecTreeExit`: `Step_pure`'s exits (`label-vals`, `frame-vals`), branches and returns
  (`br-zero`, `br-succ`, `return-frame`, `return-label`) and traps (`trap-vals`, `trap-label`,
  `trap-frame`) fire in `simEnv20V B`, at every `B` (**`spureV_labelVals`**, …,
  **`spureV_trapVals`**).
* `VecTreeTyp`: the cases of `instr` are a prefix of those of `admininstr` in the corrected
  script (`take_adminCasesV`, kernel `rfl`), so **`typedV_instr_of_admin`**: an `admininstr`
  named as an `instr` case is an `instr`; for straight-line vector code,
  `typedV_instrsV_of_vecOk`.
* `VecTreeCover`: vector trees (`VecCode`: straight-line vector instructions, traps, and labels
  and frames with vector-tree bodies); **`cover_tree`**: every V2 step from one with plain tails
  is a nested vector redex or exit; `vecCode_nest`.
* `VecTreeFwd`: **`fwdBaseV_exit`** (every `B`), **`wholeStepTree`**, **`wholeRunTree`**,
  `wholeRunTree_expr`.
* `VecTreeBits`: `$inot_`, `$iandnot_`, `$ibitselect_` have no clause and no answer at
  `vecNB P`, so their calls denote nothing there (**`not_callDef_bitPrims`**); restated by
  `callDef_bitPrim_of_answer`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.spureV_trapVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.spureV_trapVals

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.spureV_brSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.spureV_brSucc

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.typedV_instr_of_admin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.typedV_instr_of_admin

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.cover_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.cover_tree

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.fwdBaseV_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.fwdBaseV_exit

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.wholeStepTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.wholeStepTree

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.wholeRunTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.wholeRunTree

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTree.not_callDef_bitPrims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTree.not_callDef_bitPrims
