module

public import Silmaril.Proofs.Wasm.Logic.Sep.Array

/-!
# Separation logic over the Core 3.0 store: rules

Proofs in `Silmaril/Proofs/Wasm/Logic/Sep`:

* structural: `STriple.frame` (the **frame rule**), `STriple.conseq`,
  `STriple.seq`, and `STriple.hwp` (a triple run without a frame gives an
  every-run weakest precondition, hence `Silmaril.Wasm.Logic.Hoare.HWP.sound`);
* GC structures, with store-relative addresses: `STriple.structNew` (fresh
  allocation at a new address), `STriple.structGet`, `STriple.structSet`;
* GC arrays (`Silmaril.Proofs.Wasm.Logic.Sep.Array`): `STriple.arrayNewFixed`
  (fresh allocation, `arrayPts`), `STriple.arrayGet`, `STriple.arraySet`
  (element points-to `pointsTo (.elem a i) (.fv fv)`).

The separate `Silmaril.Wasm.Logic.Sep.Memory.Thms` header proves a full-width
`i32.store` rule over four owned native byte cells. Globals still have no
separation-logic instruction rule here (plain rules are in
`Silmaril.Wasm.Logic.Instr.Thms`).
-/
