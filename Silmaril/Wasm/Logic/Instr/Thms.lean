module

public import Silmaril.Proofs.Wasm.Logic.Instr.Control

/-!
# Instruction rules for the every-run logic

Instruction-specific rules for `Silmaril.Wasm.Logic.Hoare`, stated once for both
readings (`Wp .part = HWP`, partial correctness; `Wp .total = TWP`, total
correctness; `Silmaril.Wasm.Logic.Instr.Defs`), for **every profile** and every host
relation. Every rule is derived, with a proof, from the generic head rule
`Hoare.Safe.head` (no rule is assumed):

* the family rules (`Silmaril.Proofs.Wasm.Logic.Instr.Det`): `Wp.fam` (every head
  step of a non-control instruction; the operand split is unique,
  `Head.split_unique`) and `Wp.det` (one witness, for `ProfileFree`
  instructions; `Head.unique`), with `Safe.*`/`HWP.*`/`TWP.*` versions;
* parametric, variable, numeric (integer and float, scalar conversions) and
  reference rules (`…/Instr/Basic`);
* loads, stores, `memory.size`/`memory.grow` and bulk memory over every memory
  and address type (`…/Instr/Memory`);
* tables, `call_indirect` and `return_call_indirect` (`…/Instr/Table`);
* vector instructions, including the relaxed and float ones (`…/Instr/Vector`);
* GC structures and arrays (`…/Instr/Aggregate`);
* branches (`br`, `br_table`, `br_on_non_null`, `br_on_cast`,
  `br_on_cast_fail`), `throw_ref` and `return_call_ref` exits
  (`…/Instr/Control`).

The coverage table, instruction by instruction, is in `docs/projects/wasm-binaryen-tooling.md`.

A Silmaril addition.
-/
