module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30

/-!
# Instruction typing of the wasm-3.0 script against Core 3.0 validation: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Instr30Rules,Instr30Derive,Instr30Heads,Instr30Inv,
Instr30Seq,Instr30}`; see
`docs/projects/spectec/README.md`, "insttyp".

The model is `stepModel BI` (`Round4Int.BI`), as in `Typing30`. The sentence map is
`ISen.toSen`, Core's reading is `ISen.Holds`, and the domain is `ISen.Dom`.

* `valtypeOk_of`, `resulttypeOk_of`, `instrtypeOk_of`: bounded Core-valid value, result and
  instruction types are `Valtype_ok`, `Resulttype_ok`, `Instrtype_ok` facts in `{}`.
* `instr_preserves`: on the domain (`nop`, `unreachable`, `drop` at bounded types), every
  `Instr_ok {}` judgement Core validates is a fact of `stepModel BI`.
* `fragOk_dd`, `instrs_preserves`, `instrs_holds`: the same for `Instrs_ok {}` on `FragOk`
  derivations (bounded derivations over the reached instructions by `Instrs_ok/empty`, `instr`,
  `seq` and `frame`; `seq` fires through `$with_locals(C, [], []) = C`). `unreachableDrop`:
  non-vacuity, through `seq`.
* `nop_sat_iff`: at `nop` the satisfaction condition is exact, at every instruction type: only
  `Instr_ok/nop` types `NOP` (`instrOk_heads`, `nop_inv`).
* `drop_shape`, `drop_reflects`: an `Instr_ok {}` fact at `drop` has a type `[t] -> []` with
  `Valtype_ok {}` at `t`, and is Core-valid when Core validates `t`.
* `emptyModule_ok`: Core validates the empty module at `[] -> []`; that `stepModel BI` validates
  its image `emptyModuleV` is the frozen open target `Task.emptyModuleOk`.
* `drop_nested`: `drop` at `REF NULL D_out` is in the domain and a fact, and Core rejects it, so
  `Instr_ok` is not reflected.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.instr_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.instr_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.instrs_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.instrs_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.drop_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.drop_nested

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.nop_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.nop_sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.drop_reflects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.drop_reflects

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.unreachableDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.unreachableDrop

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30.emptyModule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30.emptyModule_ok
