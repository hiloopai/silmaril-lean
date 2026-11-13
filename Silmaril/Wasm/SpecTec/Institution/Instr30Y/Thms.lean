module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Y

/-!
# Instruction typing of the wasm-3.0 script, results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30Y`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Instr30YVar,Instr30YFloat,Instr30YFlat,Instr30YSub,Instr30Y}`; see
`docs/projects/spectec/README.md`, "insttyp".

* `dd_floatConst`, `dd_floatUnOp`, `dd_floatBinOp`, `dd_floatRelOp`: `Instr_ok/const`, `unop`,
  `binop`, `relop` at Core's float instructions, in any typed context.
* `ctxLG`, `ctxT_lg`: the context value `{LOCALS ls, GLOBALS gs}`, typed when bounded.
  `dd_localGet`, `dd_localSet`, `dd_localTee`, `dd_globalGet`, `dd_globalSet`,
  `variable_preserves`: all five variable rules fire there at Core's typings.
* `valtypeOk_flat`, `resulttypeOk_flat`, `instrtypeOk_flat`, `valtypeSub_numVec`: validity and
  subtyping of flat value types in every typed context. `dd_selectExpl`, `dd_selectImpl`,
  `parametric_preserves`: `nop`, `unreachable`, `drop` and `select` in every context, at flat types.
* `numeric_preserves`, `instrY_preserves`, `instrY_sat`: every Core typing of a `fragY`
  instruction in `{locals := L, globals := G}` (under `ParamOk`) is an `Instr_ok` fact.
* `ruleAt_instrsSub`, `ruleAt_instrtypeSub`, `dpremB_setminus`, `dd_instrtypeSub`, `dd_instrsSub`,
  `resulttypeSub_numVec`: `Instrs_ok/sub` and `Instrtype_sub`, with `$setminus_(localidx, [], [])`
  evaluated clause by clause, and `Resulttype_sub` towards number and vector types.
* `fragOkY_dd`, `instrsY_sat`, `fragOkY_sound`: the same for `Instrs_ok` on `FragOkY` (`empty`,
  `instr`, `seq`, `frame`, `sub`). `globalAdd`: non-vacuity,
  `global.get 0; f64.const 1; f64.add; global.set 0`; `unreachableBot`: non-vacuity of `sub`,
  `unreachable` at `[] -> [i32]` from `[] -> [BOT]`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.variable_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.variable_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.parametric_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.parametric_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.instrY_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.instrY_sat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.instrsY_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.instrsY_sat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.globalAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.globalAdd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.unreachableBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.unreachableBot

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30Y.dd_instrsSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30Y.dd_instrsSub
