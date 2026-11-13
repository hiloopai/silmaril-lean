module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModule
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XFrag
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XRefl
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XLocalInv
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModOk

/-!
# Instruction typing of the wasm-3.0 script, extended: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Instr30X`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Instr30XModule,Instr30XNum,Instr30XFrag,Instr30XRefl,
Instr30XLocal,Instr30XLocalInv,Instr30XModRule,Instr30XModFns,Instr30XModEvalA,Instr30XModEvalB,
Instr30XModEvalC,Instr30XFuncidx,Instr30XModOk}`; see `docs/projects/wasm-components.md`,
"Stretch, insttyp2".

* `not_moduleOk`, `stepModel_not_moduleOk`: on the concrete primitives, `Module_ok` has no
  `DDerivesB` facts: its rule concludes `$clos_moduletype(C, …)`, whose one clause binds `dt*` only
  in an `if` premise, so it never has a value (`not_callDef_closMod`).
* `not_emptyModuleOk`: so `Instr30.Task.emptyModuleOk` is false.
* `moduleOk_empty`, `moduleOk_withClosMod`, `emptyModuleOk_repaired`: and that is the only
  obstacle. In an evaluator whose primitives answer `$clos_moduletype({}, [] -> [])` (such as
  `withClosMod B`), `Module_ok`'s rule fires at the empty module: its twenty premises are
  discharged at the scope `modσ`, the side conditions by evaluating `$disjoint_`, the context
  equations, `$tagsxt`, `$globalsxt`, `$memsxt`, `$tablesxt`, `$funcsxt` at `[]` and
  `$funcidx_nonfuncs` (through `$funcidx_module`, `$free_module`, `$free_list`, `$free_opt`;
  `funcidxEmpty`) clause by clause.
* `dd_intConst`, `dd_intUnOp`, `dd_intBinOp`, `dd_intTestOp`, `dd_intRelOp`: `Instr_ok/const`,
  `unop`, `binop`, `testop`, `relop` fire at the images of Core's integer instructions, in any
  typed context (one shape, `opRule`, fired by `dd_opRule`).
* `instrX_preserves`: on `DomX`, every `Instr_ok {}` judgement Core validates is a fact of
  `stepModel BI` (`nop`, `unreachable`, `drop`, and the integer numeric instructions).
* `fragOkX_dd`, `instrsX_preserves`, `instrsX_holds`: the same for `Instrs_ok {}` on `FragOkX`
  derivations. `constAdd`: non-vacuity, `i32.const a; i32.const b; i32.add` at `[] -> [i32]`.
* `instrsOk_params`, `dropNestedS_not_reflected`: Core derivations over `Instr30.frag` have valid
  parameter types, so Core rejects `[drop]` at `[REF NULL D_out] -> []`, an `Instrs_ok {}` fact of
  `stepModel BI`: `Instrs_ok` is not reflected on reached sequences at bounded types, so its domain
  has to stay a Core-side condition (`FragOk`, `FragOkX`).
* Contexts with locals: `ctxL` is the image of Core's `{locals := L}` (`ctxT_locals`: typed when
  `L` is bounded). `dd_localGet`, `dd_localSet`, `local_preserves`: `Instr_ok/local.get` and
  `local.set` fire there at Core's typings. `localGet_inv`, `localGet_sat_iff`: at `local.get` the
  satisfaction condition is exact, in every `simEnv B` and under every reading of `otherwise`.
-/

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

/-- **`ModuleOkEmpty` at the concrete primitives.** -/
theorem moduleOkEmpty_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    ModuleOkEmpty (Round4Int.BI P hn host) :=
  stepModel_not_moduleOk P hn host

end Silmaril.Wasm.SpecTec.Institution.Instr30X

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.not_emptyModuleOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.not_emptyModuleOk

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.instrX_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.instrX_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.instrsX_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.instrsX_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.constAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.constAdd

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.dropNestedS_not_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.dropNestedS_not_reflected

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.local_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.local_preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.localGet_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.localGet_sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Instr30X.emptyModuleOk_repaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Instr30X.emptyModuleOk_repaired
