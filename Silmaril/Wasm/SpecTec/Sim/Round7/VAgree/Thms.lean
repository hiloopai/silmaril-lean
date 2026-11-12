module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Eq

/-!
# Round 7, memory SIMD: the evaluator half of the `$vbytes_` transfer

`OpenRMRest` is stated at `BM = withVBytes (Prims.builtins …)`, and round 6's proofs are at
`BI = Prims.builtins …`. Pass 2 (`Round7.VBytes`) proved the syntactic half: only `Step_read` rule
43 and `Step` rule 23 refer to `$vbytes_`. This header proves the evaluator half: for any two
builtins `B₁`, `B₂` that agree at every name other than `$vbytes_` (`AgreeOff`, which holds for
`withVBytes B` and `B` by `agreeOff_withVBytes`), the fuelled evaluator of `simEnv B₁` and
`simEnv B₂` answers alike on syntax that never reaches `$vbytes_`:

* `evalExp_eq`, `evalArgs_eq`, `matchExp_eq`, `premsHold_eq`, `callDef_eq`: on `GoodEvs` syntax
  (definitions reachable from `Step` other than `$vbytes_`, relations reachable from `Step` other
  than `Step` and `Step_read`) in a `DefsOk` scope, at every fuel;
* `derives_eq`, `derives_iff`: every `GoodRel` relation derives alike, with or without fuel;
* `anyRule_goodRule_eq`: one rule tried on its own answers alike when it is a `GoodRule`. That
  covers every rule of `Step_pure` (`goodRule_pure`), every rule of `Step_read` other than 43
  (`goodRule_read`) and every rule of `Step` other than 1–5 and 23 (`goodRule_step`). Rules 1–5
  of `Step` refer to `Step_read` or `Step`, so a derivation through them may reach rule 43 or 23.

The proof is round 7's `$utf8` agreement (`Script.agreeAt`) adapted to builtins that differ at one
name (`Raw/…/Round7/VAgree/Agree.lean`). Its invariants are discharged by kernel computations:
`stepRelOnly_fixed` (no reachable item other than `Step` and `Step_read` refers to them) and the
rule facts of `VAgree/Rules.lean`, with `Round7.VBytes` for `$vbytes_`.

What is not proved here: the declarative layer. `Fires` and `TypedD` read rules through
`DDerives`, `QuantsOk` (the typing block `hasTyp`) and `otherwise`. Carrying the equalities
there needs the same agreement for `hasTyp`, an induction over `DDerives` for `GoodRel` premises,
and, for the `otherwise` rules of `Step_read` after 43 (54–102), a proof that rule 43 does not fire
on their left-hand sides.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.stepRelOnly_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepRelOnly_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.goodRule_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goodRule_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.evalExp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalExp_eq

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.derives_withVBytes_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms derives_withVBytes_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.anyRule_goodRule_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms anyRule_goodRule_eq

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
