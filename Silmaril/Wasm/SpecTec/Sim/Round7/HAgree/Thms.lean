module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.Pairs

/-!
# Round 7, `BD`: the declarative transfer off `$vbytes_` and `$hostcall`

`Round7.VAgree` and `Round7.VDecl` move single rules and `TypedD` between builtins that agree off
`$vbytes_`. This topic does the same for builtins that agree off `$vbytes_` **and** `$hostcall`
(`AgreeOff`), which covers round 7's three builtins: `HostD.BD` (`$hostcall` keyed on `storeVD`
images), `MemSimd.BM = withVBytes BI` and round 6's `BI = Prims.builtins …` (`agreeOff_bd_bm`,
`agreeOff_bm_bi`, `agreeOff_bd_bi`).

* **Kernel facts** (`decide +kernel`, kernel reduction, no native code): in the fixed wasm-3.0 script only the
  relation `Step` refers to `$hostcall` (`hostcallOnlyStep_fixed`, four chunks), and of its rules
  only 8 and 9 (`relRulesUsers_step`; none of `Step_pure` or `Step_read`). The relations `Step`
  reaches have `RG` quantifier types and conclusion alternatives with `$hostcall` also excluded
  (`relFacts_fixed`, five chunks).
* **Evaluator** (`evalExp_eq`, `derives_eq`, `anyRule_goodRule_eq`, …): VAgree's agreement, with
  `GoodName` excluding both names. The proofs are copies (`Raw/…/Round7/HAgree/{Good,Agree}.lean`):
  they never use which names are excluded.
* **Declarative layer** (`hasTyp_iff`, `typedD_iff`, `dderives_agree`, `otherwiseAt_read`):
  VDecl's, copied the same way (`Raw/…/Round7/HAgree/{Typ,Der}.lean`).
* **Single rules** (`fires_pure_iff`, `fires_read_iff`, `fires_step_iff`): every rule of
  `Step_pure`, every rule of `Step_read` but 43 and every rule of `Step` but 1–5, 8, 9 and 23
  (`stepBad`) fires alike; at round 6's backend reading too (`firesB_pure_iff`, `firesB_read_iff`,
  `firesB_step_iff`).
* **Obligations** (`backwardUpToDRestSH_agree`): the per-rule backward obligations off memory SIMD
  and off the host calls move across.

Not here: the whole step under a value invariant (VDecl's `Step.lean`, VInv's `StepInvB`), which
would need `Step` rules 8 and 9 kept silent as well as 43 and 23.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.hostcallOnlyStep_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hostcallOnlyStep_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.relFacts_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relFacts_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.fires_read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_read_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.fires_step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_step_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.firesB_read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesB_read_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.typedD_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedD_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.backwardUpToDRestSH_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backwardUpToDRestSH_agree

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
