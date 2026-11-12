module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Assemble

/-!
# Round 7, memory SIMD: `$vbytes_` is called only by the memory SIMD rules

`Round7.Task.wholeStepValidRM` is open. What is left is `OpenRMRest`, stated at
`BM = withVBytes (Prims.builtins …)`, where round 6's proofs are at `BI`. The two builtins differ
only at `$vbytes_` (`withVBytes`). A transfer `BI → BM` for the fields that exclude the memory
SIMD rules (`rest.pure`, `rest.read` off `msReadRules`, `rest.step` off `stepMSRules`) needs
two things:

1. a syntactic fact: the parts of the script those fields run never mention `$vbytes_`;
2. an evaluator fact: two environments whose builtins differ only at a name that the syntax
   never mentions evaluate alike. This is the analogue of round 7's `Script.agreeAt`, which does
   it for `$utf8`.

This header proves (1). Every statement is a kernel computation over the fixed wasm-3.0 script
(`decide +kernel`, in four chunks and one rule module), read in `simEnv B` for every `B`:

* `vbytesOnlyStep_fixed`: only the relations `Step_read` and `Step` refer to `$vbytes_`;
* `def_noVBytes`, `typ_noVBytes`: no definition and no type refers to it, so no function
  body and no type check can reach `$vbytes_`;
* `rel_noVBytes`: no relation other than `Step_read` and `Step` refers to it;
* `pure_noVBytes`: no rule of `Step_pure` refers to it;
* `read_noVBytes`: only rule 43 of `Step_read` (`vload-num-val`) refers to it, and
  `43 ∈ msReadRules`;
* `step_noVBytes`: only rule 23 of `Step` (`vstore-val`) refers to it, and `23 ∈ stepMSRules`.

(2) is not proved here. Rules with an `otherwise` premise also read the competing rules of
their relation, so (2) has to cover those rules too, as round 7's `otherwiseAtB_iff` does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VBytes

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.vbytesOnlyStep_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms vbytesOnlyStep_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.read_noVBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_noVBytes

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.step_noVBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_noVBytes

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.def_noVBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms def_noVBytes

end Silmaril.Wasm.SpecTec.Sim.Round7.VBytes
