module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.Assemble

/-!
# Round 9, rm (pass 2): the 28 `otherwise` rules of `Step_read` under code erasure

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.RMElse`; see `docs/projects/spectec/README.md`.

* `elseAt_ok` (kernel): the 28 `otherwise` rules of `Step_read` pass round 8's evaluator check and
  have only `otherwise` and `FiresC.relG` relation premises.
* `fires_erase_else`, `firesEraseD_else`: the rule case of `FiresC.fires_erase_rel` with an
  `otherwise` premise; such a rule keeps firing when the code is erased, given
  `ElseBwd.ElseBwdDRest` (the backward firing at 68 pairs).
* `restMSHCJ_of_rest`, `wholeStepValidRM_of_restDPK`: `Round7.MemSimd.Task.wholeStepValidRM`
  from `OpenRMRestDPK` (`forward`, `elseBwd`, `castsFwd`, `castsBwd`).

The backward firing along `eraseC` (round 9's `ElseBwd.reflect_core`, ported):

* `goodTypsC_fixed` (kernel), `ncB_of_HasTyp`, `envNC_simEnv`: values of the types named in
  `goodC` (round 7's export-free names, and `expr`, `frame`, `funccode`, `instr`, `moduleinst`)
  hold no `CODE` record, so `eraseC` fixes them.
* `reflect_coreC`, `pairReflectD_simple`: the backward firing at the 48 pairs of `simplePairsC`
  (round 9's 45 simple pairs, `(21, 9)`, and `(101, 100)`, `(102, 100)`, whose earlier rule has an
  `Expand` premise: `Expand` concludes `CODE`-free values, `dderives_ncB`).
* `fireFwd`, `pairReflectD_chain`: at the 16 chain pairs of two levels (`chainPairsC`,
  `chain2PairsC`), where the earlier rule's own `otherwise` goes back because every rule before it
  is head-differing, adjacency-clashing, or goes forward.
* `elseBwdDRest_of_left`, `wholeStepValidRM_of_restDPL`: `wholeStepValidRM` from `OpenRMRestDPL`,
  whose `elseLeft` asks the backward firing at 4 pairs (`leftPairsC`, the `Ref_ok` pairs).
* `refOk_bwd` (kernel check `refOkOk_fixed`), `pairReflectD_sf` (kernel check `sfPairsOk_fixed`):
  a `Ref_ok` derivation at an erased store goes back, by rebinding the store quantifier; so the
  4 pairs hold (`elseBwdDLeftC_sim`).

**Closed:** `elseBwdDRest_builtins` (all 68 pairs), `restMSHCJ_sim` (round 8's `firesRead`, with
no hypothesis), and `wholeStepValidRM_of_restDPM`: `Round7.MemSimd.Task.wholeStepValidRM` from
`OpenRMRestDPM`, whose fields are `forward`, `castsFwd` and `castsBwd` outside `EasyP` only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.fires_erase_else' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fires_erase_else

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.wholeStepValidRM_of_restDPK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPK

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.pairReflectD_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairReflectD_simple

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.pairReflectD_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairReflectD_chain

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.wholeStepValidRM_of_restDPL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPL

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.refOk_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refOk_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.restMSHCJ_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restMSHCJ_sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.wholeStepValidRM_of_restDPM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPM

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
