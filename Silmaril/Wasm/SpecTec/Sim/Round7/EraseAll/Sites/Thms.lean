module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.HypsB
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.WithInst

/-!
# Round 7, the export swap: the excluded sites (round 3, pass 3, proved)

See `docs/projects/spectec/README.md`. Pass 2 left six reachable names out of the
checked part: `$with_tableinst`, `$with_meminst`, `$hostcall`, `$blocktype_`, `Step_read` and
`Step`.

* **`$blocktype_` and `Step_read` join the checked part.** `$blocktype_`'s primitive reads only
  `MODULE.TYPES` of its state, which erasure maps pointwise, through strict decoders
  (`blocktypeCall_eraseV`, `call_blocktype_erase`). So round 6's primitives commute with erasure
  at every name but `$hostcall` (`biErase_BI'`). The kernel checks the clauses of `$blocktype_` and
  the rules of `Step_read` at the enlarged sets `gdB`, `grB` (`xBNamedOk_fixed`); the rest of the
  script follows by monotonicity of the check (`xExp_mono`). So
  `hyps_B : StripInj c → Hyps (QC c) grB gdB (utf8Env (Round4Int.BI P hn host))`, and
  `Round7.EraseAll.eraseAt` covers both.
* **`$with_tableinst` and `$with_meminst` at a real state.** `callDef_withTableinst_state`,
  `callDef_withMeminst_state`: when the call's first argument is a state whose store is no record
  with an `EXPORTS` field, the call commutes with erasure and keeps the swap set. The generic step
  is `tryClauses_root` (a clause whose body is a pair whose first component is an update written
  only at the root, `step_updRoot`), and `root_of_state` evaluates `$sof(z)` in the clause's scope.
* Still open here: `$hostcall` (its answers agree only as sets, `Round7.Swap.hostcallCall_erase`)
  and the relation `Step` itself, whose rules call the three remaining names.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.hyps_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyps_B

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.biErase_BI'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms biErase_BI'

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.callDef_withTableinst_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms callDef_withTableinst_state

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.callDef_withMeminst_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms callDef_withMeminst_state

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
