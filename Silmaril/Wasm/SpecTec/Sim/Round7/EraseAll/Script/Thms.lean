module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.Script

/-!
# Round 7, the whole-evaluator erasure on the wasm-3.0 script (round 3, pass 2, proved)

Definitions are in `Round7/EraseAll/Script/Defs.lean`; see `docs/projects/spectec/README.md`.

* `xRelsOk_fixed`, `xDefsOk_fixed` (kernel computations, in forty chunks of the script): every relation
  and every definition of `stepReachE` (what `Step` reaches, without `$with_tableinst`,
  `$with_meminst`, `$hostcall`, `$blocktype_`, `Step_read` and `Step`) passes the syntactic check
  `xExp` at `grE`, `gdE`. In particular `stepReachE` is closed under references, and the
  composition in `Deftype_ok` has the `nilLit` shape.
* `hyps_utf8Env : StripInj c → BIErase (QC c) gdE (utf8Env B) → Hyps (QC c) grE gdE (utf8Env B)`.
  So `Round7.EraseAll.eraseAt` holds in the round-7 environment for every `B` whose primitives of
  `stepReachE` commute with erasure. That last hypothesis is open for round 6's builtins.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.xDefsOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xDefsOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.hyps_utf8Env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyps_utf8Env

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
