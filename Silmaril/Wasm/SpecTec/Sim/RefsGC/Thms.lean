module

public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Aggregate
public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.AggregateIter

/-!
# SpecTec ↔ Core 3.0, family R (references and GC): what is proved

* `otherwiseAt_of_table`, `otherwise_of_ruleAt`: an `otherwise` premise holds when every earlier
  rule names an opcode foreign to the instruction (`pureTagTable_eq`, `readTagTable_eq` check the
  tag tables against the pinned script), except a listed set refuted by hand.
* `fwd_reference`: `Forward.reference` at `simEnv B`, all 20 constructors of `RefStep`.
* `fwd_brOnCastSucceed`, `fwd_brOnCastFail`, `fwd_brOnCastFailSucceed`, `fwd_brOnCastFailFail`:
  the four `Forward.brOnCast*` fields at `simEnv B`.
* `Aggregate.lean`: the aggregate rules that trap on null or out-of-bounds, and `array.len`
  (with `ai.fields.length < 2 ^ 32`), forward, for any environment with the rules.
* `AggregateIter.lean`: `array.fill-zero/succ`, `array.copy-zero`, `array.new_elem-oob`,
  `array.init_elem-oob2/zero`, forward, with their `otherwise` premises.

All conditional on `TypingFacts`, `RTyping`, `RFuns`, `RStoreFuns` and `RefOkBridge`
(`RefsGC/Defs.lean`). See `docs/projects/spectec/README.md`, family R.
-/
