module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Float
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Heads
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Tags
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Ctrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Values
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Refs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Exn
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Inj
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Facts
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Types
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Whole
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Example

/-!
# SpecTec ↔ Core 3.0, typing track: what is proved

After the two ported-code fixes (`Sem.argSubOk`, the subtype test of a `SubE` argument pattern;
`Sem.bindQuants`, case quantifiers bound by a defining equation; see `docs/projects/spectec/README.md`):

* `Typing.hasTyp_fN`, `Typing.hasTyp_num_float`: every encoded float (`floatV`, all IEEE shapes:
  normal, subnormal including `±0`, infinities, NaNs with any payload) inhabits `fN(N)` and
  `num_(Fnn)` in every `simEnv B`;
* `Typing.typedDep_num`: every numeral inhabits `num_(t)` (family V's `FloatTyping.num`);
* `Typing.hasTyp_vec`, `Typing.typedV_vecT`: every 128-bit pattern inhabits `vec_(V128)`
  (family V's `VecTyping.vec`);
* `Typing.typedV_val_num`, `Typing.typedV_val_vec`: every numeric and vector `Val` is a typed
  `val`;
* `Typing.not_forall_not_hasTyp_num_float`: the premise of round 1's refutations
  (`IntNumeric.not_hasTyp_num_float`, `Whole.not_floatTyping`, `Whole.not_vecTyping`) is false.
* `Typing.instrToV_head`, `Typing.adminToV_case`: the head constructor of an encoded instruction
  (`instrHead`, `adminHead`) is determined by the instruction; the tag inversions `head_*`
  follow, and with them `Typing.ctrlDecode_simEnv : CtrlDecode (simEnv B)` (family C's decoder
  interface, including its `vals` field).
* `Typing.typedV_ref`, `Typing.typedV_val`: every Core reference is a typed `ref`, every Core
  value a typed `val`.
* `Typing.floatV_injective`, `Typing.refToValue_injective`, `Typing.valV_injective`: the value
  encoding is injective.
* Discharged interfaces, in every `simEnv B`: `Typing.typingFacts_simEnv : TypingFacts`,
  `Typing.ctrlTyping_simEnv : CtrlTyping`, `Typing.ctrlDecode_simEnv : CtrlDecode`,
  `Typing.stateTyping_simEnv : State.StateTyping`, `Typing.stateDecode_simEnv :
  State.StateDecode`, `Typing.rTyping_simEnv : RefsGC.RTyping`, `Typing.exnTyping_simEnv' :
  Exn.Typing` (through `typedV_heaptype`, `typedV_valtype`, `typedV_blocktype`).
* `Typing.assumptions_of'`: `Whole.Assumptions` from its non-typing fields alone.
* `Typing.typed_vals`: `Typed` holds for real configurations (empty store, any locals, the empty
  module instance, any sequence of value constants), so it is not vacuous.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.hasTyp_num_float' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.hasTyp_num_float

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.typedV_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.typedV_val

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.valV_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.valV_injective

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.ctrlDecode_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.ctrlDecode_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.assumptions_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.assumptions_of'

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Typing.typed_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Typing.typed_vals
