module

public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Backward

/-!
# SpecTec ↔ Core 3.0, aggregates track: what is proved

* `Proved.lean`: family R's 24 proved `AggregateStep` constructors as `FwdP (simEnv B)`
  obligations (`fwd_structGetNull`, …, `fwd_arrayInitElemZero`); `array.len-array` and
  `array.fill-succ` under `Bounded s`.
* `Eval.lean`: the aggregate state functions (`$type`, `$structinst`, `$arrayinst`,
  `$moduleinst`, `$with_struct`, `$with_array`, `$add_structinst`, `$add_arrayinst`) evaluated by
  their clauses (`aggDefs_simEnv`); family R's `RStoreFuns` follows from its `$inst_reftype` field
  alone (`rStoreFuns_of_instReftype`).
* `Read.lean`: `array.get-array` (rule 79) forward for unpacked fields.
* `Store.lean`: `$with_array`/`$with_struct` evaluated; `array.set-array` (`Step` 35) forward for
  unpacked fields; the packed-field finding (`$packfield_` takes its unpacked clause).
* `Struct.lean`: two-domain iterations; `struct.get-struct` (rule 71) and `struct.set-struct`
  (`Step` 31) forward for unpacked fields.
* `Alloc.lean`: `array.new` (`Step_pure` 41, all values), `array.new_fixed` (`Step` 32) and
  `struct.new` (`Step` 29) forward for unpacked fields; `$add_arrayinst`/`$add_structinst`
  evaluated.
* `Forward.lean`: `fwd_aggregate`, `Forward.aggregate` at `simEnv B` on the covered fragment
  (`AggCovered`, `Unpacked`, `Bounded`).
* `Backward.lean`: `Backward.read` at rules 70, 77, 80 (`bwd_structGetNull`, `bwd_arrayGetNull`,
  `bwd_arrayLenNull`), under the decoders `CtrlDecode` and `AggDecode` (assumed).

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim.Aggregates

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Aggregates.fwd_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fwd_aggregate

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Aggregates.rStoreFuns_of_instReftype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rStoreFuns_of_instReftype
