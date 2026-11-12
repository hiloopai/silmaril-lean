module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Transfer.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, track transfer: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Transfer`; see `docs/projects/spectec/README.md`.

* `sstepB_iff_of_not_castRedex`: at the image of a Core configuration whose redex is not a cast,
  the backend reading `Reading.SStepB` and the declarative reading `SStep` have the same
  successors, for every `B` and every encoding. No hypothesis on the configuration, the
  encoding, the host or the profile.
* `transfer_backend`, `transfer_backend_BI`: **`Round6.Target.Transfer Int.backend B hn` holds**,
  in particular at `B := Round4Int.BI P hn host`.
* `wholeStepValidR_backend_of_casts`: `Round6.Task.wholeStepValidR Int.backend` from the cast
  leaf `Round6.Target.Casts` alone.
* Along the way: `sReadB_iff_noCast` (`Step_read` agrees under both readings at the image of a
  configuration without a cast redex, whatever casts follow the redex), `castRedex_of_body_readK`
  (the eight cast rules fire only on cast redexes, under any interpretation of their premises),
  `firesB_iff_swap` (a rule with one leading relational premise transfers when the readings agree
  at that premise's instances).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.sstepB_iff_of_not_castRedex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.sstepB_iff_of_not_castRedex

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.transfer_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.transfer_backend

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.transfer_backend_BI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.transfer_backend_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.wholeStepValidR_backend_of_casts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.wholeStepValidR_backend_of_casts

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.sReadB_iff_noCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.sReadB_iff_noCast

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.castRedex_of_body_readK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.castRedex_of_body_readK

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.firesB_iff_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.firesB_iff_swap

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.plain_read_of_not_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Transfer.plain_read_of_not_mem
