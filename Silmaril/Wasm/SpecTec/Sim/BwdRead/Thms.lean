module

public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Dispatch

/-!
# SpecTec ↔ Core 3.0, round 3, track bwd-read: what is proved

* `BwdRead.read_done`: for every `B` with `NoAcc B` (the state accessors are left to their
  clauses), every `Step_read` rule in `readDone`
  (23, 24, 25, 26, 28, 53, 70, 77, 80, 82, 93, 98)
  has its backward lemma: whatever it derives from the image of a typed configuration is the
  image of a Core `Step_read` successor. Nothing else is assumed: the decoders are proved
  (`aggDecode`, the tag decoders, `Typing.ctrlDecode_simEnv`, `Typing.stateDecode_simEnv`).
* `BwdRead.noAcc_builtins`: `NoAcc` holds for the concrete `Prims.builtins`.
* `Integrate.RemainingW.read` no longer lists these rules; `Integrate.remaining_of_w`
  dispatches them, so `Integrate.backward_concrete` no longer assumes them.
* Toolkit: `evalExp_call1_inv` (a call of a single-clause premise-free definition, inverted),
  `evalExp_local_inv`, `evalExp_storeAcc_inv`, `table_inv`, `elem_inv`, `tableLen_inv`,
  `elemLen_inv`, `decode_aconst`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim.BwdRead

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdRead.read_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_done

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdRead.noAcc_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noAcc_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdRead.aggDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aggDecode
