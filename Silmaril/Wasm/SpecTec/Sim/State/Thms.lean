module

public import Silmaril.Wasm.SpecTec.Sim.State.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Variable
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Grow
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Backward

/-!
# SpecTec ↔ Core 3.0, family M (state): what is proved

Core → SpecTec, at `simEnv B`, under the encoding's `TypingFacts` and the immediate-typing facts
`StateTyping`:

* `fwd_variable_` — the `Forward.variable_` obligation: `local.get`, `local.set`, `local.tee`,
  `global.get`, `global.set` (`Step_read` 23, 24; `Step` 11, 12; `Step_pure` 30), via the
  per-rule constructions `sread_localGet`, `sread_globalGet`, `sstep_localSet`,
  `sstep_globalSet`, `spure_localTee`.
* tables: `fwd_tableGetOob`, `fwd_tableGetVal`, `fwd_tableFillOob` (`Step_read` 25, 26, 28),
  `fwd_tableSetOob`,
  `fwd_tableSetVal`, `fwd_elemDrop` (`Step` 13, 14, 17), each of the type of the matching
  `TableStep` case of `Forward.table`, via `sread_tableGetOob`, `sread_tableGetVal`,
  `sread_tableFillOob`, `sstep_tableSetOob`, `sstep_tableSetVal`, `sstep_elemDrop`.
* growth failing and segment drop: `fwd_tableGrowFail`, `fwd_memoryGrowFail` (`Step` 16, 27; in
  any profile, since the SpecTec rules have no premise), `fwd_dataDrop` (`Step` 28), via
  `sstep_tableGrowFail`, `sstep_memoryGrowFail`, `sstep_dataDrop`; the result
  `$inv_signed_($size(at), -1)` is `evalExp_growFailResult`.
* SpecTec → Core: `bwd_pure_localTee`, the `Backward.pure 30` obligation (`local.tee`), via the
  inversion `fires_localTee_inv`, given the decoders `StateDecode` (a typed `val` image is a value;
  a `LOCAL.TEE` image is `local.tee`'s).
* `stateDefs_simEnv`, `growDefs_simEnv` — the accessor definitions the state rules evaluate through, by computation;
  `evalExp_local`, `evalExp_global`, `evalExp_table`, `evalExp_mem`, `evalExp_elem`,
  `evalExp_data`, `evalExp_withLocal`, `evalExp_withGlobal` evaluate them on state values.

Coverage and gaps are tracked in `docs/projects/spectec/README.md`, family M.
-/
