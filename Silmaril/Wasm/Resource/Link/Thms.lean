module

public import Silmaril.Wasm.Resource.Link.Defs
public import Silmaril.Proofs.Wasm.Resource.Link.Basic

@[expose] public section

/-!
# Protocols and the Wasm game: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Link.Basic`. Every profile `P`; no determinism is assumed.

* `LTSInv.run`, **`LTSInv.accepts`**: a protocol invariant of a transition system makes every play
  of `Strategy.ofLTS L` accepted (receptive plays included, given `OTotal`).
* **`dlts_accepts`**: for a scalar instance, a protocol invariant of `I.dlts P s` (host-free Core
  steps silent) gives acceptance of every play of `I.strategy P s`.
* `models_of_plays`, `not_models_of_play`: from plays to sentences of `protoLogic` over
  `wasmSem P`, and refutation by one rejected play.
* **`provider_sound`**: `ProvSat P I π Inv` (one every-run Hoare triple per export and protocol
  state, `Silmaril.Wasm.Logic`), `ImportNeutral π`, `OTotal π` and `Inv π.init s` imply that every
  play of `I.strategy P s` is accepted (the invariant `ProvJ`, after
  `Silmaril.Proofs.Wasm.Logic.GameLink.Strategy`).
-/
