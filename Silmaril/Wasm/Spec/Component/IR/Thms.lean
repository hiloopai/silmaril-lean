module

public import Silmaril.Wasm.Spec.Component.IR.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Ground

@[expose] public section

/-!
# The IR semantics of components: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Ground` (and short ones in
`Silmaril.Wasm.Spec.Component.IR.Defs`).

* `mapAll_prefix`, `irTraces_good`: observed traces of IR strategies form good sets;
* `irTraces_call_ret`, `irTraces_call_trap`: a play `ask (j, vals vs) · ans (vals ws)` (or
  `· ans none`) of the IR strategy is the trace `call j vs · ret j (returns ws)` (or
  `· ret j traps`) with values read through `toRefVal`;
* `irSem_level`: every IR program sits at an interface of level at most `aggregate` (no strings,
  lists, handles, streams or futures in Silmaril's IR).

Grounding of the IR traces in Core 3.0 and in the reference machine:
`Silmaril.Wasm.Spec.Component.Ground.Thms`.
-/
