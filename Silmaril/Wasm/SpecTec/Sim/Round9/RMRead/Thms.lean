module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMRead.Assemble

/-!
# Round 9, rm: the structured `Step_read` rules at memory SIMD code (round 9, pass 1, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.RMRead`; see `docs/projects/spectec/README.md`.

* `read_exits`: the nine `Step_read` rules that move a `return_call_ref` or a thrown exception
  out of a label, handler or frame (8, 9, 10, 13, 14, 15, 16, 19, 20) hold backward at `configVD`,
  in every `simEnv B`, at every configuration, with no typing hypothesis.
* `read_struct`: with `block` (0), `loop` (1), `return_call_ref-frame-addr` (11),
  `throw_ref-handler-catch` (17), `-catch_ref` (18) and `try_table` (22), at the concrete
  primitives (`$blocktype_` reads only the frame: `blocktypeD_inv`; `$funcinst`, `$exninst`,
  `$tagaddr` at `stateVD`: `funcTypeD_of_eval`, `applies_exninstD`, `applies_tagaddrD`).
* `adminsMS_of_handlerNext`: `throw_ref-handler-next` (21) fires only at memory-SIMD-free code.
* `restMSHCI_of_J`, `wholeStepValidRM_of_restDPJ`: `Round7.MemSimd.Task.wholeStepValidRM` from
  `OpenRMRestDPJ`, which has no per-rule obligation at memory SIMD code left: only round 8's
  `firesRead`, `forward`, `castsFwd` and `castsBwd`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.read_exits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_exits

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.read_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_struct

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.wholeStepValidRM_of_restDPJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPJ

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
