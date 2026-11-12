module

public import Silmaril.Wasm.Spec.Run.Defs
public import Silmaril.Proofs.Wasm.Spec.Run.Basic

@[expose] public section

/-!
# The verified refuter: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Run.Basic`.

* `hasValB_sound`, `typedB_sound`, `ofResult?_of_resultTypedB`: decidable typing of values and
  results is sound.
* `invokeOk_of_wellFormed`: typed arguments of an export of a well-formed instance meet the
  premises of `$invoke`.
* **`refuteRet_sound`**: if `refuteRet o n p j args Q = .refuted` for a well-formed program and
  typed `args`, then `p` does not satisfy the return postcondition `Q` of `j` in
  `inst (retPost …) (wasmSem P)`, for every profile `P` admitting the steps of `profile o`; the
  witness is the trace `[call j args, ret j b]` of a Core run (`call_ret_mem_iff`).
  `refuteRet_sound_spec`: in particular for the specification profiles `Profile.spec nd {}`.
-/
