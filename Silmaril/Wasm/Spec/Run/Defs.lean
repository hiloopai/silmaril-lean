module

public import Silmaril.Wasm.Spec.Verdict.Defs
public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

@[expose] public section

/-!
# A verified refuter for return postconditions

`refuteRet o n p j args Q` runs export `j` of the Wasm program `p` on `args` with silmaril-lean's
verified interpreter (`runInvoke?`, deterministic profile `profile o`, fuel `n`, no host). If the
run ends in a result typed by the export's result types whose behaviour `Q` rejects, the verdict
is `refuted`; otherwise `unknown`. It is a pure, computable function (for decidable `Q`), suited
to a service: a `refuted` verdict comes with the concrete counterexample trace
`[call j args, ret j b]`.

Soundness (`refuteRet_sound`, `Silmaril.Wasm.Spec.Run.Thms`): a `refuted` verdict means the program
does **not** satisfy the return postcondition in `inst (retPost …) (wasmSem P)` for every
profile `P` admitting the deterministic steps of `profile o` (for instance every specification
profile `Profile.spec nd {}`, by silmaril-lean's `Step.deterministic_refines_spec`).

`Verdict` and the executable typing checks (`typedB`, `resultTypedB`) are in
`Silmaril.Wasm.Spec.Verdict`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- **The refuter.** -/
def refuteRet {X : WIface} (o : GrowOracle) (n : Nat) (p : WasmProg X) (j : X.Exp)
    (args : List Val) (Q : Behaviour Val → Bool) : Verdict :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? o n p.store (p.inst.addr j) args with
  | some (_, _, some r) =>
    if resultTypedB (X.exports.get j).results r && !Q r.toBehaviour then .refuted else .unknown
  | _ => .unknown

end Silmaril.Wasm.Spec
