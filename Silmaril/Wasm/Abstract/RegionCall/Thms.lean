module

public import Silmaril.Wasm.Abstract.RegionCall.Defs
public import Silmaril.Wasm.Cfg.Region.Defs
import Silmaril.Proofs.Wasm.Abstract.RegionCall.Basic

/-!
# The closed oracle is `Region.CallSound`: theorems

* `callSoundAnn_closedCallOk`: the same for every `call_ref` annotation `c`
  (`c.IsCallRef`), as tail calls need (`return_call_ref-frame-addr` calls with
  `c.retToCallIn fi.module`).
* `callSound_closedCallOk`: for every profile `P` and host, `closedCallOk` is
  `Cfg.Region.CallSound P host`. Every oracle answer
  `closedCall s a us (s₁, fl)`, on an arity-checked store and a typed
  invocation, is a Core 3.0 run of `vals us ++ [ref.func a, call_ref]`, in
  **any** caller frame, to:
  * the top `rs.length` values in result order, when `fl.retVals = some vs`;
  * a trap, when `fl = .trap`.
  It never throws (`Interp.steps_callRef_of_eval`).

So `Region.run_soundC` with `C := closedCallOk` holds with no assumed oracle
hypothesis. The restriction is deliberate: `CallSound` quantifies over every
store, and soundness of native evaluation is only proved on arity-checked
stores and typed invocations; the unrestricted `closedCall` is not claimed.
Divergence and completeness of the closed oracle are
`Silmaril.Wasm.Abstract.Oracle` (`closedCall_core_iff`,
`closedCall_none_iff_diverges`, under `StoreOk`/`NativeFuncsOk`/`StoreChk`/
`InvokeOk`).
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The checked closed oracle is sound for Region calls**, every profile and host. -/
theorem callSound_closedCallOk (P : Numerics.Profile) (host : HostSemantics H) :
    Cfg.Region.CallSound P host (closedCallOk (H := H)) :=
  Silmaril.Proofs.Wasm.Abstract.RegionCall.callSound_closedCallOk P host

/-- **`callSound_closedCallOk` for every `call_ref` annotation** (as tail calls need). -/
theorem callSoundAnn_closedCallOk (P : Numerics.Profile) (host : HostSemantics H)
    (s s₁ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
    (us : List Val) (fl : Binaryen.Flow) (c : Admin) (hc : c.IsCallRef)
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : us.length = ps.length) (hcall : closedCallOk (H := H) s a us (s₁, fl)) :
    (∀ vs, fl.retVals = some vs → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
        ⟨s₁, f, vals (vs.take rs.length).reverse⟩) ∧
    (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₁, f, [.trap]⟩) ∧
    (∀ t, fl = .throw t → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
        ⟨s₁, f, throwing t⟩) :=
  Silmaril.Proofs.Wasm.Abstract.RegionCall.callSoundAnn_closedCallOk P host s s₁ f a fi ps rs us fl c
    hc hfi hty hn hcall

end Silmaril.Wasm.Abstract
