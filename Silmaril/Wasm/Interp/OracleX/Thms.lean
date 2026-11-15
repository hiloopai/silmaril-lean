module

public import Silmaril.Proofs.Wasm.Interp.OracleSimX
public import Silmaril.Proofs.Wasm.Interp.OracleCloseX

/-!
# Core 3.0 adequacy of the indirect and reference calls (F4, call forms)

`evalOXT_good`: with a sound oracle (`OracleSoundX`: as `OracleSound`, the
callee's Core run stated for every `call_ref` form), every
`Abstract.CallXT.EvalOXT C` run of code passing the arity check extended by
`irExt` is a Core 3.0 run, with the arity invariants, at every profile and
host. `EvalOXT` is `CallX.EvalOX` whose `call_indirect`/`call_ref` callees have
the annotated type's counts; it forgets to `EvalOX` (`CallXT.EvalOXT.forget`).

**Scope (intermediate).**

* **Store check.** `ArityGoodE irExt`, `CoreGoodE irExt` and `OracleSoundX`
  assume and preserve `StoreChkE irExt s.funcs`: every function of the store
  passes the extended check, so store functions may hold indirect and
  reference calls. A natively checked store qualifies
  (`storeChkE_of_storeChk`). An oracle answer that appends functions must keep
  `StoreChkE irExt` (`FuncsGoodE irExt`); old functions transfer
  (`storeChk_of_funcsExtE`).
* Tail calls: `irExt` does not describe `return_call*`, so `chkE irExt`
  rejects code containing them and nothing is claimed for it. A tail call
  replaces the caller's frame in Core 3.0; its adequacy is a frame-level
  statement, still to come.
* The arity premises of `EvalOXT` are discharged from typing in a follow-up
  (for `call_indirect` from the successful `ref.cast`, for `call_ref` from the
  reference's type).
* **The oracle is closed** on good stores (`GoodStoreX`: valid function and
  instance types, bodies without `call_ref` whose indirect calls name instance
  types): `oracleSoundX_closedX`, by least-fixpoint induction. Hence
  `evalOX_closed_good`: closed extended runs are Core 3.0 runs, no oracle
  assumed. `call_ref` waits on its typed discharge.
-/

public section

namespace Silmaril.Wasm.Interp.OracleX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp (irExt OracleSoundX ArityGoodE CoreGoodE)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Forward simulation of the indirect and reference calls.** -/
theorem evalOXT_good {C : Abstract.CallRel H} (hC : OracleSoundX P host C) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallXT.EvalOXT C s f stk es r) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOXT_goodE hC h

/-- A sound oracle for every `call_ref` form is sound for `call`, for the store
check extended by `irExt`. -/
theorem oracleSound_of_X {C : Abstract.CallRel H} (hC : OracleSoundX P host C) :
    Silmaril.Wasm.Interp.OracleSoundE irExt P host C :=
  hC.sound

/-- **The closure on good stores is a sound oracle.** -/
theorem oracleSoundX_closedX :
    OracleSoundX P host (Silmaril.Wasm.Interp.closedX (H := H)) :=
  Silmaril.Wasm.Interp.oracleSoundX_closedX

/-- **Closed extended runs are Core 3.0 runs** (indirect calls, good stores, native store
check as above). -/
theorem evalOX_closed_good {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.CallX.EvalOX Abstract.XRecursion.closedCallX s f stk es r)
    (hG : Silmaril.Wasm.Interp.GoodStoreX s) (hm : Abstract.CallXT.TyTypes f.module)
    (hx : Abstract.CallXT.indOkL f.module es = true) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r :=
  Silmaril.Wasm.Interp.evalOX_closed_goodE h hG hm hx

end Silmaril.Wasm.Interp.OracleX
