module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Defs

/-!
# The forward direction at wasm-3.0, finished: definitions

`FwdX30.ReadHeadX` classifies 90 of the 99 Core constructors labelled `Step_read`. This header
names the other nine.

* `CastRead c is'`: the eight cast steps (`ref.test`, `ref.cast`, `br_on_cast`,
  `br_on_cast_fail`, each with both outcomes), as round 6's `Casts.CastTop` from `c` to
  `⟨c.store, c.frame, is'⟩`. Under the backend reading of `stepModel` these rules are not the
  declarative ones; their facts are taken from the cast leaf of `Round6.Int.openR_backend`.
* `RetFrameAddr c is'`: `return_call_ref` out of a frame at an address. Core resolves the
  `CALL_REF` index against the exited frame's module (`Admin.retToCallIn`), while SpecTec keeps
  it (`Admin.retToCall`). So its forward fact is a `Step_read` fact only up to `ConfigEq`: to
  SpecTec's code `vals vs ++ [ref (func a), c.retToCall]`, which is `CodeEq` to Core's
  (`Bwd.codeEq_retToCall`) and not equal to it in general (`Sim.adminToV_retToCallIn_ne`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30Fin

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-- **The eight cast rules of `Step_read`**, as Core head steps that keep the state. -/
def CastRead (c : Config H) (is' : List Admin) : Prop :=
  Round6.Casts.CastTop c ⟨c.store, c.frame, is'⟩

/-- **`Step_read/return_call_ref-frame-addr`**, as Core's head step (with the resolved index). -/
inductive RetFrameAddr : Config H → List Admin → Prop where
  /-- Core's `Step.returnCallRefFrameAddr`. -/
  | mk {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat} {c : Admin}
      {rest : List Admin} {fn : FuncInst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
      (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
      (hn : vs.length = ps.length) :
      RetFrameAddr ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
        (vals vs ++ [.ref (.func a), c.retToCallIn fi.module])

end Silmaril.Wasm.SpecTec.Institution.FwdX30Fin
