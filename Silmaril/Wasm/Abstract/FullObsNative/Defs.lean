module

public import Silmaril.Wasm.Abstract.StoreCall.Defs
public import Silmaril.Wasm.Abstract.FullObs.Defs

/-!
# Full observations of the exposed native body, filtered by an oracle

The exposed native body `StoreCall.denListE es f stk` makes every internal call a visible event
of `StoreCall.CallSig H`, answered by the store and flow the call ends in. As a body from
`PUnit` (`nbody es f stk`) it has a full observation `FullObs.toFull` (finished paths, lifted
by `BodyTrace.liftCall`/`endOf`, and productive runs). Filtering both parts by an oracle `C`
(`AnsL C`, `AnsLS C`: every lifted call event is answered as `C` allows) gives `obsC C es f stk`,
the observation of the code when its calls are answered by `C`. Theorems in
`Silmaril.Wasm.Abstract.FullObsNative.Thms`: it is exact for the native semantics `EvalO C`
(finite part) and for local divergence `LocalDivO C` (silent and productive runs), and at the H2
oracle `C = hostCall host` for `EvalH host` and `LocalDivO (hostCall host)`.

This is the native H2 host slice only: no extended call forms, no exception handlers, no
pending tail calls.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.FullObsNative

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall

variable {H : Type}

/-- The exposed native body of a list of trees, as a body from `PUnit`. -/
noncomputable def nbody (es : List BExpr) (f : Frame) (stk : List Val) :
    Hom (CallSig H) (St H) PUnit.{2} PUnit.{2} Res :=
  fun _ => denListE es f stk

/-- Every lifted call event of the log is answered as `C` allows. -/
def AnsL (C : Silmaril.Wasm.Abstract.CallRel H) (c : List (Call (liftSig (CallSig H)))) : Prop :=
  ∀ x ∈ c, C x.1.down.2.2 x.1.down.1 x.1.down.2.1 x.2.down

/-- Every lifted call event of the stream is answered as `C` allows. -/
def AnsLS (C : Silmaril.Wasm.Abstract.CallRel H) (ω : Nat → Call (liftSig (CallSig H))) : Prop :=
  ∀ n, C (ω n).1.down.2.2 (ω n).1.down.1 (ω n).1.down.2.1 (ω n).2.down

/-- **The full observation of the exposed native body, filtered by the oracle `C`.** -/
noncomputable def obsC (C : Silmaril.Wasm.Abstract.CallRel H) (es : List BExpr) (f : Frame)
    (stk : List Val) : FullFun (liftSig (CallSig H)) (St H) PUnit.{2} Res :=
  (fun σ a => {x | x ∈ (FullObs.toFull (nbody es f stk)).1 σ a ∧ AnsL C x.1},
    fun σ a => {ω | ω ∈ (FullObs.toFull (nbody es f stk)).2 σ a ∧ AnsLS C ω})

end Silmaril.Wasm.Abstract.FullObsNative
