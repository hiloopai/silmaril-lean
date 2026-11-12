module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass 2, track fwdref: definitions

`Prims.HostRespects hn host` (a field of `Round5.Int.Open`) fails for a finite `HostOk` host
(`Round5.FwdRef.not_hostRespects_junkHost`): `storeV` sends stores holding invalid instructions to
one image, and `HostOk` says nothing about such stores. Every consumer of `HostRespects` (the
forward `call_ref` host rules and `Bwd.HostStepsV`) uses it only at a call whose store image is
part of a *typed* configuration image, and the junk image of an invalid instruction (`.tuple []`)
is not an `instr`. So this header restates it there:

* `HostRespectsT env hn host`: `HostRespects` at calls whose store image is a typed `store`. It
  follows from `HostRespects` (`hostRespectsT_of`), and for every host from injectivity of
  `storeV` on stores with typed images (`hostRespectsT_of_storeInj`).
* `OpenT`: `Round5.Int.Open` with `HostRespectsT` for `HostRespects` and without `newDataNum`
  (discharged, `Round5.FwdRef.newDataNumB_builtins`). It is no stronger than `Open`
  (`openT_of_open`), and gives `PartsOkR` (`partsOkR_of_openT`).
* `StoreInjT env hn`: `storeV hn` is injective on stores whose image is a typed `store`; a fact
  about the encoding alone (no host). Not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **`Prims.HostRespects` at calls on a store whose image is a typed `store`**: two host calls
with the same SpecTec image, the first on such a store, have outcomes with the same images. -/
def HostRespectsT (env : Env) (hn : H → String) (host : HostSemantics H) : Prop :=
  ∀ (h h' : H) (s s' : Store H) (vs vs' : List Val), TypedV env storeT (storeV hn s) →
    Prims.hostArgs hn h s vs = Prims.hostArgs hn h' s' vs' →
    ∀ o, host h s vs o → ∃ o', host h' s' vs' o' ∧ outcomeV hn o = outcomeV hn o'

/-- **`storeV` is injective on stores with typed images** (a fact about the encoding alone). -/
def StoreInjT (env : Env) (hn : H → String) : Prop :=
  ∀ s s' : Store H, TypedV env storeT (storeV hn s) → storeV hn s = storeV hn s' → s = s'

/-- **The leaves still open after round 5, pass 2, track fwdref**: `Round5.Int.Open` with
`HostRespectsT` for the refuted `HostRespects`, and without `newDataNum` (proved). -/
structure OpenT (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding at calls on typed store images. -/
  hostRespects : HostRespectsT (simEnv (BI P hn host)) hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- Family V's agreement of the vector primitives (backward vector rules). -/
  vecAgree : Vec.VecAgree (simEnv (BI P hn host)) P
  /-- `Step_pure` 64, 70–73, backward. -/
  pureOpen : BwdStep.PureOpenV hn P host
  /-- The remaining `Step_read` rules, backward. -/
  read : Int.ReadOpen hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
