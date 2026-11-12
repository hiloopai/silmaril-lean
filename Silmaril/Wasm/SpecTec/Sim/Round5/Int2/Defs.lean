module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass-2 integration: definitions

Pass 2 showed that pass 1's leaves `Round5.Int.Open` can never all hold:

* `vecAgree` failed because `Prims.builtins` did not answer `$lanes_`
  (`Round5.Simd.not_vecAgree_of_lanes`). Track simd fixed the builtins.
* `hostRespects` fails for a finite `HostOk` host (`Round5.FwdRef.not_open_all`): `storeV` is not
  injective on stores holding invalid instructions.

Each track restated its own leaves. This header combines the restatements:

* `Open2`: the leaves still open after pass 2. Compared with `Round5.Int.Open`:
  * `hostRespects` is restated as `HostRespectsT` (calls on typed store images);
  * `newDataNum` is dropped (proved, `Round5.FwdRef.newDataNumB_builtins`);
  * `vecAgree` is narrowed to `VecAgreeOps` (its 16 lane-wise operator fields);
  * `pureOpen` is narrowed to `PureOpenVtestop` (rule 64 only);
  * `read` is restated as `ReadRest` (under `ReadValidS`, minus its proved rules).
  `Open2` asks no more than `OpenT` (`Round5.Int2.open2_of_openT`).
* `WitnessBnd`: the `CALL_REF` annotations of a typed witness `d ≈ c` are bounded when `c`'s
  code is. The backward multi-step relation needs it, because `ReadValidS` has to
  carry over to the witness. Not proved.
* `MultiOk2`: `MultiOk` with the backward relation also under `WitnessBnd`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)

variable {H : Type}

/-- **The leaves still open after round 5, pass 2**, at one encoding, host and profile. -/
structure Open2 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding at calls on typed store images. -/
  hostRespects : FwdRef.HostRespectsT (simEnv (BI P hn host)) hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- The lane-wise vector operators agree with Core. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P
  /-- `Step_pure` 64 (`vtestop`), backward. -/
  vtestop : Simd.PureOpenVtestop hn P host
  /-- The `Step_read` rules still open, backward, under `ReadValidS`. -/
  read : Round5.Read.ReadRest hn P host

/-- **The `CALL_REF` annotations of typed witnesses are bounded**: a typed `d ≈ c` has bounded
code when `c` has. -/
def WitnessBnd (B : Builtins) (hn : H → String) : Prop :=
  ∀ c d : Config H, Round4.AdminsBnd c.code → Bwd.ConfigEq c d → Typed (simEnv B) hn d →
    Round4.AdminsBnd d.code

/-- **The composable one-step simulations for the restated target, pass 2**: track multi's
`MultiOk`, with the backward relation under `SuccTyped` and `WitnessBnd`. -/
def MultiOk2 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        Multi.FwdRel B hn (Profile.spec nd r) host ∧
          (Multi.SuccTyped B hn → WitnessBnd B hn →
            Multi.BwdRel B hn (Profile.spec nd r) host)

end Silmaril.Wasm.SpecTec.Sim.Round5.Int2
