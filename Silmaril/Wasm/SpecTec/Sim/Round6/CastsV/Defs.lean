module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track casts-v: definitions

Track casts (pass 2) proved the cast leaf `Target.Casts Int.backend` from track reading's
`Reading.RefOkBB`, which track refokbb refuted (`RefOkB.not_refOkBB`). Its restatement
`RefOkB.RefOkBV` asks `Ref_ok` to agree with Core's `RefOk` only on a Core-valid store (`StoreOk`)
and a Core-valid closed type (`TyOk {}`). This track re-derives the cast leaf from `RefOkBV`. The
two validity facts hold at every cast of a valid configuration, and they are carried, as a
syntactic invariant of the code, under labels, handlers and frames.

* `castTy? i`: the reference type that the cast instruction `i` tests against (`rt₂` for the
  `br_on_cast` pair), or `none`.
* `CastsOkA M a`, `CastsOkL M l`: every cast at the top level of `a` / `l` (not under a block,
  but under labels, handlers and frames, with the innermost frame's module) has an instantiated
  type valid in `{}`.
* `CastsInv c`: `StoreOk c.store` and `CastsOkL c.frame.module c.code`. It follows from
  `ConfigOk` (`Round6.CastsV.castsInv_of_configOk`).
* `CastRefOk env hn V`: `RefOkAtB` holds at the store and instantiated cast type of each top-level
  cast pair `[ref r, i]` satisfying `V`, on a typed store. It is the hypothesis that the
  generalized cast lemmas of track reading and track casts take, in place of `RefOkBB`.

See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.CastsV

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The reference type a cast instruction tests against: `rt` for `ref.test rt`/`ref.cast rt`,
`rt₂` for `br_on_cast l rt₁ rt₂`/`br_on_cast_fail l rt₁ rt₂`; `none` otherwise. -/
def castTy? : Instr → Option RefType
  | .refTest rt => some rt
  | .refCast rt => some rt
  | .brOnCast _ _ rt₂ => some rt₂
  | .brOnCastFail _ _ rt₂ => some rt₂
  | _ => none

mutual
/-- Every cast at the top level of `a`, under labels, handlers and frames, has an instantiated
type valid in `{}`; `M` is the module of the innermost enclosing frame. -/
def CastsOkA : ModuleInst → Admin → Prop
  | M, .plain i => ∀ rt, castTy? i = some rt → TyOk {} (M.instRef rt)
  | M, .label _ _ b => CastsOkL M b
  | M, .handler _ _ b => CastsOkL M b
  | _, .frame _ fr b => CastsOkL fr.module b
  | _, _ => True

/-- `CastsOkA` at every instruction of a code sequence. -/
def CastsOkL : ModuleInst → List Admin → Prop
  | _, [] => True
  | M, a :: l => CastsOkA M a ∧ CastsOkL M l
end

/-- **The validity facts the cast rules need, at a configuration**: the store is valid in Core,
and every cast of the code has a closed, valid instantiated type. -/
def CastsInv (c : Config H) : Prop := StoreOk c.store ∧ CastsOkL c.frame.module c.code

/-- **`RefOkAtB` at the casts satisfying `V`**: at a top-level cast pair `[ref r, i]` satisfying
`V`, on a typed store, `Ref_ok` under `DDerivesB` is Core's `RefOk` at the instantiated cast
type. -/
structure CastRefOk (env : Env) (hn : H → String) (V : Config H → Prop) : Prop where
  /-- At a cast pair. -/
  refOk : ∀ (s : Store H) (f : Frame) (r : Ref) (i : Instr) (rt : RefType), castTy? i = some rt →
    V ⟨s, f, [.ref r, .plain i]⟩ → TypedV env storeT (storeV hn s) →
      Reading.RefOkAtB env hn s (f.module.instRef rt)

end Silmaril.Wasm.SpecTec.Sim.Round6.CastsV
