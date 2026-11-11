module

public import Silmaril.Wasm.Binaryen.Deferred.Thms
public import Silmaril.Wasm.Binaryen.CodeSimTyped
public import Silmaril.Wasm.Binaryen.ConstBranchSim
public import Silmaril.Wasm.Execution.Core.Sim.TypedLocalBounds
public import Silmaril.Wasm.Binaryen.DropGet.Defs
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
import Silmaril.Proofs.Wasm.Binaryen.DropGet.Reverse
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # Dropped local reads: soundness

The proofs are in `Silmaril.Proofs.Wasm.Binaryen.DropGet.{Sound,Reverse}`. Both
simulation directions hold at an arbitrary numerical profile under the closed host:

* `dgBaseSim` (the original simulates the result, in `Sound.lean`);
* `dgReverseTypedSim` (a silmaril `TypedBaseSim`: typing of the original's active `local.get x` gives a value of `x` in the actual frame).

`dropGet_sound_any` gives exact export equivalence of the raw rewrite for valid input
and output, and `dropGetChecked_sound_any` gives validity and exact export equivalence
of the checked stage from validity of the input alone, at **every** numerical
profile. No determinism of the profile is used.

This header packages the stage for silmaril's executable stage contract
`Exe.StageOk` (stated at deterministic profiles) and as an arbitrary-profile shared
pass `ArbitraryProfile.EquivPass` (used by the selected-stage byte driver).
-/

namespace Silmaril.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

section Soundness

variable {H : Type} {P : Profile}

/-- **The raw rewrite is exactly export-equivalent** for valid input and output, at every
numerical profile under the closed host. -/
theorem dropGet_sound_any {m : BModule} (hm : m.Ok) (hm' : (dropGet m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (dropGet m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.DropGet.dropGet_sound_any hm hm'

/-- **The checked stage keeps validity and is exactly export-equivalent**, with validity of
the input as its only premise, at every numerical profile under the closed host. -/
theorem dropGetChecked_sound_any {m : BModule} (hm : m.Ok) :
    (dropGetChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (dropGetChecked m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.DropGet.dropGetChecked_sound_any hm

end Soundness

/-- **The stage satisfies silmaril's executable stage contract.** -/
theorem dropGet_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    Exe.StageOk o H dropGetChecked :=
  fun _ hm => dropGetChecked_sound_any hm.ok

/-- **The stage as an arbitrary-profile shared pass.** -/
def dropGetP {H : Type} (P : Profile) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := dropGetChecked
  inv_run hm := (dropGetChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (dropGetChecked_sound_any hm).2

/-- The bodies of `dropGet m` are those of `m` with `dgBI` pairs rewritten (the syntactic body
relation of the soundness proof; `Silmaril.Wasm.FnInst.Ground` reuses it). -/
theorem dropGet_bodiesRel (m : BModule) : ModuleBodiesRel dgBI m.lower (dropGet m).lower :=
  Silmaril.Proofs.Wasm.Binaryen.DropGet.dropGet_bodiesRel m

end Silmaril.Wasm.Binaryen.DropGet
