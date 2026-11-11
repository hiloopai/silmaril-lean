module

public import Silmaril.Wasm.Binaryen.Deferred.Thms
public import Silmaril.Wasm.Binaryen.TeeForm.Defs
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank
import Silmaril.Proofs.Wasm.Binaryen.TeeForm.Reverse
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # Tee formation (a SimplifyLocals subrule): soundness

The proofs are in `Silmaril.Proofs.Wasm.Binaryen.TeeForm.{Sound,Reverse}`. Both
simulation directions hold at an arbitrary numerical profile under the closed host:

* `tfBaseSim` (the result simulates the original, in `Sound.lean`);
* `tfReverseSim` (a `Deferred.DeferredBaseSim`: the original's read-back after its store is a forced step).

`teeForm_sound_any` gives exact export equivalence of the raw rewrite for valid input
and output, and `teeFormChecked_sound_any` gives validity and exact export equivalence
of the checked stage from validity of the input alone, at **every** numerical
profile. No determinism of the profile is used.

This header packages the stage for silmaril's executable stage contract
`Exe.StageOk` (stated at deterministic profiles) and as an arbitrary-profile shared
pass `ArbitraryProfile.EquivPass` (used by the selected-stage byte driver).
-/

namespace Silmaril.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

section Soundness

variable {H : Type} {P : Profile}

/-- **The raw rewrite is exactly export-equivalent** for valid input and output, at every
numerical profile under the closed host. -/
theorem teeForm_sound_any {m : BModule} (hm : m.Ok) (hm' : (teeForm m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (teeForm m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.TeeForm.teeForm_sound_any hm hm'

/-- **The checked stage keeps validity and is exactly export-equivalent**, with validity of
the input as its only premise, at every numerical profile under the closed host. -/
theorem teeFormChecked_sound_any {m : BModule} (hm : m.Ok) :
    (teeFormChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (teeFormChecked m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.TeeForm.teeFormChecked_sound_any hm

end Soundness

/-- **The stage satisfies silmaril's executable stage contract.** -/
theorem teeForm_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    Exe.StageOk o H teeFormChecked :=
  fun _ hm => teeFormChecked_sound_any hm.ok

/-- **The stage as an arbitrary-profile shared pass.** -/
def teeFormP {H : Type} (P : Profile) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := teeFormChecked
  inv_run hm := (teeFormChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (teeFormChecked_sound_any hm).2

/-- The bodies of `m` are those of `teeForm m` with `tfBI` pairs expanded (the syntactic body
relation of the soundness proof; `Silmaril.Wasm.FnInst.Ground` reuses it). -/
theorem teeForm_bodiesRel (m : BModule) : ModuleBodiesRel tfBI (teeForm m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.TeeForm.teeForm_bodiesRel m

end Silmaril.Wasm.Binaryen.TeeForm
