module

public import Silmaril.Wasm.Binaryen.Deferred.Thms
public import Silmaril.Wasm.Binaryen.RseLine.Defs
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
import Silmaril.Proofs.Wasm.Binaryen.RseLine.Reverse
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # Self-store elimination (silmaril's rse-line): soundness

The proofs are in `Silmaril.Proofs.Wasm.Binaryen.RseLine.{Sound,Reverse}`. Both
simulation directions hold at an arbitrary numerical profile under the closed host:

* `RedundantSetLine.rsBaseSim` (silmaril's; the result simulates the original);
* `rsReverseSim` (a `Deferred.DeferredBaseSim`: the original's self store (after a tee expansion) is a forced step that leaves the frame unchanged).

`rseLine_sound_any` gives exact export equivalence of the raw rewrite for valid input
and output, and `rseLineChecked_sound_any` gives validity and exact export equivalence
of the checked stage from validity of the input alone, at **every** numerical
profile. No determinism of the profile is used.

This header packages the stage for silmaril's executable stage contract
`Exe.StageOk` (stated at deterministic profiles) and as an arbitrary-profile shared
pass `ArbitraryProfile.EquivPass` (used by the selected-stage byte driver).
-/

namespace Silmaril.Wasm.Binaryen.RseLine

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

section Soundness

open Silmaril.Wasm.Binaryen.RedundantSetLine (rseLine)

variable {H : Type} {P : Profile}

/-- **The raw rewrite is exactly export-equivalent** for valid input and output, at every
numerical profile under the closed host. -/
theorem rseLine_sound_any {m : BModule} (hm : m.Ok) (hm' : (rseLine m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (rseLine m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.RseLine.rseLine_sound_any hm hm'

/-- **The checked stage keeps validity and is exactly export-equivalent**, with validity of
the input as its only premise, at every numerical profile under the closed host. -/
theorem rseLineChecked_sound_any {m : BModule} (hm : m.Ok) :
    (rseLineChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (rseLineChecked m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.RseLine.rseLineChecked_sound_any hm

end Soundness

/-- **The stage satisfies silmaril's executable stage contract.** -/
theorem rseLine_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    Exe.StageOk o H rseLineChecked :=
  fun _ hm => rseLineChecked_sound_any hm.ok

/-- **The stage as an arbitrary-profile shared pass.** -/
def rseLineP {H : Type} (P : Profile) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := rseLineChecked
  inv_run hm := (rseLineChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (rseLineChecked_sound_any hm).2

/-- The bodies of `m` are those of `rseLine m` with `rsBI` pairs rewritten back (the syntactic
body relation of the soundness proof; `Silmaril.Wasm.FnInst.Ground` reuses it). -/
theorem rseLine_bodiesRel (m : BModule) :
    ModuleBodiesRel Silmaril.Wasm.Binaryen.RedundantSetLine.rsBI
      (Silmaril.Wasm.Binaryen.RedundantSetLine.rseLine m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.RseLine.rseLine_bodiesRel m

end Silmaril.Wasm.Binaryen.RseLine
