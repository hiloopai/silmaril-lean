module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track bwdstep: definitions

Round 4 left the `step` field of `Round4Read.RemainingV` open: the store-changing `Step` rules
that no earlier track had dispatched backward. This track proves them one by one, under
`Round4Read.ReadValid`, at the concrete `B := Prims.builtins P hn host` (`Round4Int.BI`).

* `stepDoneR5`: the `Step` rules dispatched here.
* `stepOpenR5`: the `Step` rules still open after this track. Together with `Bwd.stepDone`,
  `BwdPureStep.stepDone` and `stepDoneR5` they cover rules 6–35, the whole store-changing part
  of `Step` (`Equiv.ExecStepRules`).
* `StepOpenV`: the backward obligation of `RemainingV.step`, restricted to `stepOpenR5`. The
  track's assembly (`Round5.BwdStep.remStep_of_open`) gives the whole `RemainingV.step` field from
  it.
* `pureVecDone`, `pureOpenR5`, `PureOpenV`: the same for the vector rules 54–78 of `Step_pure`,
  the rest of `RemainingV.pure` (`remPure_of_open`, given family V's `VecAgree`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Read (ReadValid)

variable {H : Type}

/-- The `Step` rules dispatched backward by this track: `table.grow-succeed` (15),
`table.grow-fail` (16), `store-num-val` (19), `store-pack-val` (21), `memory.grow-succeed` (26),
`memory.grow-fail` (27), `struct.new` (29), `struct.set-struct` (31), `array.new_fixed` (32),
`array.set-array` (35). -/
def stepDoneR5 : List Nat := [15, 16, 19, 21, 26, 27, 29, 31, 32, 35]

/-- The `Step` rules without a backward proof: the memory SIMD stores `vstore-oob` (22),
`vstore-val` (23), `vstore_lane-oob` (24), `vstore_lane-val` (25). At the current, provisional
encoding of those instructions they do not fire (`Round5.BwdStep.stepOpenV_provisional`). -/
def stepOpenR5 : List Nat := [22, 23, 24, 25]

/-- **The open part of `RemainingV.step`**: the backward obligation for the rules of
`stepOpenR5`, under `ReadValid`, at `simEnv (BI P hn host)`. -/
def StepOpenV (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i ∈ stepOpenR5 → ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv (Round4Int.BI P hn host)) hn c →
    Fires (simEnv (Round4Int.BI P hn host)) "Step" i (.tuple [configV hn c, w]) →
    Bwd.BwdUpTo hn P host c w

/-- The vector rules of `Step_pure` dispatched here, from family V's `VecAgree`: 54–78 except
`vtestop` (64), `vsplat` (70), `vextract_lane-num`/`-pack` (71, 72) and `vreplace_lane` (73). -/
def pureVecDone : List Nat :=
  [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69, 74, 75, 76, 77, 78]

/-- The `Step_pure` rules still open: 64, 70, 71, 72, 73. -/
def pureOpenR5 : List Nat := [64, 70, 71, 72, 73]

/-- **The open part of `RemainingV.pure`**: the backward obligation for the rules of
`pureOpenR5`, under `ReadValid`, at `simEnv (BI P hn host)`. -/
def PureOpenV (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i ∈ pureOpenR5 → ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ReadValid ⟨s, f, is⟩ → Typed (simEnv (Round4Int.BI P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Round4Int.BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
