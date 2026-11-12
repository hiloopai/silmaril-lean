module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass 2, track read: definitions

Pass 1 left `Round5.Int.ReadOpen` open: the `Step_read` rules no track had dispatched, backward,
under `Round5.Bwd.ReadValidR`. Two kinds of rule need more than `ReadValidR` gives:

* `array.init_elem-zero` (96) and `array.init_data-zero` (101) carry only `otherwise` and
  `n = 0`. Their `otherwise` holds when the segment `y` does not resolve (the `-oob2` rule then
  has no value to compare), but Core's `-zero` steps need `$elem(z, y)`, resp. `$data(z, y)`.
  `Round4Read.codeIdx` resolves the segment indices of `table.init`/`memory.init` but not those of
  the aggregate instructions.
* `vload*` (42–51): the SIMD loads are outside the bounded fragment (`Round4.instrBnd`), so a
  bounded configuration never has them in its active code; `ReadValidR` does not say so.

This header therefore restates the validity facts (additively; `ReadValidR` is unchanged):

* `Instr.SegOk`, `adminSeg`, `codeSeg`: the segment indices of `array.new_elem`, `array.new_data`,
  `array.init_elem` and `array.init_data` resolve, and the types of `array.new_data`,
  `array.init_data` and `array.new_default` are the array types validation requires, at every
  depth of the active code.
* `ReadValidS`: `ReadValidR`, `codeSeg`, `Round4.AdminsBnd` of the active code and
  `Round4.ModuleBnd` of the frame's module. Core validity and `Round4.Bounded` give it
  (`Round5.Read.readValidS_of_bounded`), and it is closed under the
  context decompositions (`readValidS_ctxClosed`).
* `ReadOpenS`: `Round5.Int.ReadOpen` with `ReadValidS` for `ReadValidR`.
* `readDoneS`, `readDoneK`: the rules this track dispatches (`readDoneK` from track fwd's
  `Fwd.RefOkB`); `ReadRest`: what remains of `ReadOpenS`.
* `PartsOkS`, `OpenS`: `Round5.Int.PartsOkR`/`Open` with the `read` obligation as `ReadOpenS`
  (resp. `ReadRest`); they give `Round5.Task.wholeStepValidOk` as before.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **The indices of an aggregate instruction resolve as validation requires**: the segment of
`array.new_elem`, `array.init_elem` (element segment), `array.new_data`, `array.init_data` (data
segment); the type of `array.new_data`, `array.init_data` (an array type with numeric or vector
elements, so `$zsize` is defined) and of `array.new_default` (an array type whose element type is
defaultable). -/
def Instr.SegOk (s : Store H) (f : Frame) : Instr → Prop
  | .arrayNewElem _ y | .arrayInitElem _ y => (s.elem? f y).isSome
  | .arrayNewData x y | .arrayInitData x y => (s.data? f y).isSome ∧
      ∃ d m zt, f.type? x = some d ∧ Expand d (.array (.field m zt)) ∧ 0 < storageSize zt
  | .arrayNewDefault x => ∃ d m zt, f.type? x = some d ∧ Expand d (.array (.field m zt)) ∧
      (defaultVal? zt.unpack).isSome
  | _ => True

mutual
/-- `Instr.SegOk` for every plain instruction of `a`, at any depth; a frame's body is checked
against the frame's own module. -/
def adminSeg (s : Store H) (f : Frame) : Admin → Prop
  | .plain i => Instr.SegOk s f i
  | .label _ _ b => codeSeg s f b
  | .handler _ _ b => codeSeg s f b
  | .frame _ fi b => codeSeg s fi b
  | _ => True

/-- `adminSeg` along a code sequence. -/
def codeSeg (s : Store H) (f : Frame) : List Admin → Prop
  | [] => True
  | a :: l => adminSeg s f a ∧ codeSeg s f l
end

/-- **The validity facts the remaining backward read rules use**: `Bwd.ReadValidR`, the
aggregate segment indices, and the bounded fragment of the active code. -/
structure ReadValidS (c : Config H) : Prop where
  /-- Store bounds, index resolution and reference liveness. -/
  r : Bwd.ReadValidR c
  /-- The aggregate instructions' segment indices resolve. -/
  seg : codeSeg c.store c.frame c.code
  /-- The active code is in the bounded fragment (no SIMD loads or stores). -/
  bnd : Round4.AdminsBnd c.code
  /-- The frame's module is bounded (its defined types are within SpecTec's syntax). -/
  frame : Round4.ModuleBnd c.frame.module

/-- **The remaining `Step_read` rules, backward, under `ReadValidS`**: `Round5.Int.ReadOpen` with
`ReadValidS` for `ReadValidR`. -/
def ReadOpenS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ Round4Read.readDoneV →
    i ∉ Bwd.readDoneR → ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩

/-- The `Step_read` rules this track dispatches, for the concrete builtins, under `ReadValidS`:
`vload*` (42–51, vacuously: not bounded), `array.new_default` (72), `array.new_elem-alloc` (74),
`array.new_data-oob` (75), `array.fill-succ` (85), `array.copy-zero` (90),
`array.init_elem-zero` (96), `array.init_elem-succ` (97), `array.init_data-oob2` (100) and
`array.init_data-zero` (101). -/
def readDoneS : List Nat :=
  [42, 43, 44, 45, 46, 47, 48, 49, 50, 51] ++ [72, 74, 75, 85, 90, 96, 97, 100, 101]

/-- The cast rules this track dispatches from track fwd's bridge `Fwd.RefOkB` (a leaf of
`Round5.Int.Open`): `br_on_cast` (2, 3), `br_on_cast_fail` (4, 5), `ref.test` (65, 66),
`ref.cast` (67, 68). -/
def readDoneK : List Nat := [2, 3, 4, 5, 65, 66, 67, 68]

/-- **What is left of `ReadOpenS`**: the rules (of the 103 of `Step_read`) outside every
dispatched list. -/
def ReadRest (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i < 103 → i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ Round4Read.readDoneV →
    i ∉ Bwd.readDoneR → i ∉ readDoneS → i ∉ readDoneK → ∀ (c : Config H) (w : Value),
    ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩

/-- **`Round5.Int.PartsOkR` with the read obligation restated** (`ReadOpenS` for
`RemR.read`). -/
structure PartsOkS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves, export-free. -/
  pos : Pos.PosTypingNE (BI P hn host) hn
  /-- The forward conjunct on valid, bounded, export-free sources. -/
  fwd : R4Fwd.Forward (BI P hn host) hn P host Pos.ValidNE
  /-- The host-call rules (`Step` 8, 9), backward. -/
  hostSteps : Bwd.HostStepsV (simEnv (BI P hn host)) hn P host
  /-- `Step_pure` outside the dispatched lists (`RemR.pure`). -/
  pure : ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), Bwd.ReadValidR ⟨s, f, is⟩ →
    Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- The remaining `Step_read` rules, under `ReadValidS`. -/
  read : ReadOpenS hn P host
  /-- `Step` (index `≥ 6`) outside the dispatched lists (`RemR.step`). -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
    ∀ (c : Config H) (w : Value), Bwd.ReadValidR c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w]) →
    Bwd.BwdUpTo hn P host c w

/-- **`Round5.Int.Open` with the read leaf restated**: `ReadRest` (under `ReadValidS`, minus
this track's rules) for `ReadOpen`. -/
structure OpenS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding (host `call_ref`, forward and backward). -/
  hostRespects : Prims.HostRespects hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- `array.new_data` with `n > 0`, forward. -/
  newDataNum : Fwd.NewDataNumB (BI P hn host) hn
  /-- Family V's agreement of the vector primitives (backward vector rules). -/
  vecAgree : Vec.VecAgree (simEnv (BI P hn host)) P
  /-- `Step_pure` 64, 70–73, backward. -/
  pureOpen : BwdStep.PureOpenV hn P host
  /-- The `Step_read` rules still open, backward, under `ReadValidS`. -/
  read : ReadRest hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
