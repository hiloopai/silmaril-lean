module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass-1 integration: definitions

Pass 1 of round 5 refuted the round-4 target and both round-4 reductions:

* `Round4.Task.wholeStepValid` is false (`Round5.Pos.not_wholeStepValid`: `$utf8` never
  evaluates, so frames with exports are untyped and SpecTec cannot step from them), and so is
  its restriction to `HostOk` hosts;
* `Round4Int.Parts` is unsatisfiable through `pos` (`Round5.Pos.not_parts`) and through `rem`
  (`Round5.Bwd.not_parts`: `Round4Read.RemainingV` fails at a dangling array reference);
* `Round5.Bwd.PartsR` keeps `Round4.PosTyping`, so it is unsatisfiable too
  (`Round5.Pos.not_posTyping`).

The documented restated target is `Round5.Task.wholeStepValidOk` (`HostOk` hosts,
export-free configurations). Track pos reduced it to `Pos.PartsOk`, whose `rem` field is
`RemainingV`, again refuted. This header combines the tracks' reductions:

* `PartsOkR`: `Pos.PartsOk` with `HostStepsV` for `fam` and `RemR` (under
  `ReadValidR`, which Core validity gives) for `rem`;
* `Open`: the leaves still open after pass 1, from which `PartsOkR` is assembled with every
  proved piece of the four tracks (`Round5.Int.partsOkR_of_open`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **What `Task.wholeStepValidOk` reduces to after pass 1**, at one encoding, host and profile,
for `B := Prims.builtins P hn host`. -/
structure PartsOkR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves, export-free. -/
  pos : Pos.PosTypingNE (BI P hn host) hn
  /-- The forward conjunct on valid, bounded, export-free sources. -/
  fwd : R4Fwd.Forward (BI P hn host) hn P host Pos.ValidNE
  /-- The host-call rules (`Step` 8, 9), backward. -/
  hostSteps : Bwd.HostStepsV (simEnv (BI P hn host)) hn P host
  /-- The backward rules no track has dispatched, under `ReadValidR`. -/
  rem : Bwd.RemR (simEnv (BI P hn host)) hn P host

/-- The `Step_read` rules no track has dispatched, backward, under `ReadValidR`: the `read`
field of `Bwd.RemR`. -/
def ReadOpen (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ Round4Read.readDoneV →
    i ∉ Bwd.readDoneR → ∀ (c : Config H) (w : Value), Bwd.ReadValidR c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩

/-- The non-bitwise SIMD operators, forward, from bounded sources (`vector`
hypothesis, round 4's `Open4.vector`). -/
def VectorFwd (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Round4.Bounded ⟨s, f, is⟩ →
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- **The leaves still open after round 5, pass 1**, at one encoding, host and profile. -/
structure Open (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding (host `call_ref`, forward and backward). -/
  hostRespects : Prims.HostRespects hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : VectorFwd hn P host
  /-- `array.new_data` with `n > 0`, forward. -/
  newDataNum : Fwd.NewDataNumB (BI P hn host) hn
  /-- Family V's agreement of the vector primitives (backward vector rules). -/
  vecAgree : Vec.VecAgree (simEnv (BI P hn host)) P
  /-- `Step_pure` 64, 70–73, backward. -/
  pureOpen : BwdStep.PureOpenV hn P host
  /-- The remaining `Step_read` rules, backward. -/
  read : ReadOpen hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.Int
