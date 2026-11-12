module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Thms

/-!
# SpecTec ↔ Core 3.0, round 5, track bwd: definitions

Round 4's integration reduced `Round4.Task.wholeStepValid` to `Round4Int.Parts`. This track
works on its backward fields `fam` (`Round4Int.FamBwdV`) and the `Step_read` part of `rem`
(`Round4Read.RemainingV.read`).

* `HostStepsV`: the two host-call rules of `FamBwdV.step` (`Step` 8 `call_ref-host`, 9
  `call_ref-host-div`), backward, on `ReadValid` sources. Every other rule of `FamBwdV` is proved
  for the concrete builtins (`Round5.Bwd.famBwdV_of_hostSteps`). These two need `$hostcall` read
  back (`Bwd.HostInv`); the concrete `$hostcall` answers at a chosen call with the same image, so
  `HostInv` holds when the host respects the encoding (`Prims.HostRespects`), which the target
  does not assume.
* `ReadValidR`: `Round4Read.ReadValid` plus **reference liveness** (`codeLive`): every array,
  struct, function and exception reference of the active code, at any depth, names an allocated
  instance. `ReadValid` alone does not suffice: `Round4Read.RemainingV` is false
  (`Round5.Bwd.not_remainingV`), because `Step_read/array.fill-zero` fires through `otherwise` at
  a dangling array, where Core is stuck. Core validity gives liveness (`RefOk`), so
  `ConfigOk c ts → Bounded c → ReadValidR c` (`Round5.Bwd.readValidR_of_bounded`).
* `readDoneR`: the `Step_read` rules this track dispatches under `ReadValidR`.
* `RemR`: what is left of the backward rules (`RemainingV` with `ReadValidR` and without
  `readDoneR`).
* `PartsR`: the restated reduction of `Round4.Task.wholeStepValid`, with `HostStepsV` in place
  of `FamBwdV` and `RemR` in place of `RemainingV`. `Round4Int.Parts` is unsatisfiable
  (`Round5.Bwd.not_parts`); `PartsR` is not known to be.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Round4Read (ReadValid)

variable {H : Type}

/-- **The host-call rules of `FamBwdV.step`**: `Step` 8 (`call_ref-host`) and 9
(`call_ref-host-div`), backward, from typed `ReadValid` sources. -/
def HostStepsV (env : Env) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i, i ∈ [8, 9] → ∀ (c : Config H) (w : Value), ReadValid c → Typed env hn c →
    Fires env "Step" i (.tuple [configV hn c, w]) → Bwd.BwdUpTo hn P host c w

/-- **A reference names an allocated instance** (arrays, structs, functions and exceptions;
`extern` through its payload). -/
def refLive (s : Store H) : Ref → Prop
  | .array a => (s.arrays[a]?).isSome
  | .struct a => (s.structs[a]?).isSome
  | .func a => (s.funcs[a]?).isSome
  | .exn a => (s.exns[a]?).isSome
  | .extern r => refLive s r
  | _ => True

mutual
/-- `refLive` for every reference of `a`, at any depth. -/
def adminLive (s : Store H) : Admin → Prop
  | .ref r => refLive s r
  | .label _ _ b => codeLive s b
  | .handler _ _ b => codeLive s b
  | .frame _ _ b => codeLive s b
  | _ => True

/-- `adminLive` along a code sequence. -/
def codeLive (s : Store H) : List Admin → Prop
  | [] => True
  | a :: l => adminLive s a ∧ codeLive s l
end

/-- **The validity facts the backward rules use, round 5**: `Round4Read.ReadValid` and
reference liveness. -/
structure ReadValidR (c : Config H) : Prop where
  /-- Store bounds and index resolution. -/
  read : ReadValid c
  /-- Every reference of the active code is live. -/
  live : codeLive c.store c.code

/-- The `Step_read` rules this track dispatches: `array.new_elem-oob` (73), `array.get-oob` (78),
`array.copy-null1`/`-null2` (86, 87), `array.copy-oob1`/`-oob2` (88, 89),
`array.init_elem-oob1`/`-oob2` (94, 95), `array.init_data-oob1` (99), and `array.fill-zero`
(84, the one that needs reference liveness). -/
def readDoneR : List Nat := [73, 78, 86, 87, 88, 89, 94, 95, 99, 84]

/-- **The open backward rules, round 5**: `Round4Read.RemainingV` with `ReadValidR` for
`ReadValid` and the rules of `readDoneR` removed from `read`. -/
structure RemR (env : Env) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `Step_pure` outside the dispatched lists. -/
  pure : ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), ReadValidR ⟨s, f, is⟩ →
    Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read` outside the dispatched lists. -/
  read : ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ Round4Read.readDoneV →
    i ∉ readDoneR → ∀ (c : Config H) (w : Value), ReadValidR c → Typed env hn c →
    Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step` (index `≥ 6`) outside the dispatched lists. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
    ∀ (c : Config H) (w : Value), ReadValidR c → Typed env hn c →
    Fires env "Step" i (.tuple [configV hn c, w]) → Bwd.BwdUpTo hn P host c w

/-- **The restated reduction of `Round4.Task.wholeStepValid`**, for `B := Prims.builtins`:
`Round4Int.Parts` with `HostStepsV` for `fam` (the rest of `FamBwdV` is proved) and `RemR` for
`rem`. -/
structure PartsR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves. -/
  pos : Round4.PosTyping (Round4Int.BI P hn host) hn
  /-- Bounded Core successors of valid, bounded configurations are typed. -/
  succTyped : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round4.Bounded c →
    Round4.Bounded c' → Step P host c c' → Typed (simEnv (Round4Int.BI P hn host)) hn c'
  /-- The forward conjunct on valid sources. -/
  fwd : R4Fwd.Forward (Round4Int.BI P hn host) hn P host Round4Int.Valid
  /-- The host-call rules, backward. -/
  hostSteps : HostStepsV (simEnv (Round4Int.BI P hn host)) hn P host
  /-- The backward rules no track has dispatched, under `ReadValidR`. -/
  rem : RemR (simEnv (Round4Int.BI P hn host)) hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
