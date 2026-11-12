module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.BwdStep.Assemble
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.VStore

/-!
# Round 5: the `step` field of `RemainingV`, discharged (current encoding)

`stepOpenR5` is the four memory SIMD stores (22–25). Under the current, provisional encoding of
the memory SIMD instructions none of them fires (`VStore.lean`), so `StepOpenV` holds
(`stepOpenV_provisional`) and with it the whole `step` field of `RemainingV`, for every profile
in which growth may both succeed and fail (`remStep`), in particular `Profile.spec`.

This module is the only one that depends on the provisional encoding: when the memory SIMD
instructions are encoded against the IL (`Open4`), it stops compiling, and `remStep_of_open`
(`Assemble.lean`) still reduces the field to `StepOpenV`.

`remainingV_of`: `RemainingV` at the concrete `B` from family V's `VecAgree`, `PureOpenV` and the
`Step_read` field (owned by other tracks).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)
open Round4Read (ReadValid RemainingV)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`StepOpenV`, at the current encoding**: none of the memory SIMD stores fires. -/
theorem stepOpenV_provisional : StepOpenV hn P host := by
  intro i hi c w _ _ hf
  simp only [stepOpenR5, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  exacts [absurd hf not_fires_vstoreOob, absurd hf not_fires_vstoreVal,
    absurd hf not_fires_vstoreLaneOob, absurd hf not_fires_vstoreLaneVal]

/-- **The `step` field of `RemainingV`, discharged** at the concrete `B`, in every profile in
which growth may both succeed and fail. -/
theorem remStep (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) :
    ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
      ∀ (c : Config H) (w : Value), ReadValid c → Typed (simEnv (BI P hn host)) hn c →
      Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w]) →
      Bwd.BwdUpTo hn P host c w :=
  remStep_of_open hPs hPf stepOpenV_provisional

/-- **`RemainingV` at the concrete `B`**, from `VecAgree`, the open vector rules `PureOpenV` and
the `Step_read` field. -/
theorem remainingV_of (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (A : Vec.VecAgree (simEnv (BI P hn host)) P)
    (O : PureOpenV hn P host)
    (Rd : ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ Round4Read.readDoneV →
      ∀ (c : Config H) (w : Value), ReadValid c → Typed (simEnv (BI P hn host)) hn c →
      Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
      ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
        Step P host c ⟨c.store, c.frame, is'⟩) :
    RemainingV (simEnv (BI P hn host)) hn P host where
  pure := remPure_of_open A O
  read := Rd
  step := remStep hPs hPf

/-- `Profile.spec` lets growth succeed. -/
theorem growMaySucceed_spec (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) :
    ∀ k a n d, (Profile.spec nd r).growMaySucceed k a n d := fun _ _ _ _ => trivial

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
