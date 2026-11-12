module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.ReadDead

/-!
# Round 6: the per-rule backward obligations under `ReadValidS`

`Target.backwardUpToNC` proves round 5's per-rule backward obligations under
`NoCastV` (`ReadValidS` and no cast redex); only its exclusion of the cast rules of `Step_read`
uses the second half. Here the same obligations are stated under `ReadValidS` alone:

* `pureDecl`, `stepDecl`: `Step_pure`, and `Step` from rule 6 on, under the old reading;
* `readDecl`: the non-cast rules of `Step_read`, under the old reading;
* `readB`: **every** rule of `Step_read` under the new reading: the cast rules by track
  reading's `castsBwdB_of` (from `RefOkBB`), the others by `fires_of_firesB_read` and `readDecl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)
open Round5.Read (ReadValidS readDoneK)
open Reading (FiresB RefOkBB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`Step_pure`, backward, under `ReadValidS`** (`Target.backwardUpToNC`'s `pure`). -/
theorem pureDecl (hinj : Function.Injective hn) (hf : HostFinite host) (i : Nat) (s : Store H)
    (f : Frame) (is : List Admin) (w : Value) (hv : ReadValidS ⟨s, f, is⟩)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hfi : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  by_cases h₀ : i ∈ Bwd.pureDone
  · exact (Round5.Bwd.famBwdV_of_hostSteps (Target.hostStepsBI hinj hf)).pure
      i h₀ s f is w hv.r.read hc hfi
  by_cases h₁ : i ∈ Integrate.floatDone
  · exact Integrate.pure_floatDone (Prims.intB_builtins hn host)
      (Prims.floatB_builtins hn host) h₁ hfi
  by_cases h₂ : i ∈ BwdPureStep.pureDone
  · exact Bwd.pure_upTo (BwdPureStep.pure_done _ (BwdPureStep.bwdB_builtins hn host) i h₂ hfi)
  · exact Target.remPureNC i h₀ h₁ h₂ s f is w hv.r.read hc hfi

/-- **The non-cast rules of `Step_read`, backward, under `ReadValidS`**
(`Target.backwardUpToNC`'s `read`, without its cast exclusion). -/
theorem readDecl (hinj : Function.Injective hn) (hf : HostFinite host) (i : Nat)
    (hk : i ∉ readDoneK) (c : Config H) (w : Value) (hv : ReadValidS c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hfi : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  by_cases h₀ : i ∈ Bwd.readDoneUpTo
  · exact (Round5.Bwd.famBwdV_of_hostSteps (Target.hostStepsBI hinj hf)).read
      i h₀ c w hv.r.read hc hfi
  by_cases h₁ : i ∈ BwdRead.readDone
  · exact Bwd.read_upTo (BwdRead.read_done _ (BwdRead.noAcc_builtins P hn host) i h₁ c w hc hfi)
  by_cases h₂ : i ∈ Round4Read.readDoneV
  · exact Bwd.read_upTo (Round4Read.read_doneV _ (BwdRead.noAcc_builtins P hn host) i h₂ c w
      hv.r.read hc hfi)
  by_cases h₃ : i ∈ Round5.Bwd.readDoneR
  · exact Bwd.read_upTo (Round5.Bwd.read_doneR i h₃ c w hv.r hc hfi)
  by_cases h₄ : i ∈ Round5.Read.readDoneS
  · exact Bwd.read_upTo (Round5.Read.read_doneS i h₄ c w hv hc hfi)
  · exact Round5.Read2.readRest i (Round5.Read.lt_of_fires_read hfi) h₀ h₁ h₂ h₃ h₄ hk c w
      hv hc hfi

/-- **The store-changing rules of `Step`, backward, under `ReadValidS`**
(`Target.backwardUpToNC`'s `step`). -/
theorem stepDecl (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (i : Nat) (h6 : 6 ≤ i) (c : Config H) (w : Value) (hv : ReadValidS c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hfi : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    Bwd.BwdUpTo hn P host c w := by
  by_cases h₀ : i ∈ Bwd.stepDone
  · exact (Round5.Bwd.famBwdV_of_hostSteps (Target.hostStepsBI hinj hf)).step
      i h₀ c w hv.r.read hc hfi
  by_cases h₁ : i ∈ BwdPureStep.stepDone
  · exact Bwd.step_upTo (BwdPureStep.step_done _ (BwdPureStep.bwdB_builtins hn host) i h₁ hfi)
  · exact Round5.BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.r.read hc hfi

/-- **Every rule of `Step_read`, backward, under the new reading and `ReadValidS`**, from
`CastRefOk` at `ReadValidS c ∧ W c`. -/
theorem readG (hinj : Function.Injective hn) (hf : HostFinite host) {W : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => ReadValidS c ∧ W c)) (i : Nat)
    (c : Config H) (w : Value) (hv : ReadValidS c ∧ W c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hfi : FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  by_cases hk : i ∈ readDoneK
  · obtain ⟨is', rfl, hst⟩ := Reading.read_doneKG K i hk c w hv hc hfi
    exact ⟨is', is', Bwd.CodeEq.refl _, rfl, hst⟩
  · exact readDecl hinj hf i hk c w hv.1 hc (fires_of_firesB_read hk hfi)

/-- **Every rule of `Step_read`, backward, under the new reading and `ReadValidS`**, from
`RefOkBB`. -/
theorem readB (hinj : Function.Injective hn) (hf : HostFinite host)
    (KB : RefOkBB (simEnv (BI P hn host))) (i : Nat) (c : Config H) (w : Value)
    (hv : ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hfi : FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ :=
  readG (W := fun _ => True) hinj hf (Reading.castRefOk_bnd KB fun _ h => h.1.frame) i c w
    ⟨hv, trivial⟩ hc hfi

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
