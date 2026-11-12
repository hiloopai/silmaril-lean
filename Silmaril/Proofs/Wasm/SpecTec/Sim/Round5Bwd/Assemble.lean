module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Bwd.Fam
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Bwd.Valid
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Bwd.Refute
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5Bwd.AggElse

/-!
# Round 5: the restated reduction

* `read_doneR`: the rules of `readDoneR`, backward, for the concrete builtins, under
  `ReadValidR` (only `array.fill-zero` uses liveness).
* `remainingR_of_remR`: `RemR` and this track's rules give `Round4Read.RemainingV` restated to
  `ReadValidR`, as a `Round4Read.BackwardUpToV ReadValidR` field.
* `backward_R`, `backward_validR`: the backward conjunct of `Round4.Task.wholeStepValid` from
  `PosTyping`, `HostStepsV` and `RemR`.
* `oneStep_of_partsR`, `wholeStepValid_of_partsR`: the frozen target from `PartsR`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Read (ReadValid BackwardUpToV)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **This track's `Step_read` rules, backward**, for the concrete builtins. -/
theorem read_doneR (i : Nat) (hi : i ∈ readDoneR) (c : Config H) (w : Value) (hv : ReadValidR c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have NA := BwdRead.noAcc_builtins P hn host
  simp only [readDoneR, List.mem_cons, List.mem_nil_iff, or_false] at hi
  have hr := hv.read
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwdV_arrayNewElemOob _ NA c w hr hc hf, bwdV_arrayGetOob _ c w hr hc hf,
    bwdV_arrayCopyNull₁ _ c w hr hc hf, bwdV_arrayCopyNull₂ _ c w hr hc hf,
    bwdV_arrayCopyOob₁ _ c w hr hc hf, bwdV_arrayCopyOob₂ _ c w hr hc hf,
    bwdV_arrayInitElemOob₁ _ c w hr hc hf, bwdV_arrayInitElemOob₂ _ NA c w hr hc hf,
    bwdV_arrayInitDataOob₁ _ c w hr hc hf, bwdR_arrayFillZero _ c w hv hc hf]

/-- `Step_pure`, backward, under `ReadValidR`, for the concrete builtins. -/
theorem backwardR_pure (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) (i : Nat) (s : Store H) (f : Frame)
    (is : List Admin) (w : Value) (hv : ReadValidR ⟨s, f, is⟩)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  by_cases h₀ : i ∈ Bwd.pureDone
  · exact (famBwdV_of_hostSteps Hh).pure i h₀ s f is w hv.read hc hf
  by_cases h₁ : i ∈ Integrate.floatDone
  · exact Integrate.pure_floatDone (Prims.intB_builtins hn host) (Prims.floatB_builtins hn host)
      h₁ hf
  by_cases h₂ : i ∈ BwdPureStep.pureDone
  · exact Bwd.pure_upTo (BwdPureStep.pure_done _ (BwdPureStep.bwdB_builtins hn host) i h₂ hf)
  · exact Rm.pure i h₀ h₁ h₂ s f is w hv hc hf

/-- `Step_read`, backward, under `ReadValidR`, for the concrete builtins. -/
theorem backwardR_read (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) (i : Nat) (c : Config H) (w : Value)
    (hv : ReadValidR c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  have NA := BwdRead.noAcc_builtins P hn host
  by_cases h₀ : i ∈ Bwd.readDoneUpTo
  · exact (famBwdV_of_hostSteps Hh).read i h₀ c w hv.read hc hf
  by_cases h₁ : i ∈ BwdRead.readDone
  · exact Bwd.read_upTo (BwdRead.read_done _ NA i h₁ c w hc hf)
  by_cases h₂ : i ∈ Round4Read.readDoneV
  · exact Bwd.read_upTo (Round4Read.read_doneV _ NA i h₂ c w hv.read hc hf)
  by_cases h₃ : i ∈ readDoneR
  · exact Bwd.read_upTo (read_doneR i h₃ c w hv hc hf)
  · exact Rm.read i h₀ h₁ h₂ h₃ c w hv hc hf

/-- `Step`, backward, under `ReadValidR`, for the concrete builtins. -/
theorem backwardR_step (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) (i : Nat) (h6 : 6 ≤ i) (c : Config H)
    (w : Value) (hv : ReadValidR c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    Bwd.BwdUpTo hn P host c w := by
  by_cases h₀ : i ∈ Bwd.stepDone
  · exact (famBwdV_of_hostSteps Hh).step i h₀ c w hv.read hc hf
  by_cases h₁ : i ∈ BwdPureStep.stepDone
  · exact Bwd.step_upTo (BwdPureStep.step_done _ (BwdPureStep.bwdB_builtins hn host) i h₁ hf)
  · exact Rm.step i h6 h₀ h₁ c w hv hc hf

/-- **The per-rule obligations under `ReadValidR`**, for the concrete builtins, from
`HostStepsV` and `RemR`. -/
theorem backwardUpToR (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) :
    BackwardUpToV ReadValidR (simEnv (BI P hn host)) hn P host :=
  ⟨backwardR_pure Hh Rm, backwardR_read Hh Rm, backwardR_step Hh Rm⟩

/-- **The backward simulation from typed `ReadValidR` sources**, for the concrete builtins. -/
theorem backward_R (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) (c : Config H) (w : Value)
    (hv : ReadValidR c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  Round4Read.backward_upToV readValidR_ctxClosed (backwardUpToR Hh Rm)
    (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)) (Typing.typingFacts_simEnv _ hn)
    (hasStepRules_simEnv _) (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

/-- **The backward conjunct of `Round4.Task.wholeStepValid`**, for the concrete builtins, from
`PosTyping`, `HostStepsV` and `RemR`. -/
theorem backward_validR (K : Round4.PosTyping (BI P hn host) hn)
    (Hh : HostStepsV (simEnv (BI P hn host)) hn P host)
    (Rm : RemR (simEnv (BI P hn host)) hn P host) (c : Config H) (ts : List CValType)
    (w : Value) (hc : ConfigOk c ts) (hb : Round4.Bounded c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backward_R Hh Rm c w (readValidR_of_bounded hc hb) (Round4.typed_of_configOk K hc hb) hs

/-- **The one-step simulation over valid, bounded configurations, from `PartsR`.** -/
theorem oneStep_of_partsR (Pa : PartsR hn P host) : Round4.OneStep (BI P hn host) hn P host :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨ts, hc⟩, hb⟩ hb.store (Round4.typed_of_configOk Pa.pos hc hb)
        (Pa.succTyped c c' ts hc hb hb' hs) hs,
    fun c ts w hc hb hs => backward_validR Pa.pos Pa.hostSteps Pa.rem c ts w hc hb hs⟩

/-- **The frozen round-4 target, from `PartsR`** at every injective encoding, finite host and
`Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValid_of_partsR
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        PartsR hn (Profile.spec nd r) host) :
    Round4.Task.wholeStepValid := fun H hn hinj host hfin nd r =>
  ⟨_, oneStep_of_partsR (h H hn hinj host hfin nd r)⟩

/-- **`PartsR` from the old `Parts`**: `Parts` (if it held) would give `PartsR`. So `PartsR` is
no stronger; unlike `Parts`, it is not known to be unsatisfiable. -/
theorem partsR_of_parts (Pa : Round4Int.Parts hn P host) : PartsR hn P host where
  pos := Pa.pos
  succTyped := Pa.succTyped
  fwd := Pa.fwd
  hostSteps i hi c w hv hc hf := Pa.fam.step i (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide) c w hv hc hf
  rem := ⟨fun i h₀ h₁ h₂ s f is w hv hc hf => Pa.rem.pure i h₀ h₁ h₂ s f is w hv.read hc hf,
    fun i h₀ h₁ h₂ _ c w hv hc hf => Pa.rem.read i h₀ h₁ h₂ c w hv.read hc hf,
    fun i h6 h₀ h₁ c w hv hc hf => Pa.rem.step i h6 h₀ h₁ c w hv.read hc hf⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
