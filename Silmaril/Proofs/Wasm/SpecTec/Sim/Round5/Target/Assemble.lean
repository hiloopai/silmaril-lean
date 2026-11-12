module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Typing
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Refute
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Thms

/-!
# Round 5: the restated target `Task.wholeStepValidSel`, assembled

* `backward_Sel`: `Round5.Read.backward_S` from `PartsSel` (its proof uses only the
  backward fields, which `PartsSel` shares with `Round5.Read.PartsOkS`).
* `oneStepSel_of_partsSel`, `wholeStepValidSel_of_partsSel`: `Round5.Task.wholeStepValidSel`
  from `PartsSel`, both configurations typed by `typed_of_configOk_selK`.
* `partsSel_of_open5`, `wholeStepValidSel_of_open5`: `Open5` (pass 3's `Round5.Int3.Open4`
  without `simd`) gives `PartsSel`, as `Round5.Int2.partsOkS_of_open2` with the pass-3 leaves
  discharged as in `Round5.Int3.open2_of_open4`, and `posTypingSel` for `pos`.
* `partsSel_of_partsOkS`, `open5_of_open4`, `wholeStepValidSel_of_ok`: the new statements ask no
  more than the earlier ones.
* `not_open5_spec`: `Open5` is still false under the spec NaN profile, through `vecOps`
  (`Round5.Simd.not_vecAgreeOps_spec`), so `wholeStepValidSel_of_open5` is vacuous as stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Target

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Read (BackwardUpToV)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The backward half, from `PartsSel` -/

/-- `Step_pure`, backward, under `ReadValidS`, from `PartsSel` (`Read.backwardS_pure`). -/
theorem backwardSel_pure (Pa : PartsSel hn P host) (i : Nat) (s : Store H) (f : Frame)
    (is : List Admin) (w : Value) (hv : Read.ReadValidS ⟨s, f, is⟩)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  by_cases h₀ : i ∈ Bwd.pureDone
  · exact (Bwd.famBwdV_of_hostSteps Pa.hostSteps).pure i h₀ s f is w hv.r.read hc hf
  by_cases h₁ : i ∈ Integrate.floatDone
  · exact Integrate.pure_floatDone (Prims.intB_builtins hn host) (Prims.floatB_builtins hn host)
      h₁ hf
  by_cases h₂ : i ∈ BwdPureStep.pureDone
  · exact Bwd.pure_upTo (BwdPureStep.pure_done _ (BwdPureStep.bwdB_builtins hn host) i h₂ hf)
  · exact Pa.pure i h₀ h₁ h₂ s f is w hv.r hc hf

/-- `Step_read`, backward, under `ReadValidS`, from `PartsSel` (`Read.backwardS_read`). -/
theorem backwardSel_read (Pa : PartsSel hn P host) (i : Nat) (c : Config H) (w : Value)
    (hv : Read.ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  have NA := BwdRead.noAcc_builtins P hn host
  by_cases h₀ : i ∈ Bwd.readDoneUpTo
  · exact (Bwd.famBwdV_of_hostSteps Pa.hostSteps).read i h₀ c w hv.r.read hc hf
  by_cases h₁ : i ∈ BwdRead.readDone
  · exact Bwd.read_upTo (BwdRead.read_done _ NA i h₁ c w hc hf)
  by_cases h₂ : i ∈ Round4Read.readDoneV
  · exact Bwd.read_upTo (Round4Read.read_doneV _ NA i h₂ c w hv.r.read hc hf)
  by_cases h₃ : i ∈ Bwd.readDoneR
  · exact Bwd.read_upTo (Bwd.read_doneR i h₃ c w hv.r hc hf)
  · exact Pa.read i h₀ h₁ h₂ h₃ c w hv hc hf

/-- `Step`, backward, under `ReadValidS`, from `PartsSel` (`Read.backwardS_step`). -/
theorem backwardSel_step (Pa : PartsSel hn P host) (i : Nat) (h6 : 6 ≤ i) (c : Config H)
    (w : Value) (hv : Read.ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    Bwd.BwdUpTo hn P host c w := by
  by_cases h₀ : i ∈ Bwd.stepDone
  · exact (Bwd.famBwdV_of_hostSteps Pa.hostSteps).step i h₀ c w hv.r.read hc hf
  by_cases h₁ : i ∈ BwdPureStep.stepDone
  · exact Bwd.step_upTo (BwdPureStep.step_done _ (BwdPureStep.bwdB_builtins hn host) i h₁ hf)
  · exact Pa.step i h6 h₀ h₁ c w hv.r hc hf

/-- **The per-rule backward obligations under `ReadValidS`**, from `PartsSel`. -/
theorem backwardUpToSel (Pa : PartsSel hn P host) :
    BackwardUpToV Read.ReadValidS (simEnv (BI P hn host)) hn P host :=
  ⟨backwardSel_pure Pa, backwardSel_read Pa, backwardSel_step Pa⟩

/-- **The backward simulation from typed `ReadValidS` sources**, from `PartsSel`. -/
theorem backward_Sel (Pa : PartsSel hn P host) (c : Config H) (w : Value)
    (hv : Read.ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  Round4Read.backward_upToV Read.readValidS_ctxClosed (backwardUpToSel Pa)
    (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)) (Typing.typingFacts_simEnv _ hn)
    (hasStepRules_simEnv _) (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

/-! ## The restated target -/

/-- **The restated one-step simulation, from `PartsSel`**, for a `HostOk` host. -/
theorem oneStepSel_of_partsSel (Pa : PartsSel hn P host) (hh : HostOk host) :
    (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSel c → BoundedSel c' →
      Step P host c c' → ∃ d', Bwd.ConfigEq c' d' ∧
        SStep (simEnv (BI P hn host)) (configV hn c) (configV hn d')) ∧
    (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSel c →
      SStep (simEnv (BI P hn host)) (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c') :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨⟨ts, hc⟩, hb.1.1⟩, hb.1.2⟩ hb.1.1.store (typed_of_configOk_selK Pa.pos hc hb)
        (typed_of_configOk_selK Pa.pos (Step.preservation hh hc hs).1 hb') hs,
    fun c _ w hc hb hs =>
      backward_Sel Pa c w (Read.readValidS_of_bounded hc hb.1.1)
        (typed_of_configOk_selK Pa.pos hc hb) hs⟩

/-- **`Round5.Task.wholeStepValidSel`, from `PartsSel`** at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValidSel_of_partsSel
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), PartsSel hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidSel := fun H hn hinj host hfin hok nd r =>
  ⟨_, oneStepSel_of_partsSel (h H hn hinj host hfin hok nd r) hok⟩

/-- `PartsOkS` gives `PartsSel`: the restated reduction asks no more (vacuously:
`PartsOkS.pos` is false, `SimdTy.not_posTypingNE`). -/
theorem partsSel_of_partsOkS (Pa : Read.PartsOkS hn P host) : PartsSel hn P host where
  pos := posTypingSel_of_posTypingNE Pa.pos
  fwd := Pa.fwd
  hostSteps := Pa.hostSteps
  pure := Pa.pure
  read := Pa.read
  step := Pa.step

/-- **`PartsSel` from the leaves `Open5`**, for an injective encoding and a finite host, in a
profile where growth may both succeed and fail. The pass-3 leaves are discharged as in
`Round5.Int3.open2_of_open4`, and `pos` by `posTypingSel`. -/
theorem partsSel_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : Open5 hn P host) : PartsSel hn P host where
  pos := posTypingSel _ hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (FwdRef.forward_validT (Int.typesB _) O.refOk hf (FwdRef2.hostRespectsT_all _ hinj host)
      (SimdTy.vectorFwd_of_ops O.vecOps))
  hostSteps := FwdRef.hostStepsV_of_T hf (FwdRef2.hostRespectsT_all _ hinj host)
  pure := fun i h₀ h₁ h₂ s f is w hv hc hfi =>
    BwdStep.remPure_of_open (Simd.vecAgree_of_ops O.vecOps)
      (Simd.pureOpenV_of_vtestop Simd.pureOpenVtestop) i h₀ h₁ h₂ s f is w hv.read hc hfi
  read := Read.readOpenS_of_rest O.refOk Read2.readRest
  step := fun i h6 h₀ h₁ c w hv hc hfi => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hfi

/-- **`Round5.Task.wholeStepValidSel` from the leaves still open after pass 4**, at every
injective encoding, finite `HostOk` host and `Profile.spec nd r`. Vacuous: see
`not_open5_spec`. -/
theorem wholeStepValidSel_of_open5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open5 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidSel :=
  wholeStepValidSel_of_partsSel fun H hn hinj host hfin hok nd r =>
    partsSel_of_open5 hinj hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

/-- `Round5.Int3.Open4` gives `Open5`: the new leaves ask no more. -/
theorem open5_of_open4 (O : Int3.Open4 hn P host) : Open5 hn P host where
  refOk := O.refOk
  vecOps := O.vecOps

/-- **`Open5` never holds under the spec NaN profile**: its `vecOps` leaf fails at `convert`. -/
theorem not_open5_spec (nd : Bool) (r : RelaxedChoice) : ¬ Open5 hn (Profile.spec nd r) host :=
  fun O => Simd.not_vecAgreeOps_spec rfl O.vecOps

/-- **The old target implies the new one**: `Task.wholeStepValidSel` only restricts the source
configurations of `Task.wholeStepValidOk` (vacuously, since that target is false,
`not_wholeStepValidOk`). -/
theorem wholeStepValidSel_of_ok (h : Round5.Task.wholeStepValidOk) :
    Round5.Task.wholeStepValidSel := fun H hn hinj host hfin hok nd r => by
  obtain ⟨B, hf, hb⟩ := h H hn hinj host hfin hok nd r
  exact ⟨B, fun c c' ts hc h₁ h₂ hs => hf c c' ts hc h₁.1 h₂.1 hs,
    fun c ts w hc h₁ hs => hb c ts w hc h₁.1 hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Target
