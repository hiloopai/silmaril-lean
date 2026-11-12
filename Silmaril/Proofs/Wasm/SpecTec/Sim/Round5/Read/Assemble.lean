module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Read.Valid
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.VLoad
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Succ
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.NewElem
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Cast
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.NewDefault
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.InitDataZero

/-!
# Round 5, pass 2, track read: assembly

* `read_doneS`: this track's `Step_read` rules (`readDoneS`), backward, for the concrete
  builtins, under `ReadValidS`.
* `read_doneK`: the cast rules (`readDoneK`), backward, from `Fwd.RefOkB`.
* `readOpenS_of_rest`: `ReadOpenS` from `Fwd.RefOkB` and what is left (`ReadRest`);
  `readOpenS_of_readOpen`: pass 1's `Round5.Int.ReadOpen` gives `ReadOpenS`, so the
  restatement asks no more.
* `backward_S`: the backward simulation from typed `ReadValidS` sources, from `PartsOkS`.
* `wholeStepValidOk_of_partsOkS`, `wholeStepValidOk_of_openS`: the restated target
  `Round5.Task.wholeStepValidOk` from `PartsOkS`, resp. from the open leaves `OpenS`;
  `partsOkS_of_partsOkR`, `openS_of_open`: the new reductions ask no more than pass 1's.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Read (BackwardUpToV)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **This track's `Step_read` rules, backward**, for the concrete builtins, under
`ReadValidS`. -/
theorem read_doneS (i : Nat) (hi : i ∈ readDoneS) (c : Config H) (w : Value) (hv : ReadValidS c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  simp only [readDoneS, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact bwdS_arrayInitDataZero c w hv hc hf
    | exact bwdS_arrayNewDefault c w hv hc hf
    | exact bwdS_arrayNewDataOob c w hv hc hf
    | exact bwdS_arrayInitDataOob₂ c w hv hc hf
    | exact bwdS_arrayNewElemAlloc c w hv hc hf
    | exact bwdS_arrayInitElemSucc c w hv hc hf
    | exact bwdR_arrayFillSucc c w hv.r hc hf
    | exact bwdR_arrayCopyZero c w hv.r hc hf
    | exact bwdS_arrayInitElemZero c w hv hc hf
    | exact (bwdS_vload _ (by simp) c w hv hf).elim

/-- **The cast rules, backward**, for the concrete builtins, under `ReadValidS`, from track
fwd's bridge `Fwd.RefOkB`. -/
theorem read_doneK (KB : Fwd.RefOkB (simEnv (BI P hn host))) (i : Nat) (hi : i ∈ readDoneK)
    (c : Config H) (w : Value) (hv : ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  simp only [readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwdK_brOnCastSucceed KB c w hv hc hf, bwdK_brOnCastFail KB c w hv hc hf,
    bwdK_brOnCastFailSucceed KB c w hv hc hf, bwdK_brOnCastFailFail KB c w hv hc hf,
    bwdK_refTestTrue KB c w hv hc hf, bwdK_refTestFalse KB c w hv hc hf,
    bwdK_refCastSucceed KB c w hv hc hf, bwdK_refCastFail KB c w hv hc hf]

/-- **`ReadOpenS` from what is left of it**, given track fwd's bridge `Fwd.RefOkB`. -/
theorem readOpenS_of_rest (KB : Fwd.RefOkB (simEnv (BI P hn host))) (R : ReadRest hn P host) :
    ReadOpenS hn P host :=
  fun i h₀ h₁ h₂ h₃ c w hv hc hf => by
    by_cases h₄ : i ∈ readDoneS
    · exact Bwd.read_upTo (read_doneS i h₄ c w hv hc hf)
    by_cases h₅ : i ∈ readDoneK
    · exact Bwd.read_upTo (read_doneK KB i h₅ c w hv hc hf)
    · exact R i (lt_of_fires_read hf) h₀ h₁ h₂ h₃ h₄ h₅ c w hv hc hf

/-- Pass 1's `Round5.Int.ReadOpen` gives `ReadOpenS`: the restatement asks no more. -/
theorem readOpenS_of_readOpen (R : Int.ReadOpen hn P host) : ReadOpenS hn P host :=
  fun i h₀ h₁ h₂ h₃ c w hv hc hf => R i h₀ h₁ h₂ h₃ c w hv.r hc hf

/-- `Step_pure`, backward, under `ReadValidS`, from `PartsOkS`. -/
theorem backwardS_pure (Pa : PartsOkS hn P host) (i : Nat) (s : Store H) (f : Frame)
    (is : List Admin) (w : Value) (hv : ReadValidS ⟨s, f, is⟩)
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

/-- `Step_read`, backward, under `ReadValidS`, from `PartsOkS`. -/
theorem backwardS_read (Pa : PartsOkS hn P host) (i : Nat) (c : Config H) (w : Value)
    (hv : ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
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

/-- `Step`, backward, under `ReadValidS`, from `PartsOkS`. -/
theorem backwardS_step (Pa : PartsOkS hn P host) (i : Nat) (h6 : 6 ≤ i) (c : Config H)
    (w : Value) (hv : ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    Bwd.BwdUpTo hn P host c w := by
  by_cases h₀ : i ∈ Bwd.stepDone
  · exact (Bwd.famBwdV_of_hostSteps Pa.hostSteps).step i h₀ c w hv.r.read hc hf
  by_cases h₁ : i ∈ BwdPureStep.stepDone
  · exact Bwd.step_upTo (BwdPureStep.step_done _ (BwdPureStep.bwdB_builtins hn host) i h₁ hf)
  · exact Pa.step i h6 h₀ h₁ c w hv.r hc hf

/-- **The per-rule backward obligations under `ReadValidS`**, for the concrete builtins, from
`PartsOkS`. -/
theorem backwardUpToS (Pa : PartsOkS hn P host) :
    BackwardUpToV ReadValidS (simEnv (BI P hn host)) hn P host :=
  ⟨backwardS_pure Pa, backwardS_read Pa, backwardS_step Pa⟩

/-- **The backward simulation from typed `ReadValidS` sources**, for the concrete builtins. -/
theorem backward_S (Pa : PartsOkS hn P host) (c : Config H) (w : Value) (hv : ReadValidS c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  Round4Read.backward_upToV readValidS_ctxClosed (backwardUpToS Pa)
    (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)) (Typing.typingFacts_simEnv _ hn)
    (hasStepRules_simEnv _) (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

/-- **The restated one-step simulation, from `PartsOkS`**, for a `HostOk` host. -/
theorem oneStepOk_of_partsOkS (Pa : PartsOkS hn P host) (hh : HostOk host) :
    (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Pos.BoundedNE c →
      Pos.BoundedNE c' → Step P host c c' → ∃ d', Bwd.ConfigEq c' d' ∧
        SStep (simEnv (BI P hn host)) (configV hn c) (configV hn d')) ∧
    (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → Pos.BoundedNE c →
      SStep (simEnv (BI P hn host)) (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c') :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨⟨ts, hc⟩, hb.1⟩, hb.2⟩ hb.1.store (Pos.typed_of_configOk_ne Pa.pos hc hb)
        (Pos.typed_of_configOk_ne Pa.pos (Step.preservation hh hc hs).1 hb') hs,
    fun c _ w hc hb hs =>
      backward_S Pa c w (readValidS_of_bounded hc hb.1) (Pos.typed_of_configOk_ne Pa.pos hc hb) hs⟩

/-- **`Round5.Task.wholeStepValidOk`, from `PartsOkS`** at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValidOk_of_partsOkS
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), PartsOkS hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk := fun H hn hinj host hfin hok nd r =>
  ⟨_, oneStepOk_of_partsOkS (h H hn hinj host hfin hok nd r) hok⟩

/-- `Round5.Int.PartsOkR` gives `PartsOkS`: the restated reduction asks no more. -/
theorem partsOkS_of_partsOkR (Pa : Int.PartsOkR hn P host) : PartsOkS hn P host where
  pos := Pa.pos
  fwd := Pa.fwd
  hostSteps := Pa.hostSteps
  pure := Pa.rem.pure
  read := fun i h₀ h₁ h₂ h₃ c w hv hc hf => Pa.rem.read i h₀ h₁ h₂ h₃ c w hv.r hc hf
  step := Pa.rem.step

/-- **`PartsOkS` from the open leaves `OpenS`**, for a finite host, in a profile where growth may
both succeed and fail. -/
theorem partsOkS_of_openS (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : OpenS hn P host) : PartsOkS hn P host where
  pos := Pos.posTypingNE_of_simd O.simd hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (Fwd.forward_valid_final (Int.typesB _) O.refOk hf O.hostRespects O.vector O.newDataNum)
  hostSteps := Bwd.hostStepsV_of_hostInv (Integrate.hostInv_concrete hf O.hostRespects)
  pure := fun i h₀ h₁ h₂ s f is w hv hc hf =>
    BwdStep.remPure_of_open O.vecAgree O.pureOpen i h₀ h₁ h₂ s f is w hv.read hc hf
  read := readOpenS_of_rest O.refOk O.read
  step := fun i h6 h₀ h₁ c w hv hc hf => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hf

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after pass 2, track read**, at
every injective encoding, finite `HostOk` host and `Profile.spec nd r`. -/
theorem wholeStepValidOk_of_openS
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenS hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  wholeStepValidOk_of_partsOkS fun H hn hinj host hfin hok nd r =>
    partsOkS_of_openS hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

/-- Pass 1's `Round5.Int.Open` gives `OpenS`: the new leaves ask no more. -/
theorem openS_of_open (O : Int.Open hn P host) : OpenS hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := O.hostRespects
  vector := O.vector
  newDataNum := O.newDataNum
  vecAgree := O.vecAgree
  pureOpen := O.pureOpen
  read := fun i _ h₀ h₁ h₂ h₃ _ _ c w hv hc hf => O.read i h₀ h₁ h₂ h₃ c w hv.r hc hf

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
