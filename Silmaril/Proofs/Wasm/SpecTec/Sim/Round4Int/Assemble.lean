module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Int.Valid

/-!
# Round 4 integration: the assembled reduction

* `famBwdV_of_hyps`: the old family bundles imply the rule-level `FamBwdV`.
* `backwardUpToV_of_fam`: track r4-read's dispatch with `FamBwdV` in place of `Bwd.BwdHyps`.
* `backward_fam`: the backward simulation from typed `ReadValid` sources for the concrete `B`,
  from `FamBwdV` and `RemainingV` only (no refuted bundle).
* `backward_valid4`: the same from valid, bounded sources, with `Typed` from `PosTyping`.
* `succTyped_of_hostOk`, `oneStep_of_parts`, `wholeStepValid_of_parts`: the frozen round-4
  target from `Parts`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Read (ReadValid RemainingV BackwardUpToV)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The family bundles imply the rule-level restatement.** So `FamBwdV` is no stronger than
what rounds 1–3 assumed, and holds wherever `Bwd.BwdHyps` does. -/
theorem famBwdV_of_hyps (B : Builtins) (Hy : Bwd.BwdHyps B hn host)
    (T : TypingFacts (simEnv B) hn) : FamBwdV (simEnv B) hn P host where
  pure i h s f is w _ hc hf := Bwd.pure_upTo (Bwd.pure_done B Hy i h s f is w hc hf)
  read i h c w _ hc hf := by
    by_cases h11 : i = 11
    · exact Bwd.bwdUpTo_returnCallRefFrameAddr B Hy.ctrlDecode Hy.ctrlState Hy.callInv c w hc
        (h11 ▸ hf)
    · have h₀ : i ∈ Bwd.readDone := by simpa [Bwd.readDoneUpTo, h11] using h
      exact Bwd.read_upTo (Bwd.read_done B Hy T i h₀ c w hc hf)
  step i h c w _ hc hf := Bwd.step_upTo (Bwd.step_done B Hy i h c w hc hf)

/-- **The per-rule obligations under validity, without `Bwd.BwdHyps`**: track r4-read's
`backwardUpToV_dispatch` with the family rules taken from `FamBwdV`. -/
theorem backwardUpToV_of_fam (B : Builtins) (hI : IntNumeric.IntB B) (hF : Floats.FloatB P B)
    (Hb : BwdPureStep.BwdB B) (NA : BwdRead.NoAcc B) (Fm : FamBwdV (simEnv B) hn P host)
    (Rm : RemainingV (simEnv B) hn P host) : BackwardUpToV ReadValid (simEnv B) hn P host where
  pure i s f is w hv hc hf := by
    by_cases h₀ : i ∈ Bwd.pureDone
    · exact Fm.pure i h₀ s f is w hv hc hf
    by_cases h₁ : i ∈ Integrate.floatDone
    · exact Integrate.pure_floatDone hI hF h₁ hf
    by_cases h₂ : i ∈ BwdPureStep.pureDone
    · exact Bwd.pure_upTo (BwdPureStep.pure_done B Hb i h₂ hf)
    exact Rm.pure i h₀ h₁ h₂ s f is w hv hc hf
  read i c w hv hc hf := by
    by_cases h₀ : i ∈ Bwd.readDoneUpTo
    · exact Fm.read i h₀ c w hv hc hf
    by_cases h₁ : i ∈ BwdRead.readDone
    · exact Bwd.read_upTo (BwdRead.read_done B NA i h₁ c w hc hf)
    by_cases h₂ : i ∈ Round4Read.readDoneV
    · exact Bwd.read_upTo (Round4Read.read_doneV B NA i h₂ c w hv hc hf)
    exact Rm.read i h₀ h₁ h₂ c w hv hc hf
  step i h6 c w hv hc hf := by
    by_cases h₀ : i ∈ Bwd.stepDone
    · exact Fm.step i h₀ c w hv hc hf
    by_cases h₁ : i ∈ BwdPureStep.stepDone
    · exact Bwd.step_upTo (BwdPureStep.step_done B Hb i h₁ hf)
    exact Rm.step i h6 h₀ h₁ c w hv hc hf

/-- **The backward simulation from typed `ReadValid` sources, for the concrete `B`**, from the
rule-level obligations `FamBwdV` and `RemainingV` alone. -/
theorem backward_fam (Fm : FamBwdV (simEnv (BI P hn host)) hn P host)
    (Rm : RemainingV (simEnv (BI P hn host)) hn P host) (c : Config H) (w : Value)
    (hv : ReadValid c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  Round4Read.backward_upToV Round4Read.readValid_ctxClosed
    (backwardUpToV_of_fam _ (Prims.intB_builtins hn host) (Prims.floatB_builtins hn host)
      (BwdPureStep.bwdB_builtins hn host) (BwdRead.noAcc_builtins _ hn host) Fm Rm)
    (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)) (Typing.typingFacts_simEnv _ hn)
    (hasStepRules_simEnv _) (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

/-- **The backward conjunct of `Round4.Task.wholeStepValid`**, for the concrete `B`, from
`PosTyping`, `FamBwdV` and `RemainingV`. -/
theorem backward_valid4 (K : Round4.PosTyping (BI P hn host) hn)
    (Fm : FamBwdV (simEnv (BI P hn host)) hn P host)
    (Rm : RemainingV (simEnv (BI P hn host)) hn P host) (c : Config H) (ts : List CValType)
    (w : Value) (hc : ConfigOk c ts) (hb : Round4.Bounded c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backward_fam Fm Rm c w (readValid_of_bounded hc hb) (Round4.typed_of_configOk K hc hb) hs

/-- **Track r4-read's dispatched rules, from Core validity**: no `ReadValid` hypothesis left. -/
theorem read_doneV_of_configOk (B : Builtins) (NA : BwdRead.NoAcc B) (i : Nat)
    (hi : i ∈ Round4Read.readDoneV) (c : Config H) (ts : List CValType) (w : Value)
    (hok : ConfigOk c ts) (hs : Integrate.StoreOk c.store) (hc : Typed (simEnv B) hn c)
    (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  Round4Read.read_doneV B NA i hi c w (readValid_of_configOk hok hs) hc hf

/-- **`Parts.succTyped` for `HostOk` hosts**, from `PosTyping` and Core's subject reduction. -/
theorem succTyped_of_hostOk {B : Builtins} (K : Round4.PosTyping B hn) (hh : HostOk host)
    (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (_ : Round4.Bounded c)
    (hb' : Round4.Bounded c') (hs : Step P host c c') : Typed (simEnv B) hn c' :=
  Round4.typed_of_configOk K (Step.preservation hh hc hs).1 hb'

/-- **The one-step simulation over valid, bounded configurations, from `Parts`.** -/
theorem oneStep_of_parts (Pa : Parts hn P host) : Round4.OneStep (BI P hn host) hn P host :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨ts, hc⟩, hb⟩ hb.store (Round4.typed_of_configOk Pa.pos hc hb)
        (Pa.succTyped c c' ts hc hb hb' hs) hs,
    fun c ts w hc hb hs => backward_valid4 Pa.pos Pa.fam Pa.rem c ts w hc hb hs⟩

/-- **The frozen round-4 target, from `Parts`** at every injective encoding, finite host and
`Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValid_of_parts
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Parts hn (Profile.spec nd r) host) :
    Round4.Task.wholeStepValid := fun H hn hinj host hfin nd r =>
  ⟨_, oneStep_of_parts (h H hn hinj host hfin nd r)⟩

end Silmaril.Wasm.SpecTec.Sim.Round4Int
