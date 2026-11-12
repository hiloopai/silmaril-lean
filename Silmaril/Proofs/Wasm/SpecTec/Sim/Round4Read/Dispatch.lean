module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.TableInit
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.MemInit
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.Agg
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.Loads
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.Refs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.Concrete

/-!
# The dispatch under validity

* `read_doneV`: every index of `readDoneV` has its backward lemma under `ReadValid`, for every
  `B` with `NoAcc B` (proved for the concrete `B`, `BwdRead.noAcc_builtins`).
* `backwardUpToV_dispatch`: every rule dispatched by rounds 1–4 (families, tracks backward,
  bwd-pure-step, bwd-read, the float track and this one), plus `RemainingV`, give the per-rule
  obligations `BackwardUpToV ReadValid`.
* `backward_valid`: the backward simulation from every typed source satisfying `ReadValid`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The dispatch under validity**: every index of `readDoneV` has its backward lemma. -/
theorem read_doneV (B : Builtins) (NA : BwdRead.NoAcc B) (i : Nat) (hi : i ∈ readDoneV)
    (c : Config H) (w : Value) (hv : ReadValid c) (hc : Typed (simEnv B) hn c)
    (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  simp only [readDoneV, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [bwdV_tableSize B NA c w hv hc hf, bwdV_tableFillZero B c w hv hc hf,
    bwdV_tableFillSucc B c w hv hc hf, bwdV_tableCopyOob B c w hv hc hf,
    bwdV_tableCopyZero B c w hv hc hf, bwdV_tableCopyLe B c w hv hc hf,
    bwdV_tableCopyGt B c w hv hc hf, bwdV_tableInitOob B c w hv hc hf,
    bwdV_tableInitZero B c w hv hc hf, bwdV_tableInitSucc B c w hv hc hf,
    bwdV_memorySize B NA c w hv hc hf, bwdV_memoryFillZero B c w hv hc hf,
    bwdV_memoryFillSucc B c w hv hc hf, bwdV_memoryCopyOob B c w hv hc hf,
    bwdV_memoryCopyZero B c w hv hc hf, bwdV_memoryCopyLe B c w hv hc hf,
    bwdV_memoryCopyGt B c w hv hc hf, bwdV_memoryInitOob B c w hv hc hf,
    bwdV_memoryInitZero B c w hv hc hf, bwdV_memoryInitSucc B c w hv hc hf,
    bwdV_arrayLenArray B c w hv hc hf, bwdV_loadNumOob B NA c w hv hc hf,
    bwdV_loadPackOob B NA c w hv hc hf, bwdV_refNull B c w hv hc hf,
    bwdV_refFunc B c w hv hc hf, bwdV_arrayFillOob B c w hv hc hf]

/-- **The per-rule obligations under validity**, from every lemma of rounds 1–4 and the open
rules `RemainingV`. The hypotheses are those of `Bwd.backwardUpTo_of` and
`Integrate.remaining_of_w` (family structures `BwdHyps`, `TypingFacts`, the integer and float
primitives, `BwdPureStep.BwdB`, `NoAcc`). -/
theorem backwardUpToV_dispatch (B : Builtins) (Hy : Bwd.BwdHyps B hn host)
    (T : TypingFacts (simEnv B) hn) (hI : IntNumeric.IntB B) (hF : Floats.FloatB P B)
    (Hb : BwdPureStep.BwdB B) (NA : BwdRead.NoAcc B) (Rm : RemainingV (simEnv B) hn P host) :
    BackwardUpToV ReadValid (simEnv B) hn P host where
  pure i s f is w hv hc hf := by
    by_cases h₀ : i ∈ Bwd.pureDone
    · exact Bwd.pure_upTo (Bwd.pure_done B Hy i h₀ s f is w hc hf)
    by_cases h₁ : i ∈ Integrate.floatDone
    · exact Integrate.pure_floatDone hI hF h₁ hf
    by_cases h₂ : i ∈ BwdPureStep.pureDone
    · exact Bwd.pure_upTo (BwdPureStep.pure_done B Hb i h₂ hf)
    exact Rm.pure i h₀ h₁ h₂ s f is w hv hc hf
  read i c w hv hc hf := by
    by_cases h11 : i = 11
    · exact Bwd.bwdUpTo_returnCallRefFrameAddr B Hy.ctrlDecode Hy.ctrlState Hy.callInv c w hc
        (h11 ▸ hf)
    by_cases h₀ : i ∈ Bwd.readDone
    · exact Bwd.read_upTo (Bwd.read_done B Hy T i h₀ c w hc hf)
    by_cases h₁ : i ∈ BwdRead.readDone
    · exact Bwd.read_upTo (BwdRead.read_done B NA i h₁ c w hc hf)
    by_cases h₂ : i ∈ readDoneV
    · exact Bwd.read_upTo (read_doneV B NA i h₂ c w hv hc hf)
    exact Rm.read i (by simp [Bwd.readDoneUpTo, h11, h₀]) h₁ h₂ c w hv hc hf
  step i h6 c w hv hc hf := by
    by_cases h₀ : i ∈ Bwd.stepDone
    · exact Bwd.step_upTo (Bwd.step_done B Hy i h₀ c w hc hf)
    by_cases h₁ : i ∈ BwdPureStep.stepDone
    · exact Bwd.step_upTo (BwdPureStep.step_done B Hb i h₁ hf)
    exact Rm.step i h6 h₀ h₁ c w hv hc hf

/-- **The backward simulation from valid sources** (SpecTec → Core, up to `ConfigEq`): every
SpecTec step from the image of a typed configuration satisfying `ReadValid` lands on the image
of a configuration equivalent to a Core successor, given the hypotheses of `backwardUpToV_dispatch`. -/
theorem backward_valid (B : Builtins) (Hy : Bwd.BwdHyps B hn host)
    (T : TypingFacts (simEnv B) hn) (hI : IntNumeric.IntB B) (hF : Floats.FloatB P B)
    (Hb : BwdPureStep.BwdB B) (NA : BwdRead.NoAcc B) (Rm : RemainingV (simEnv B) hn P host)
    (c : Config H) (w : Value) (hv : ReadValid c) (hc : Typed (simEnv B) hn c)
    (hs : SStep (simEnv B) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backward_upToV readValid_ctxClosed (backwardUpToV_dispatch B Hy T hI hF Hb NA Rm)
    (Bwd.structDecode_of_ctrl Hy.ctrlDecode) T (hasStepRules_simEnv B)
    (Bwd.findRel_of_ruleAt (simEnv_execRules B).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules B).call) c w hv hc hs

/-- **The backward simulation from valid sources, for the concrete `B`**: `backward_valid` at
`Prims.builtins`, with every primitive structure discharged; what remains is `Bwd.BwdHyps`
(families C, X, M, through `Integrate.bwdHyps_concrete`) and `RemainingV`. -/
theorem backward_validConcrete (prof : Numerics.Profile)
    (Hy : Bwd.BwdHyps (Prims.builtins prof hn host) hn host)
    (Rm : RemainingV (simEnv (Prims.builtins prof hn host)) hn prof host)
    (c : Config H) (w : Value) (hv : ReadValid c)
    (hc : Typed (simEnv (Prims.builtins prof hn host)) hn c)
    (hs : SStep (simEnv (Prims.builtins prof hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step prof host c c' :=
  backward_valid _ Hy (Typing.typingFacts_simEnv _ hn) (Prims.intB_builtins hn host)
    (Prims.floatB_builtins hn host) (BwdPureStep.bwdB_builtins hn host)
    (BwdRead.noAcc_builtins _ hn host) Rm c w hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round4Read
