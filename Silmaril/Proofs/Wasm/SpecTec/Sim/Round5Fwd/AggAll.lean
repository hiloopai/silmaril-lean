module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggInit

/-!
# Round 5: the aggregate steps from a bounded configuration

`fwd_aggregate5` is `R4Fwd.fwd_aggregate_any` at the concrete `B`, with
`AggTypesB` (bounded types) for the refuted `Aggregates.AggTypes`, and `array.new_data-num`,
`array.init_data-zero` from the bounded obligations `NewDataNumB`, `InitDataZeroB`. The frame's
module bound is installed as a local instance for the copied lemmas (`Round5Fwd/Agg*.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Aggregates
open R4Fwd
open RefsGC (RTyping RStoreFuns)
open Round4 (Bounded ModuleBnd)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The aggregate steps from a bounded configuration**, for the concrete `B`, from
`AggTypesB` and the two bounded obligations. -/
theorem fwd_aggregate5 (A : AggTypesB (simEnv (BI P hn host)))
    (hND : NewDataNumB (BI P hn host) hn) (hIZ : InitDataZeroB (BI P hn host) hn)
    {c c' : Config H} (h : AggregateStep c c') (hb : Bounded c) :
    FwdP (simEnv (BI P hn host)) hn c c' := by
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have hV : FwdSimdAgg.VVB (BI P hn host) := FwdSimdAgg.vvB_builtins hn host
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have hsb : Aggregates.Bounded c.store := hb.store.aggs
  have : Fact (ModuleBnd c.frame.module) := ⟨hb.frame⟩
  cases h with
  | structNew hd he hn hp => exact fwd_structNewAnyB hF T R A hd he hn hp
  | structNewDefault hd he hdef =>
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz _ =>
      sread_structNewDefaultAnyB R A hd he hdef hz
  | structGetNull => exact fwd_structGetNull T R G
  | structGetStruct hs hf hd he hi hu' =>
    exact fwd_structGetStruct_anyB hF T R A hs hf hd he hi hu'
  | structSetNull => exact fwd_structSetNull T R G
  | structSetStruct hd he hi hs hf hp =>
    exact fwd_structSetStruct_anyB hF T R A hd he hi hs hf hp
  | arrayNew v n => exact fwd_arrayNew T R v n
  | @arrayNewDefault s f x n d ft v hd he hv =>
    obtain ⟨m, zt⟩ := ft
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz _ =>
      sread_arrayNewDefaultAnyB R A hd he hv hz
  | @arrayNewFixed s f x n d ft vs hd he hn hp =>
    obtain ⟨m, zt⟩ := ft
    exact fwd_arrayNewFixedAnyB hF T R A hd he hn hp
  | arrayNewElemOob he hl => exact fwd_arrayNewElemOob T R G he hl
  | arrayNewElemAlloc he hl => exact fwd_arrayNewElemAlloc T R G he hl
  | arrayGetNull => exact fwd_arrayGetNull T R G
  | arrayGetOob ha hl => exact fwd_arrayGetOob T R G ha hl
  | arrayGetArray ha hf hd he hu' => exact fwd_arrayGetArray_anyB hF T R A ha hf hd he hu'
  | arraySetNull => exact fwd_arraySetNull T R G
  | arraySetOob ha hl => exact fwd_arraySetOob T R G ha hl
  | arraySetArray ha hl hd he hp => exact fwd_arraySetArray_anyB hF T R A ha hl hd he hp
  | arrayLenNull => exact fwd_arrayLenNull T R G
  | arrayLenArray ha => exact fwd_arrayLenArray T R G ha hsb
  | arrayFillNull => exact fwd_arrayFillNull T R G
  | arrayFillOob ha hl => exact fwd_arrayFillOob T R G ha hl
  | arrayFillZero ha hl => exact fwd_arrayFillZero T R G ha hl
  | arrayFillSucc ha hl hn0 => exact fwd_arrayFillSucc T R G ha hl hn0 hsb
  | arrayCopyNull₁ => exact fwd_arrayCopyNull₁ T R G
  | arrayCopyNull₂ => exact fwd_arrayCopyNull₂ T R G
  | arrayCopyOob₁ ha hl => exact fwd_arrayCopyOob₁ T R G ha hl
  | arrayCopyOob₂ ha hl => exact fwd_arrayCopyOob₂ T R G ha hl
  | arrayCopyZero ha₁ ha₂ hl => exact fwd_arrayCopyZero T R G ha₁ ha₂ hl
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn0 hd he hle =>
    obtain ⟨m, zt⟩ := ft₂
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz _ =>
      sread_arrayCopyLeAnyB (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ hl hn0 hd he hle
        (hsb.array ha₁) (hsb.array ha₂) hz
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn0 hd he hgt =>
    obtain ⟨m, zt⟩ := ft₂
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz _ =>
      sread_arrayCopyGtAnyB (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ hl hn0 hd he hgt
        (hsb.array ha₁) (hsb.array ha₂) hz
  | arrayInitElemNull => exact fwd_arrayInitElemNull T R G
  | arrayInitElemOob₁ ha hl => exact fwd_arrayInitElemOob₁ T R G ha hl
  | arrayInitElemOob₂ he hl => exact fwd_arrayInitElemOob₂ T R G he hl
  | arrayInitElemZero ha he hl => exact fwd_arrayInitElemZero T R G ha he hl
  | arrayInitElemSucc ha he hl hn0 hr =>
    exact FwdSimdAgg.fwd_arrayInitElemSucc T R G hsb ha he hl hn0 hr
  | arrayNewDataOob hd he hdat hz hl => exact fwd_arrayNewDataOobB T R A hd he hdat hz hl
  | arrayNewDataNum hd he hdat hz hl hvs =>
    exact hND _ _ _ _ _ _ _ _ _ _ _ hb.frame hd he hdat hz hl hvs
  | arrayInitDataNull => exact fwd_arrayInitDataNull T R G
  | arrayInitDataOob₁ ha hl => exact fwd_arrayInitDataOob₁ T R G ha hl
  | arrayInitDataOob₂ hd he hdat hz hl => exact fwd_arrayInitDataOob₂B T R A hd he hdat hz hl
  | arrayInitDataZero ha hdat hl => exact hIZ _ _ _ _ _ _ _ _ _ _ hb ha hdat hl
  | arrayInitDataNum ha hd he hdat hl hn0 hv =>
    exact fwd_arrayInitDataNumB hF (zB_builtins hn host) (expandInv_builtins hn host)
      (litTyping_simEnv _) T R G A hsb ha hd he hdat hl hn0 hv

/-- **The forward conjunct on valid, bounded sources** (the `fwd` field of `Round4Int.Parts`),
from `TypesB`, `RefOkB`, a finite host respecting the encoding, the non-bitwise SIMD operators
and the two bounded data-segment obligations. -/
theorem forward_valid_agg (TB : TypesB (simEnv (BI P hn host)))
    (KB : RefOkB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host)
    (vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
      (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Bounded ⟨s, f, is⟩ →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩)
    (hND : NewDataNumB (BI P hn host) hn) (hIZ : InitDataZeroB (BI P hn host) hn) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  forward_valid_tb TB KB hf hr vector fun _ _ h hb => fwd_aggregate5 (aggTypesB_of TB) hND hIZ h hb

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
