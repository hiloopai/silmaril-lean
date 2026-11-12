module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.FwdNC
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.FwdNCLanes
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Undef
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms

/-!
# Round 5: the forward vector steps from the restated leaves

* `vecAgreeNC_of_lanes`: `VecAgreeNC` at the concrete builtins from `Simd.VecAgreeLanes` (the
  bitwise and lane fields are track simd's, as in `Simd.vecAgree_of_ops`);
* `fwdN_vecConvertR`: `vcvtop` forward from `Simd.VecConvertR`, to the result SpecTec's
  `$vcvtop__` picks, which Core allows;
* `fwd_vectorR`: every Core vector step is matched up to Core's choice (`VectorFwdR`'s shape);
* `vectorFwdR_of`, `vectorFwdR_builtins`: `VectorFwdR` from the restated leaves, hence
  unconditionally; `vectorFwdDet_builtins`: `Round5.Int.VectorFwd` on deterministic steps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Vec (typed_last2 typed_code fwd_of_spure spure_vcvtop InstrTyped)
open Round4Int (BI)

variable {H : Type}

/-- **`VecAgreeNC` at the concrete builtins, from `Simd.VecAgreeLanes`.** -/
theorem vecAgreeNC_of_lanes {P : Profile} {hn : H → String} {host : HostSemantics H}
    (L : Simd.VecAgreeLanes (simEnv (BI P hn host)) P) : VecAgreeNC (simEnv (BI P hn host)) P where
  vvunop := FwdSimdAgg.applies_vvunop (FwdSimdAgg.vvB_builtins hn host)
  vvbinop := FwdSimdAgg.applies_vvbinop (Prims.intB_builtins hn host)
    (FwdSimdAgg.vvB_builtins hn host)
  vvternop := FwdSimdAgg.applies_vvternop (FwdSimdAgg.vvB_builtins hn host)
  vvtestop op a := by
    cases op
    exact ⟨_, FwdSimdAgg.applies_vsize, FwdSimdAgg.applies_inez a⟩
  intUnOp := L.intUnOp
  floatUnOp := L.floatUnOp
  intBinOp := L.intBinOp
  floatBinOp := L.floatBinOp
  intTernOp := L.intTernOp
  floatTernOp := L.floatTernOp
  intRelOp := L.intRelOp
  floatRelOp := L.floatRelOp
  shiftOp := L.shiftOp
  bitmask := L.bitmask
  swizzle := L.swizzle
  relaxedSwizzle := L.relaxedSwizzle
  shuffle := L.shuffle
  extUnOp := L.extUnOp
  extBinOp := L.extBinOp
  extTernOp := L.extTernOp
  narrow := L.narrow
  extractNum := Simd.extractNum P hn host
  extractPack := Simd.extractPack P hn host
  replaceLane := Simd.replaceLane P hn host
  splat := Simd.splat P hn host
  allTrue := Simd.allTrue P hn host

/-- **`VecAgreeNC` at the concrete builtins.** -/
theorem vecAgreeNC_builtins {P : Profile} {hn : H → String} {host : HostSemantics H} :
    VecAgreeNC (simEnv (BI P hn host)) P :=
  vecAgreeNC_of_lanes Simd.vecAgreeLanes_builtins

section

variable {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env)
  {s : Store H} {f : Frame}

include T hr V Ty

/-- **`VectorStep.vecConvert`, forward to the value `$vcvtop__` denotes** (`Step_pure/vcvtop`). -/
theorem fwdN_vecConvertR {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
    (ha : Applies env "vcvtop__" [.val (Vec.shapeV sh₁), .val (Vec.shapeV sh₂),
      .val (Vec.vConvertOpV op), .val (Vec.vecV a)] (Vec.vecV r)) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecConvert sh₁ sh₂ op)]⟩ ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecConvert sh₁ sh₂ op) := typed_last2 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vcvtop V.vcvtop (Ty.vec a) (Ty.shape sh₂) (Ty.shape sh₁)
    (Ty.convert sh₁ sh₂ op hi) (Ty.vec r) ha) hc hc'

/-- **The `vcvtop` step, up to Core's choice**: SpecTec steps to the result `$vcvtop__` picks, a
Core vector step from the same code, and the given one when Core's step is unique. -/
theorem fwd_convertR (C : Simd.VecConvertR env P) {sh₁ sh₂ : Shape} {op : VecConvertOp}
    {a r : V128} (h : VecConvertRel P sh₁ sh₂ op a r) :
    ∃ is'', VectorStep P [vconst a, .plain (.vecConvert sh₁ sh₂ op)] is'' ∧
      ((∀ is₃, VectorStep P [vconst a, .plain (.vecConvert sh₁ sh₂ op)] is₃ →
        is₃ = [vconst r]) → is'' = [vconst r]) ∧
      FwdP env hn ⟨s, f, [vconst a, .plain (.vecConvert sh₁ sh₂ op)]⟩ ⟨s, f, is''⟩ := by
  obtain ⟨c, hc⟩ := C.total sh₁ sh₂ op a r h
  obtain ⟨r', hr', rfl⟩ := C.sound sh₁ sh₂ op a c hc
  exact ⟨_, .vecConvert hr', fun hd => hd _ (.vecConvert hr'), fwdN_vecConvertR T hr V Ty hc⟩

/-- **Every Core vector step, forward up to Core's choice**, from `VecAgreeNC` and
`Simd.VecConvertR`: the shape of `VectorFwdR`. Every constructor but `vecConvert` is matched
exactly (the copied `fwdN_vec…` lemmas). -/
theorem fwd_vectorR (A : VecAgreeNC env P) (C : Simd.VecConvertR env P) (Fy : Vec.FloatTyping env)
    {is is' : List Admin} (h : VectorStep P is is') :
    ∃ is'', VectorStep P is is'' ∧ ((∀ is₃, VectorStep P is is₃ → is₃ = is') → is'' = is') ∧
      FwdP env hn ⟨s, f, is⟩ ⟨s, f, is''⟩ := by
  have h₀ : VectorStep P is is' := h
  cases h with
  | vecConvert hc => exact fwd_convertR T hr V Ty C hc
  | vecUnOp op a => exact ⟨_, h₀, fun _ => rfl, fwdN_vecUnOp T hr V Ty A op a⟩
  | vecBinOp op a b => exact ⟨_, h₀, fun _ => rfl, fwdN_vecBinOp T hr V Ty A op a b⟩
  | vecTernOp op a b c => exact ⟨_, h₀, fun _ => rfl, fwdN_vecTernOp T hr V Ty A op a b c⟩
  | vecTestOp op a => exact ⟨_, h₀, fun _ => rfl, fwdN_vecTestOp T hr V Ty A op a⟩
  | vecIntUnOp sh op a => exact ⟨_, h₀, fun _ => rfl, fwdN_vecIntUnOp T hr V Ty A sh op a⟩
  | vecFloatUnOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatUnOp T hr V Ty A h⟩
  | vecFloatUnOpTrap h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatUnOpTrap T hr V Ty A h⟩
  | vecIntBinOp sh op a b => exact ⟨_, h₀, fun _ => rfl, fwdN_vecIntBinOp T hr V Ty A sh op a b⟩
  | vecFloatBinOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatBinOp T hr V Ty A h⟩
  | vecFloatBinOpTrap h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatBinOpTrap T hr V Ty A h⟩
  | vecIntTernOp sh op a b c =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecIntTernOp T hr V Ty A sh op a b c⟩
  | vecFloatTernOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatTernOp T hr V Ty A h⟩
  | vecFloatTernOpTrap h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatTernOpTrap T hr V Ty A h⟩
  | vecAllTrue sh a => exact ⟨_, h₀, fun _ => rfl, fwdN_vecAllTrue T hr V Ty A sh a⟩
  | vecIntRelOp sh op a b => exact ⟨_, h₀, fun _ => rfl, fwdN_vecIntRelOp T hr V Ty A sh op a b⟩
  | vecFloatRelOp sh op a b =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecFloatRelOp T hr V Ty A sh op a b⟩
  | vecShiftOp sh op a n => exact ⟨_, h₀, fun _ => rfl, fwdN_vecShiftOp T hr V Ty A sh op a n⟩
  | vecBitmask sh a => exact ⟨_, h₀, fun _ => rfl, fwdN_vecBitmask T hr V Ty A sh a⟩
  | vecSwizzle a b => exact ⟨_, h₀, fun _ => rfl, fwdN_vecSwizzle T hr V Ty A a b⟩
  | vecRelaxedSwizzle a b =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecRelaxedSwizzle T hr V Ty A a b⟩
  | vecShuffle idx a b hidx =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecShuffle T hr V Ty A idx a b hidx⟩
  | vecSplat sh x => exact ⟨_, h₀, fun _ => rfl, fwdN_vecSplat T hr V Ty A sh x⟩
  | vecExtractLane sh sx i a hi =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecExtractLane T hr V Ty A Fy sh sx i a hi⟩
  | vecReplaceLane sh i a x hi =>
      exact ⟨_, h₀, fun _ => rfl, fwdN_vecReplaceLane T hr V Ty A sh i a x hi⟩
  | vecExtUnOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecExtUnOp T hr V Ty A h⟩
  | vecExtBinOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecExtBinOp T hr V Ty A h⟩
  | vecExtTernOp h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecExtTernOp T hr V Ty A h⟩
  | vecNarrow h => exact ⟨_, h₀, fun _ => rfl, fwdN_vecNarrow T hr V Ty A h⟩

end

/-- **`VectorFwdR` from the restated leaves**, `Simd.VecAgreeLanes` and `Simd.VecConvertR`. -/
theorem vectorFwdR_of {P : Profile} {hn : H → String} {host : HostSemantics H}
    (L : Simd.VecAgreeLanes (simEnv (BI P hn host)) P)
    (C : Simd.VecConvertR (simEnv (BI P hn host)) P) : VectorFwdR hn P host :=
  fun _ _ _ _ h _ _ => fwd_vectorR (Typing.typingFacts_simEnv _ hn) (hasStepRules_simEnv _).pure
    (Vec.hasVectorRules_simEnv _) (SimdTy.vecTypingL P hn host) (vecAgreeNC_of_lanes L) C
    (Floats.floatTyping_simEnv _) h

/-- **`VectorFwdR` at the concrete builtins**, with no hypothesis. -/
theorem vectorFwdR_builtins {P : Profile} {hn : H → String} {host : HostSemantics H} :
    VectorFwdR hn P host :=
  vectorFwdR_of Simd.vecAgreeLanes_builtins vecConvertR_builtins

/-- `VectorFwdR` gives the forward vector steps Core takes deterministically. -/
theorem vectorFwdDet_of_R {P : Profile} {hn : H → String} {host : HostSemantics H}
    (R : VectorFwdR hn P host) : VectorFwdDet hn P host := by
  intro s f is is' h hd ha hb
  obtain ⟨is'', -, he, hf⟩ := R s f is is' h ha hb
  exact he hd ▸ hf

/-- **`Round5.Int.VectorFwd` on deterministic vector steps, at the concrete builtins.** -/
theorem vectorFwdDet_builtins {P : Profile} {hn : H → String} {host : HostSemantics H} :
    VectorFwdDet hn P host :=
  vectorFwdDet_of_R vectorFwdR_builtins

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
