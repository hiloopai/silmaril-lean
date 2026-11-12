module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.VecTy
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Thms

/-!
# Round 5: `Int.VectorFwd` from the operator agreement alone

`fwd_vectorL` is family V's `Vec.fwd_vector` with `VecTypingL` for the false `Vec.VecTyping`
(family V's per-constructor lemmas take `VecTypingL`). With `vecTypingL` (proved) and track
simd's `vecAgree_of_ops`, the forward non-bitwise SIMD rules follow from `Simd.VecAgreeOps`:

* `vectorFwd_of_ops`: `Int.VectorFwd hn P host` from `VecAgreeOps`;
* `vector_of_open2`: so `Round5.Int2.Open2.vector` follows from `Open2.vecOps`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type}

/-- **Family V's forward vector steps from `VecTypingL`**: `Vec.fwd_vector` with the restated
typing interface. -/
theorem fwd_vectorL {env : Env} {hn : H → String} {P : Profile} (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 0 pureRule) (V : HasVectorRules env) (Ty : VecTypingL env)
    (A : Vec.VecAgree env P) (Fy : Vec.FloatTyping env) {s : Store H} {f : Frame}
    {is is' : List Admin} (h : VectorStep P is is') :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | vecUnOp op a => exact Vec.fwd_vecUnOp T hr V Ty A op a
  | vecBinOp op a b => exact Vec.fwd_vecBinOp T hr V Ty A op a b
  | vecTernOp op a b c => exact Vec.fwd_vecTernOp T hr V Ty A op a b c
  | vecTestOp op a => exact Vec.fwd_vecTestOp T hr V Ty A op a
  | vecIntUnOp sh op a => exact Vec.fwd_vecIntUnOp T hr V Ty A sh op a
  | vecFloatUnOp h => exact Vec.fwd_vecFloatUnOp T hr V Ty A h
  | vecFloatUnOpTrap h => exact Vec.fwd_vecFloatUnOpTrap T hr V Ty A h
  | vecIntBinOp sh op a b => exact Vec.fwd_vecIntBinOp T hr V Ty A sh op a b
  | vecFloatBinOp h => exact Vec.fwd_vecFloatBinOp T hr V Ty A h
  | vecFloatBinOpTrap h => exact Vec.fwd_vecFloatBinOpTrap T hr V Ty A h
  | vecIntTernOp sh op a b c => exact Vec.fwd_vecIntTernOp T hr V Ty A sh op a b c
  | vecFloatTernOp h => exact Vec.fwd_vecFloatTernOp T hr V Ty A h
  | vecFloatTernOpTrap h => exact Vec.fwd_vecFloatTernOpTrap T hr V Ty A h
  | vecAllTrue sh a => exact Vec.fwd_vecAllTrue T hr V Ty A sh a
  | vecIntRelOp sh op a b => exact Vec.fwd_vecIntRelOp T hr V Ty A sh op a b
  | vecFloatRelOp sh op a b => exact Vec.fwd_vecFloatRelOp T hr V Ty A sh op a b
  | vecShiftOp sh op a n => exact Vec.fwd_vecShiftOp T hr V Ty A sh op a n
  | vecBitmask sh a => exact Vec.fwd_vecBitmask T hr V Ty A sh a
  | vecSwizzle a b => exact Vec.fwd_vecSwizzle T hr V Ty A a b
  | vecRelaxedSwizzle a b => exact Vec.fwd_vecRelaxedSwizzle T hr V Ty A a b
  | vecShuffle idx a b hidx => exact Vec.fwd_vecShuffle T hr V Ty A idx a b hidx
  | vecSplat sh x => exact Vec.fwd_vecSplat T hr V Ty A sh x
  | vecExtractLane sh sx i a hi => exact Vec.fwd_vecExtractLane T hr V Ty A Fy sh sx i a hi
  | vecReplaceLane sh i a x hi => exact Vec.fwd_vecReplaceLane T hr V Ty A sh i a x hi
  | vecExtUnOp h => exact Vec.fwd_vecExtUnOp T hr V Ty A h
  | vecExtBinOp h => exact Vec.fwd_vecExtBinOp T hr V Ty A h
  | vecExtTernOp h => exact Vec.fwd_vecExtTernOp T hr V Ty A h
  | vecNarrow h => exact Vec.fwd_vecNarrow T hr V Ty A h
  | vecConvert h => exact Vec.fwd_vecConvert T hr V Ty A h

/-- **`Int.VectorFwd` from the lane-wise operator agreement alone.** -/
theorem vectorFwd_of_ops {P : Profile} {hn : H → String} {host : HostSemantics H}
    (O : Simd.VecAgreeOps (simEnv (BI P hn host)) P) : Int.VectorFwd hn P host :=
  fun _ _ _ _ h _ _ => fwd_vectorL (Typing.typingFacts_simEnv _ hn) (hasStepRules_simEnv _).pure
    (Vec.hasVectorRules_simEnv _) (vecTypingL P hn host) (Simd.vecAgree_of_ops O)
    (Floats.floatTyping_simEnv _) h

/-- **`Open2.vector` follows from `Open2.vecOps`.** -/
theorem vector_of_open2 {P : Profile} {hn : H → String} {host : HostSemantics H}
    (O : Int2.Open2 hn P host) : Int.VectorFwd hn P host :=
  vectorFwd_of_ops O.vecOps

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
