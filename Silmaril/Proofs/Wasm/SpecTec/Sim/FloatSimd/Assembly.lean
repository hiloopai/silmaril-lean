module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Splat

/-!
# Family V: `Forward.vector`, assembled

`fwd_vector` has exactly the type of the `Forward.vector` obligation, from the per-constructor
lemmas of `Forward.lean`, `Lanes.lean` and `Splat.lean` and the interfaces `VecTyping`, `VecAgree`
and `FloatTyping` (for the numeral typing of extracted lanes). Every one of the 29 constructors of
`VectorStep` goes through its SpecTec rule; nothing is left as a hypothesis on steps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}

/-! ## `Forward.vector`, assembled -/

/-- **`Forward.vector`**, given the typing and agreement interfaces: every constructor of
`VectorStep`. -/
theorem fwd_vector (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
    (V : HasVectorRules env) (Ty : VecTyping env) (A : VecAgree env P)
    (Fy : FloatTyping env) {s : Store H} {f : Frame} {is is' : List Admin}
    (h : VectorStep P is is') :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have TyL : Round5.SimdTy.VecTypingL env := Round5.SimdTy.ofVecTyping Ty
  cases h with
  | vecUnOp op a => exact fwd_vecUnOp T hr V TyL A op a
  | vecBinOp op a b => exact fwd_vecBinOp T hr V TyL A op a b
  | vecTernOp op a b c => exact fwd_vecTernOp T hr V TyL A op a b c
  | vecTestOp op a => exact fwd_vecTestOp T hr V TyL A op a
  | vecIntUnOp sh op a => exact fwd_vecIntUnOp T hr V TyL A sh op a
  | vecFloatUnOp h => exact fwd_vecFloatUnOp T hr V TyL A h
  | vecFloatUnOpTrap h => exact fwd_vecFloatUnOpTrap T hr V TyL A h
  | vecIntBinOp sh op a b => exact fwd_vecIntBinOp T hr V TyL A sh op a b
  | vecFloatBinOp h => exact fwd_vecFloatBinOp T hr V TyL A h
  | vecFloatBinOpTrap h => exact fwd_vecFloatBinOpTrap T hr V TyL A h
  | vecIntTernOp sh op a b c => exact fwd_vecIntTernOp T hr V TyL A sh op a b c
  | vecFloatTernOp h => exact fwd_vecFloatTernOp T hr V TyL A h
  | vecFloatTernOpTrap h => exact fwd_vecFloatTernOpTrap T hr V TyL A h
  | vecAllTrue sh a => exact fwd_vecAllTrue T hr V TyL A sh a
  | vecIntRelOp sh op a b => exact fwd_vecIntRelOp T hr V TyL A sh op a b
  | vecFloatRelOp sh op a b => exact fwd_vecFloatRelOp T hr V TyL A sh op a b
  | vecShiftOp sh op a n => exact fwd_vecShiftOp T hr V TyL A sh op a n
  | vecBitmask sh a => exact fwd_vecBitmask T hr V TyL A sh a
  | vecSwizzle a b => exact fwd_vecSwizzle T hr V TyL A a b
  | vecRelaxedSwizzle a b => exact fwd_vecRelaxedSwizzle T hr V TyL A a b
  | vecShuffle idx a b hidx => exact fwd_vecShuffle T hr V TyL A idx a b hidx
  | vecSplat sh x => exact fwd_vecSplat T hr V TyL A sh x
  | vecExtractLane sh sx i a hi => exact fwd_vecExtractLane T hr V TyL A Fy sh sx i a hi
  | vecReplaceLane sh i a x hi => exact fwd_vecReplaceLane T hr V TyL A sh i a x hi
  | vecExtUnOp h => exact fwd_vecExtUnOp T hr V TyL A h
  | vecExtBinOp h => exact fwd_vecExtBinOp T hr V TyL A h
  | vecExtTernOp h => exact fwd_vecExtTernOp T hr V TyL A h
  | vecNarrow h => exact fwd_vecNarrow T hr V TyL A h
  | vecConvert h => exact fwd_vecConvert T hr V TyL A h

/-- `Forward.vector` in `simEnv B`: the rule provenance is discharged. -/
theorem simEnv_fwd_vector (B : Builtins) (T : TypingFacts (simEnv B) hn)
    (Ty : VecTyping (simEnv B)) (A : VecAgree (simEnv B) P) (Fy : FloatTyping (simEnv B))
    {s : Store H} {f : Frame} {is is' : List Admin} (h : VectorStep P is is') :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  fwd_vector T (hasStepRules_simEnv B).pure (hasVectorRules_simEnv B) Ty A Fy h

end Silmaril.Wasm.SpecTec.Sim.Vec
