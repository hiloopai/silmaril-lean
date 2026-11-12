module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track simdty: definitions

Track simdty (pass 3) takes the SIMD typing leaves of `Round5.Int2.Open2`: `simd`
(`Pos.SimdTyping`) and `vector` (`Int.VectorFwd`). Both turn out to rest on statements that are
false as written (`Round5.SimdTy.not_simdTyping`, `Round5.SimdTy.not_vecTyping`):

* The evaluator selects a type-family instance by matching its patterns in order, and its
  `matchExp` does not test a nested `subE` (only a top-level `subE` argument pattern is tested,
  `Sem.argSubOk`). The operator families `vunop_`, `vbinop_`, `vternop_`, `vrelop_` and
  `vcvtop__` list an instance for integer shapes (`%X%(Jnn <: lanetype, M)`) before the one for
  float shapes, so the integer instance types the float operators too. A float operator is then
  typed only when the integer instance has a case of the same name and payload type.
  `FloatMissel` lists the Core instructions this leaves untyped; `f32x4.sqrt` is one.

This header states, additively, the restriction that removes them:

* `FloatMissel i`: `i` is a float SIMD operator that the integer instance of its family
  captures and does not type (all float `vunop_`s but `ABS`, `NEG`; all float `vbinop_`s but
  `ADD`, `SUB`, `MUL`; every float `vternop_`; all float `vrelop_`s but `EQ`, `NE`; every
  `vcvtop__` but `EXTEND`);
* `SimdTypingSel B`: `Pos.SimdTyping B` on the SIMD instructions that are not `FloatMissel`.

The earlier statements are unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation

/-- **The float SIMD operators the evaluator's instance selection leaves untyped.** -/
def FloatMissel : Instr → Bool
  | .vecFloatUnOp _ op => match op with
    | .abs | .neg => false
    | _ => true
  | .vecFloatBinOp _ op => match op with
    | .add | .sub | .mul => false
    | _ => true
  | .vecFloatTernOp .. => true
  | .vecFloatRelOp _ op => match op with
    | .eq | .ne => false
    | _ => true
  | .vecConvert _ _ op => match op with
    | .extend .. => false
    | _ => true
  | _ => false

/-- **`Pos.SimdTyping` without the `FloatMissel` instructions.** -/
def SimdTypingSel (B : Builtins) : Prop :=
  ∀ (C : Context) (i : Instr) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
    Pos.InstrSimd i = true → FloatMissel i = false →
    TypedV (simEnv B) (.varT "instr" []) (instrToV i)

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
