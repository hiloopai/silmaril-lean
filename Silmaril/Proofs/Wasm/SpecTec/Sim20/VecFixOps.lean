module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixUn1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixUn2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixUn3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixUn4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBin1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBin2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBin3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBin4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixRel1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixRel2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixRel3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixRel4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixExtract
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixNeed1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixNeed2

/-!
# The vector errata: the instructions they repair are typed

* **`typedA_floatVec20V`**: every float `VUNOP`, `VBINOP` and `VRELOP` (all operators, both
  float shapes) is an `admininstr` of `simEnv20V B`, for every `B`. Without the erratum the
  fourteen float-only ones are not (`VecRefute.not_typedA_floatOnly20T`).
* **`typedA_extract20V`** (in `VecFixExtract`): so is every valid `VEXTRACT_LANE`.
  **`not_typedA_extract20T`**: without the erratum none is, at lane 0, for every valid shape and
  sign.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

variable {B : Builtins}

/-- The float vector operators: `VUNOP`, `VBINOP`, `VRELOP` at `f32x4` or `f64x2`. -/
def FloatVec : V2.Instr → Prop
  | .vecFloatUnOp _ _ | .vecFloatBinOp _ _ | .vecFloatRelOp _ _ => True
  | _ => False

/-- `hasTyp` accepts every float vector operator at fuel 200. -/
theorem hasTyp_floatVec20V {i : V2.Instr} (h : FloatVec i) :
    hasTyp 200 (simEnv20V B) VarEnv.empty (.varT "admininstr" []) (instrToV i) = .ok true := by
  rcases i <;> simp only [FloatVec] at h
  case vecFloatUnOp s op =>
    rcases s <;> rcases op
    all_goals first
      | (refine hasTyp_floatUn20V_1 _ ?_; decide) | (refine hasTyp_floatUn20V_2 _ ?_; decide)
      | (refine hasTyp_floatUn20V_3 _ ?_; decide) | (refine hasTyp_floatUn20V_4 _ ?_; decide)
  case vecFloatBinOp s op =>
    rcases s <;> rcases op
    all_goals first
      | (refine hasTyp_floatBin20V_1 _ ?_; decide) | (refine hasTyp_floatBin20V_2 _ ?_; decide)
      | (refine hasTyp_floatBin20V_3 _ ?_; decide) | (refine hasTyp_floatBin20V_4 _ ?_; decide)
  case vecFloatRelOp s op =>
    rcases s <;> rcases op
    all_goals first
      | (refine hasTyp_floatRel20V_1 _ ?_; decide) | (refine hasTyp_floatRel20V_2 _ ?_; decide)
      | (refine hasTyp_floatRel20V_3 _ ?_; decide) | (refine hasTyp_floatRel20V_4 _ ?_; decide)

/-- **Every float vector operator is an `admininstr` of `simEnv20V B`.** -/
theorem typedA_floatVec20V {i : V2.Instr} (h : FloatVec i) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i) :=
  typedV_of_hasTyp_true (hasTyp_floatVec20V h)

/-- The float-only operators of `VecRefute` are float vector operators. -/
theorem floatVec_of_floatOnly {i : V2.Instr} (h : VecRefute.FloatOnly i) : FloatVec i := by
  rcases i <;> simp only [VecRefute.FloatOnly] at h <;> trivial

/-- **Without the erratum, no valid `VEXTRACT_LANE` at lane 0 is an `admininstr` of
`simEnv20T B`.** -/
theorem not_typedA_extract20T (s : Shape) (sx : Option Signedness)
    (h : (V2.Instr.vecExtractLane s sx 0).immediatesValid = true) :
    ¬ TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.vecExtractLane s sx 0)) := by
  intro ht
  rcases s with s | s
  · exact VecRefute.not_hasTyp_of_false (hasTyp_extract20T_1 s sx h) (ht _ ⟨rfl, rfl, rfl⟩)
  · exact VecRefute.not_hasTyp_of_false (hasTyp_extract20T_2 s sx h) (ht _ ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim20.VecFix
