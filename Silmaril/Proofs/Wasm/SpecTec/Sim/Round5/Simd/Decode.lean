module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Lanes

/-!
# Round 5, track simd (pass 3): decoding the arguments of the lane-wise operators

`vecOpCall` decodes its arguments by choice (`decodeArgs`); on the image of an encoding that is
injective it recovers the encoded tuple (`decodeArgs_enc`). This module proves the encodings of
the lane-wise operators injective, and that the integer and float encodings of the dispatchers
shared by both (`$vunop_`, `$vbinop_`, `$vternop_`, `$vrelop_`) never meet.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)

/-! ## `decodeArgs`, `vecsOf`, `someVec` -/

/-- On the image of an injective encoding, `decodeArgs` recovers the encoded tuple. -/
theorem decodeArgs_enc {α : Type} {enc : α → List ArgV} (hinj : Function.Injective enc) (p : α) :
    decodeArgs enc (enc p) = some p := by
  unfold decodeArgs
  split
  · next h => exact congrArg some (hinj h.choose_spec)
  · next h => exact absurd ⟨p, rfl⟩ h

/-- Off the image of an encoding, `decodeArgs` answers nothing. -/
theorem decodeArgs_none {α : Type} {enc : α → List ArgV} {ws : List ArgV}
    (h : ∀ p, enc p ≠ ws) : decodeArgs enc ws = none := by
  unfold decodeArgs
  split
  · next hex => exact absurd hex.choose_spec (h _)
  · rfl

/-- **`vecsOf R` lists exactly the images of the patterns satisfying `R`.** -/
theorem mem_vecsOf {R : V128 → Prop} {c : Value} :
    c ∈ vecsOf R ↔ ∃ r, R r ∧ c = Vec.vecV r := by
  classical
  simp only [vecsOf, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨-, hR⟩, rfl⟩
    exact ⟨_, hR, rfl⟩
  · rintro ⟨r, hR, rfl⟩
    refine ⟨r.toNat, ⟨r.isLt, by simpa using hR⟩, by simp⟩

/-- `someVec` of a relation with exactly one solution. -/
theorem someVec_unique {R : V128 → Prop} {r : V128} (hr : R r) (hu : ∀ r', R r' → r' = r) :
    someVec R = some (Vec.vecV r) := by
  unfold someVec
  split
  · next h => rw [hu _ h.choose_spec]
  · next h => exact absurd ⟨r, hr⟩ h

/-- `someVec` of a relation with no solution. -/
theorem someVec_none {R : V128 → Prop} (h : ∀ r, ¬ R r) : someVec R = none := by
  unfold someVec
  split
  · next hex => exact absurd hex.choose_spec (h _)
  · rfl

/-- `someVec` answers only solutions. -/
theorem someVec_sound {R : V128 → Prop} {c : Value} (h : someVec R = some c) :
    ∃ r, R r ∧ c = Vec.vecV r := by
  unfold someVec at h
  split at h
  · next hex => exact ⟨_, hex.choose_spec, (Option.some.inj h).symm⟩
  · cases h

/-- `someVec` answers whenever there is a solution. -/
theorem someVec_isSome {R : V128 → Prop} (h : ∃ r, R r) : ∃ c, someVec R = some c := by
  unfold someVec
  split
  · exact ⟨_, rfl⟩
  · next hn => exact absurd h hn

/-! ## Injectivity of the operator encodings -/

/-- `ishV` is injective. -/
theorem ishV_injective : Function.Injective Vec.ishV := fun s t h =>
  by simpa [Vec.shapeV] using (shapeV_injective (a₁ := .int s) (a₂ := .int t) h)

/-- `fshV` is injective. -/
theorem fshV_injective : Function.Injective Vec.fshV := fun s t h =>
  by simpa [Vec.shapeV] using (shapeV_injective (a₁ := .float s) (a₂ := .float t) h)

/-- An integer shape image is no float shape image. -/
theorem ishV_ne_fshV (s : IntShape) (t : FloatShape) : Vec.ishV s ≠ Vec.fshV t := by
  cases s <;> cases t <;> simp [Vec.ishV, Vec.fshV, Vec.intLaneV, Vec.floatLaneV, caseNilV]

/-- `ishapeV` is injective. -/
theorem ishapeV_injective : Function.Injective Vec.ishapeV := fun s t h => by
  simp only [Vec.ishapeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at h
  exact ishV_injective h

/-- `sxV` is injective. -/
theorem sxV_injective : Function.Injective Vec.sxV := by
  intro a b h
  cases a <;> cases b <;> simp_all [Vec.sxV, caseNilV]

/-- `halfV` is injective. -/
theorem halfV_injective : Function.Injective Vec.halfV := by
  intro a b h
  cases a <;> cases b <;> simp_all [Vec.halfV, caseNilV]

/-- `i32NV` is injective. -/
theorem i32NV_injective : Function.Injective Vec.i32NV := by
  intro a b h
  simp only [Vec.i32NV, pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.num.injEq, Num.natN.injEq, and_true, true_and] at h
  exact BitVec.eq_of_toNat_eq h

/-- `laneIdxV` is injective. -/
theorem laneIdxV_injective : Function.Injective Vec.laneIdxV := by
  intro a b h
  simp only [Vec.laneIdxV, pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.num.injEq, Num.natN.injEq, and_true, true_and] at h
  exact Fin.ext h

/-- `vIntUnOpV` is injective. -/
theorem vIntUnOpV_injective : Function.Injective Vec.vIntUnOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vIntUnOpV, caseNilV]

/-- `vFloatUnOpV` is injective. -/
theorem vFloatUnOpV_injective : Function.Injective Vec.vFloatUnOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vFloatUnOpV, caseNilV]

/-- `vIntBinOpV` is injective. -/
theorem vIntBinOpV_injective : Function.Injective Vec.vIntBinOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vIntBinOpV, caseNilV, sxV_injective.eq_iff]

/-- `vFloatBinOpV` is injective. -/
theorem vFloatBinOpV_injective : Function.Injective Vec.vFloatBinOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vFloatBinOpV, caseNilV]

/-- `vFloatTernOpV` is injective. -/
theorem vFloatTernOpV_injective : Function.Injective Vec.vFloatTernOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vFloatTernOpV, caseNilV]

/-- `vIntRelOpV` is injective. -/
theorem vIntRelOpV_injective : Function.Injective Vec.vIntRelOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vIntRelOpV, caseNilV, sxV_injective.eq_iff]

/-- `vFloatRelOpV` is injective. -/
theorem vFloatRelOpV_injective : Function.Injective Vec.vFloatRelOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vFloatRelOpV, caseNilV]

/-- `vShiftOpV` is injective. -/
theorem vShiftOpV_injective : Function.Injective Vec.vShiftOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vShiftOpV, caseNilV, sxV_injective.eq_iff]

/-- `vSwizzleOpV` is injective. -/
theorem vSwizzleOpV_injective : Function.Injective Vec.vSwizzleOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vSwizzleOpV, caseNilV]

/-- `vExtBinOpV` is injective. -/
theorem vExtBinOpV_injective : Function.Injective Vec.vExtBinOpV := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vExtBinOpV, caseNilV, sxV_injective.eq_iff, halfV_injective.eq_iff]

/-- `vIntTernOpV` is injective. -/
theorem vIntTernOpV_injective : Function.Injective Vec.vIntTernOpV := by
  intro a b h
  cases a
  cases b
  simp_all [Vec.vIntTernOpV, caseNilV]

/-- `vExtUnOpV` is injective. -/
theorem vExtUnOpV_injective : Function.Injective Vec.vExtUnOpV := by
  intro a b h
  cases a
  cases b
  simp_all [Vec.vExtUnOpV, sxV_injective.eq_iff]

/-- `vExtTernOpV` is injective. -/
theorem vExtTernOpV_injective : Function.Injective Vec.vExtTernOpV := by
  intro a b h
  cases a
  cases b
  simp_all [Vec.vExtTernOpV, caseNilV]


/-- `vConvertOpV` is injective. -/
theorem vConvertOpV_injective : Function.Injective Vec.vConvertOpV := by
  intro a b h
  rcases a with ⟨_ | _, sa⟩ | ⟨_ | _ | _, sa⟩ | ⟨sa, _ | _⟩ | ⟨sa, _ | _⟩ | _ | _ <;>
  rcases b with ⟨_ | _, sb⟩ | ⟨_ | _ | _, sb⟩ | ⟨sb, _ | _⟩ | ⟨sb, _ | _⟩ | _ | _ <;>
    simp_all [Vec.vConvertOpV, Vec.halfV, caseNilV, sxV_injective.eq_iff]

/-- `shapeV` and `vConvertOpV` give an injective `$vcvtop__` encoding. -/
theorem encConvert_injective : Function.Injective encConvert := by
  intro p q h
  simp only [encConvert, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [shapeV_injective.eq_iff, vConvertOpV_injective.eq_iff, vecV_injective.eq_iff,
    Prod.ext_iff]

/-! ## Injectivity of the argument encodings -/

/-- `encIntUnOp` is injective. -/
theorem encIntUnOp_injective : Function.Injective encIntUnOp := by
  intro p q h
  simp only [encIntUnOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishV_injective.eq_iff, vIntUnOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encFloatUnOp` is injective. -/
theorem encFloatUnOp_injective : Function.Injective encFloatUnOp := by
  intro p q h
  simp only [encFloatUnOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [fshV_injective.eq_iff, vFloatUnOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encIntBinOp` is injective. -/
theorem encIntBinOp_injective : Function.Injective encIntBinOp := by
  intro p q h
  simp only [encIntBinOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishV_injective.eq_iff, vIntBinOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encFloatBinOp` is injective. -/
theorem encFloatBinOp_injective : Function.Injective encFloatBinOp := by
  intro p q h
  simp only [encFloatBinOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [fshV_injective.eq_iff, vFloatBinOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encIntTernOp` is injective. -/
theorem encIntTernOp_injective : Function.Injective encIntTernOp := by
  intro p q h
  simp only [encIntTernOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encFloatTernOp` is injective. -/
theorem encFloatTernOp_injective : Function.Injective encFloatTernOp := by
  intro p q h
  simp only [encFloatTernOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [fshV_injective.eq_iff, vFloatTernOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encIntRelOp` is injective. -/
theorem encIntRelOp_injective : Function.Injective encIntRelOp := by
  intro p q h
  simp only [encIntRelOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishV_injective.eq_iff, vIntRelOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encFloatRelOp` is injective. -/
theorem encFloatRelOp_injective : Function.Injective encFloatRelOp := by
  intro p q h
  simp only [encFloatRelOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [fshV_injective.eq_iff, vFloatRelOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encShiftOp` is injective. -/
theorem encShiftOp_injective : Function.Injective encShiftOp := by
  intro p q h
  simp only [encShiftOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishapeV_injective.eq_iff, vShiftOpV_injective.eq_iff, vecV_injective.eq_iff, i32NV_injective.eq_iff, Prod.ext_iff]

/-- `encBitmask` is injective. -/
theorem encBitmask_injective : Function.Injective encBitmask := by
  intro p q h
  simp only [encBitmask, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishapeV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encSwizzle` is injective. -/
theorem encSwizzle_injective : Function.Injective encSwizzle := by
  intro p q h
  simp only [encSwizzle, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [vSwizzleOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encShuffle` is injective. -/
theorem encShuffle_injective : Function.Injective encShuffle := by
  intro p q h
  simp only [encShuffle, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [vecV_injective.eq_iff, (List.map_injective_iff.2 laneIdxV_injective).eq_iff, Prod.ext_iff]

/-- `encExtUnOp` is injective. -/
theorem encExtUnOp_injective : Function.Injective encExtUnOp := by
  intro p q h
  simp only [encExtUnOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishapeV_injective.eq_iff, vExtUnOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encExtBinOp` is injective. -/
theorem encExtBinOp_injective : Function.Injective encExtBinOp := by
  intro p q h
  simp only [encExtBinOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishapeV_injective.eq_iff, vExtBinOpV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encExtTernOp` is injective. -/
theorem encExtTernOp_injective : Function.Injective encExtTernOp := by
  intro p q h
  simp only [encExtTernOp, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishapeV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- `encNarrow` is injective. -/
theorem encNarrow_injective : Function.Injective encNarrow := by
  intro p q h
  simp only [encNarrow, List.cons.injEq, ArgV.val.injEq, and_true] at h
  simp_all [ishV_injective.eq_iff, sxV_injective.eq_iff, vecV_injective.eq_iff, Prod.ext_iff]

/-- Integer and float arguments of `$vunop_` never meet. -/
theorem encIntUnOp_ne (p q) : encIntUnOp p ≠ encFloatUnOp q := by
  simp [encIntUnOp, encFloatUnOp, ishV_ne_fshV]
/-- Integer and float arguments of `$vbinop_` never meet. -/
theorem encIntBinOp_ne (p q) : encIntBinOp p ≠ encFloatBinOp q := by
  simp [encIntBinOp, encFloatBinOp, ishV_ne_fshV]
/-- Integer and float arguments of `$vternop_` never meet. -/
theorem encIntTernOp_ne (p q) : encIntTernOp p ≠ encFloatTernOp q := by
  simp [encIntTernOp, encFloatTernOp, ishV_ne_fshV]
/-- Integer and float arguments of `$vrelop_` never meet. -/
theorem encIntRelOp_ne (p q) : encIntRelOp p ≠ encFloatRelOp q := by
  simp [encIntRelOp, encFloatRelOp, ishV_ne_fshV]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
