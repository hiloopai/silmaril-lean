module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Convert.Defs

/-!
# Round 5: family V's forward lane lemmas under `VecAgreeNC`

**Copied** verbatim from `FloatSimd/Lanes.lean` and `FloatSimd/Splat.lean` (`fwd_vecExtractLane…`,
`fwd_vecReplaceLane`, `fwd_vecSplat`, `fwd_vecAllTrue`), renamed `fwd_vec…` to `fwdN_vec…`, with
`A : VecAgree env P` replaced by `A : VecAgreeNC env P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vconstV)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (constV i32V caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Vec

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgreeNC env P) (Fy : FloatTyping env)
  {s : Store H} {f : Frame}

include T hr V Ty A Fy

/-- The unpacked case (rule 71): shapes whose lanes are 32 or 64 bits wide. -/
theorem fwdN_vecExtractLaneNum (sh : Shape) (i : LaneIdx) (a : V128) (hi : i.val < sh.lanes)
    (hw : 32 ≤ sh.laneWidth) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane sh none i)]⟩
      ⟨s, f, [(Val.num ⟨sh.unpacked, vecExtractLane sh none i.val a⟩).toAdmin]⟩ := by
  obtain ⟨ls, ha, hk⟩ := A.extractNum sh a i.val hi hw
  rcases sh with sh | sh <;> cases sh
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i32)) (Ty.dim (.int .i32x4)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i32, _⟩)
      ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i64)) (Ty.dim (.int .i64x2)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i64, _⟩)
      ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f32)) (Ty.dim (.float .f32x4)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f32, _⟩) ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f64)) (Ty.dim (.float .f64x2)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f64, _⟩) ha hk)

omit Fy in
/-- The packed case (rule 72): integer shapes with 8- or 16-bit lanes. -/
theorem fwdN_vecExtractLanePack (sh : IntShape) (sx : Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes) (hw : sh.laneWidth < 32) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane (.int sh) (some sx) i)]⟩
      ⟨s, f, [(Val.num ⟨(Shape.int sh).unpacked,
        vecExtractLane (.int sh) (some sx) i.val a⟩).toAdmin]⟩ := by
  obtain ⟨ls, l, n, ha, hk, hn', he⟩ := A.extractPack sh sx a i.val hi hw
  cases sh
  · exact fwd_of_spure T hr (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i8x16)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact fwd_of_spure T hr (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i16x8)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- `VectorStep.vecExtractLane`, forward: rule 71 or 72, by the typing of the instruction. -/
theorem fwdN_vecExtractLane (sh : Shape) (sx : Option Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane sh sx i)]⟩
      ⟨s, f, [(Val.num ⟨sh.unpacked, vecExtractLane sh sx i.val a⟩).toAdmin]⟩ := by
  intro hc hc'
  have hty : InstrTyped env (.vecExtractLane sh sx i) := typed_last2 T (typed_code T hc)
  have hsx : sx = none ↔ 32 ≤ sh.laneWidth := Ty.extractSx sh sx i hty
  cases sx with
  | none => exact fwdN_vecExtractLaneNum T hr V Ty A Fy sh i a hi (hsx.1 rfl) hc hc'
  | some x =>
      have hw : ¬ 32 ≤ sh.laneWidth := fun h => by cases hsx.2 h
      cases sh with
      | int sh =>
          exact fwdN_vecExtractLanePack T hr V Ty A sh x i a hi (by
            simp only [Shape.laneWidth] at hw; omega) hc hc'
      | float sh => cases sh <;> exact absurd (by decide) hw

end

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgreeNC env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecReplaceLane`, forward (`Step_pure/vreplace_lane`). -/
theorem fwdN_vecReplaceLane (sh : Shape) (i : LaneIdx) (a : V128) (x : BitVec sh.unpacked.width)
    (hi : i.val < sh.lanes) :
    FwdP env hn ⟨s, f, [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)]⟩ ⟨s, f, [vconst (vecReplaceLane sh i.val a x)]⟩ := by
  obtain ⟨ls, l, u, hu, hl, hp, hs, hinv⟩ := A.replaceLane sh a i.val x hi
  have hl' : Applies env "lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes])),
      .val (vecV a)] (.list ls) := shapeV_eq sh ▸ hl
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val u] (vecV (vecReplaceLane sh i.val a x)) := shapeV_eq sh ▸ hinv
  have hsp : SPure env [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
        pctV i.val])] [vconstV (vecV (vecReplaceLane sh i.val a x))] :=
    spure_vreplaceLane V.vreplaceLane (Ty.vec a) (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh)
      (Ty.laneidx i) (Ty.vec _) hu hl' hp hs hinv'
  have e₁ : adminsToV [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)] =
      [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
          pctV i.val])] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact fwd_of_spure T hr (e₁ ▸ hsp)

end

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgreeNC env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecSplat`, forward (`Step_pure/vsplat`). -/
theorem fwdN_vecSplat (sh : Shape) (x : BitVec sh.unpacked.width) :
    FwdP env hn ⟨s, f, [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]⟩
      ⟨s, f, [vconst (vecSplat sh x)]⟩ := by
  obtain ⟨l, hu, hp, hinv⟩ := A.splat sh x
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val (.list (List.replicate sh.lanes l))] (vecV (vecSplat sh x)) :=
    shapeV_eq sh ▸ hinv
  have hsp : SPure env [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))]
      [vconstV (vecV (vecSplat sh x))] :=
    spure_vsplat V.vsplat (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh) (Ty.vec _) hu hp hinv'
  have e₁ : adminsToV [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)] =
      [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact fwd_of_spure T hr (e₁ ▸ hsp)

/-- `VectorStep.vecAllTrue`, forward (`Step_pure/vtestop`). -/
theorem fwdN_vecAllTrue (sh : IntShape) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecAllTrue sh)]⟩
      ⟨s, f, [constI32 (vecAllTrue sh a)]⟩ := by
  obtain ⟨ls, jsz, bs, hl, hjs, hz, hp⟩ := A.allTrue sh a
  exact fwd_of_spure T hr (spure_vtestop V.vtestop (Ty.vec a) (Ty.jnn sh) (Ty.dim (.int sh))
    (Ty.i32 _) (Ty.lanes sh a ls hl) hl hjs hz hp)

end

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
