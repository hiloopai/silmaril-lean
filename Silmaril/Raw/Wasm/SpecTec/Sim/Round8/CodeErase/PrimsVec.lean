module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.Prims

/-!
# Round 8 (copy of round 7 for `CODE` fields), the whole-evaluator erasure: the vector primitives are strict (unrefined)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

`oks_vecOpCall`: `Round5.Simd.vecOpCall` answers only at arguments that are images of its
encodings (`decodeArgs`), which are export-free, and answers export-free values. Walked like
`Round7.Determ.ok_vecOpCall`.
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

/-! ## The vector primitives -/

section
open Silmaril.Wasm
open Round5.Simd

theorem ncB_pctV (n : Nat) : ncB (pctV n) = true := rfl

theorem valsNx_of_decodeArgs {α : Type} {enc : α → List ArgV} (henc : ∀ p, ValsNx (enc p))
    {ws : List ArgV} {p : α} (h : decodeArgs enc ws = some p) : ValsNx ws := by
  unfold decodeArgs at h
  split at h
  · rename_i hx
    obtain ⟨q, hq⟩ := hx
    rw [← hq]
    exact henc q
  · cases h

theorem oks_decMap {α : Type} {enc : α → List ArgV} (henc : ∀ p, ValsNx (enc p)) {f : α → Value}
    (hf : ∀ p, ncB (f p) = true) (ws : List ArgV) : OKS ws ((decodeArgs enc ws).map f) := by
  refine ⟨fun v hv => ?_⟩
  cases hd : decodeArgs enc ws with
  | none => rw [hd] at hv; cases hv
  | some p =>
    rw [hd] at hv
    cases hv
    exact ⟨hf p, valsNx_of_decodeArgs henc hd⟩

theorem oks_decBind {α : Type} {enc : α → List ArgV} (henc : ∀ p, ValsNx (enc p))
    {f : α → Option Value} (hf : ∀ p v, f p = some v → ncB v = true) (ws : List ArgV) :
    OKS ws ((decodeArgs enc ws).bind f) := by
  refine ⟨fun v hv => ?_⟩
  cases hd : decodeArgs enc ws with
  | none => rw [hd] at hv; cases hv
  | some p =>
    rw [hd] at hv
    exact ⟨hf p v hv, valsNx_of_decodeArgs henc hd⟩

theorem oks_orElse {ws : List ArgV} {a b : Option Value} (ha : OKS ws a) (hb : OKS ws b) :
    OKS ws (a <|> b) := by
  refine ⟨fun v hv => ?_⟩
  cases a with
  | none => exact hb.ok v hv
  | some w => exact ha.ok v hv

theorem ncB_list_map {α : Type} (l : List α) {f : α → Value} (hf : ∀ a, ncB (f a) = true) :
    ncB (.list (l.map f)) = true := by
  simp only [ncB_list, ncBs_map, List.all_eq_true]
  exact fun a _ => hf a

theorem ncB_vecsOf (R : Numerics.V128 → Prop) : ncB (.list (vecsOf R)) = true := by
  unfold vecsOf
  exact ncB_list_map _ fun _ => rfl

theorem someVec_nx {R : Numerics.V128 → Prop} {v : Value} (h : someVec R = some v) : ncB v = true := by
  unfold someVec at h
  split at h
  · cases h; rfl
  · cases h

theorem ncB_vecV1 (a : Numerics.V128) : ncB (.list [Vec.vecV a]) = true := rfl

theorem valsNx_enc :
    (∀ p, ValsNx (encIntUnOp p)) ∧ (∀ p, ValsNx (encFloatUnOp p)) ∧
    (∀ p, ValsNx (encIntBinOp p)) ∧ (∀ p, ValsNx (encFloatBinOp p)) ∧
    (∀ p, ValsNx (encIntTernOp p)) ∧ (∀ p, ValsNx (encFloatTernOp p)) ∧
    (∀ p, ValsNx (encIntRelOp p)) ∧ (∀ p, ValsNx (encFloatRelOp p)) ∧
    (∀ p, ValsNx (encShiftOp p)) ∧ (∀ p, ValsNx (encBitmask p)) ∧
    (∀ p, ValsNx (encSwizzle p)) ∧ (∀ p, ValsNx (encShuffle p)) ∧
    (∀ p, ValsNx (encExtUnOp p)) ∧ (∀ p, ValsNx (encExtBinOp p)) ∧
    (∀ p, ValsNx (encExtTernOp p)) ∧ (∀ p, ValsNx (encNarrow p)) ∧
    (∀ p, ValsNx (encConvert p)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro p <;>
    simp [encIntUnOp, encFloatUnOp, encIntBinOp, encFloatBinOp, encIntTernOp, encFloatTernOp,
      encIntRelOp, encFloatRelOp, encShiftOp, encBitmask, encSwizzle, encShuffle, encExtUnOp,
      encExtBinOp, encExtTernOp, encNarrow, encConvert, Vec.bshapeV, Vec.laneIdxV, ncB_pctV]


/-- Every value argument of a vector encoding is export-free. -/
macro "xs_enc" : tactic => `(tactic| (intro _ <;>
  simp [encIntUnOp, encFloatUnOp, encIntBinOp, encFloatBinOp, encIntTernOp, encFloatTernOp,
    encIntRelOp, encFloatRelOp, encShiftOp, encBitmask, encSwizzle, encShuffle, encExtUnOp,
    encExtBinOp, encExtTernOp, encNarrow, encConvert, Vec.bshapeV, Vec.laneIdxV, ncB_pctV]))

section
attribute [local irreducible] vecsOf decodeArgs

theorem oks_vecOpCall (P : Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKS ws (vecOpCall P x ws) := by
  unfold vecOpCall
  delta vecOpCall.match_1
  repeat' (first
      | exact oks_none
      | (apply oks_dite <;> intro _)
      | (refine oks_cast (by assumption) ?_))
  all_goals beta_reduce
  all_goals repeat' (first
    | (apply oks_orElse)
    | (apply oks_decMap (by xs_enc); intro _; first | rfl | exact ncB_vecsOf _)
    | (apply oks_decBind (by xs_enc); intro _ _ h
       first
        | (split at h
           · cases h; rfl
           · cases h)
        | exact someVec_nx h))
end

end

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
