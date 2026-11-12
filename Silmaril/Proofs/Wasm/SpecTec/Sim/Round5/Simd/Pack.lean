module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Lanes

/-!
# Round 5: `vsplat` and `vreplace_lane` agree at the concrete builtins

`$lunpack(Lnn)` and `$lpacknum_(Lnn, c)` by their clauses (for every `B` with `FloatB`, which
`$wrap__` needs at the packed lanes), and `$inv_lanes_` through `Round5.Simd.invLanesCall`:

* `applies_lunpack`: `$lunpack(Lnn)` is the unpacked number type of the shape;
* `applies_lpacknum`: `$lpacknum_(Lnn, c)` is the lane `c` wraps to;
* `splat`, `replaceLane`: the `VecAgree` fields of `vsplat` and `vreplace_lane`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil bvV natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {B : Builtins}

/-! ## The clauses -/

/-- The pattern `numtype <: lanetype`. -/
abbrev numtypePatL : Exp := .subE (.varE "numtype") (.varT "numtype" []) (.varT "lanetype" [])

/-- The pattern `packtype <: lanetype`. -/
abbrev packtypePatL : Exp := .subE (.varE "packtype") (.varT "packtype" []) (.varT "lanetype" [])

/-- The body of `$lpacknum_`'s second clause. -/
abbrev lpackBody : Exp :=
  .callE "wrap__" [.expA (.callE "size" [.expA (.callE "lunpack" [.expA packtypePatL])]),
    .expA (.callE "psize" [.expA (.varE "packtype")]), .expA (.varE "c")]

set_option maxRecDepth 100000 in
theorem findDef_lpacknum (B : Builtins) : ∃ ps t q₁ q₂, (simEnv B).findDef? "lpacknum_" =
    some (ps, t, [.defD q₁ [.expA numtypePatL, .expA (.varE "c")] (.varE "c") [],
      .defD q₂ [.expA packtypePatL, .expA (.varE "c")] lpackBody []]) := ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_size' (B : Builtins) : ∃ ps t, (simEnv B).findDef? "size" = some (ps, t,
    [.defD [] [.expA (.caseE "I32" (.tupE []))] (.numE (.natN 32)) [],
     .defD [] [.expA (.caseE "I64" (.tupE []))] (.numE (.natN 64)) [],
     .defD [] [.expA (.caseE "F32" (.tupE []))] (.numE (.natN 32)) [],
     .defD [] [.expA (.caseE "F64" (.tupE []))] (.numE (.natN 64)) []]) := ⟨_, _, rfl⟩

/-- `$size(I32) = 32`. -/
theorem applies_size_i32 : Applies (simEnv B) "size" [.val (caseNilV "I32")] (natV 32) := by
  obtain ⟨ps, t, hd⟩ := findDef_size' B
  exact ⟨ps, t, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil) premsHold_nil RefsGC.evalExp_num')⟩

set_option maxRecDepth 100000 in
/-- `$lunpack(nt) = nt` at a number type. -/
theorem applies_lunpack_num (t : NumType) :
    Applies (simEnv B) "lunpack" [.val (Vec.numTypeV t)] (Vec.numTypeV t) := by
  obtain ⟨ps, ty, hd⟩ := R4Fwd.findDef_lunpack B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
    (evalExp_var (by simp)))⟩
  rcases t with t | t <;> cases t <;> rfl

/-- **`$lunpack(Lnn)`**: the unpacked number type of the shape. -/
theorem applies_lunpack (sh : Shape) :
    Applies (simEnv B) "lunpack" [.val (Vec.laneTypeV sh)] (Vec.numTypeV sh.unpacked) := by
  rcases sh with s | s <;> cases s
  · exact R4Fwd.applies_lunpack_pack .i8
  · exact R4Fwd.applies_lunpack_pack .i16
  · exact applies_lunpack_num (.int .i32)
  · exact applies_lunpack_num (.int .i64)
  · exact applies_lunpack_num (.float .f32)
  · exact applies_lunpack_num (.float .f64)

set_option maxRecDepth 100000 in
/-- `$lpacknum_(nt, c) = c` at a number type. -/
theorem applies_lpacknum_num (t : NumType) (c : Value) :
    Applies (simEnv B) "lpacknum_" [.val (Vec.numTypeV t), .val c] c := by
  obtain ⟨ps, ty, q₁, q₂, hd⟩ := findDef_lpacknum B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) (matchArgs_cons
      (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)) premsHold_nil
    (evalExp_var (by simp)))⟩
  rcases t with t | t <;> cases t <;> rfl

set_option maxRecDepth 100000 in
/-- `$lpacknum_(pt, c) = $wrap__(32, |pt|, c)` at a packed type. -/
theorem applies_lpacknum_pack {P : Profile} (hF : Floats.FloatB P B) (p : PackType)
    (b : BitVec 32) :
    Applies (simEnv B) "lpacknum_" [.val (tyV (Ty.pack p : CStorageType)), .val (bvV b)]
      (bvV (b.setWidth p.width)) := by
  obtain ⟨ps, ty, q₁, q₂, hd⟩ := findDef_lpacknum B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
      (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) (matchArgs_cons
        (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)) premsHold_nil ?_))⟩
  · cases p <;> rfl
  · cases p <;> rfl
  · have hl : EvalExp (simEnv B) ((VarEnv.empty.bindVal "packtype"
        (tyV (Ty.pack p : CStorageType))).bindVal "c" (bvV b))
        (.callE "lunpack" [.expA packtypePatL]) (caseNilV "I32") :=
      Vec.evalExp_call rfl (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var (by simp)))
        evalArgs_nil) (R4Fwd.applies_lunpack_pack p)
    exact Vec.evalExp_call rfl (evalArgs_cons (Vec.evalExp_call rfl (evalArgs_cons hl evalArgs_nil)
      applies_size_i32) (evalArgs_cons (Vec.evalExp_call rfl (evalArgs_cons
        (evalExp_var (by simp)) evalArgs_nil) (R4Fwd.applies_psize p))
      (evalArgs_cons (evalExp_var (by simp)) evalArgs_nil))) (R4Fwd.applies_wrap hF p.width b)

/-- `$lpacknum_(nt, c) = c` at an integer number type, with the lane written as a wrap. -/
theorem applies_lpacknum_int (t : NumType) (w : Nat) (x : BitVec w) :
    Applies (simEnv B) "lpacknum_" [.val (Vec.numTypeV t), .val (pctV x.toNat)]
      (pctV (x.setWidth w).toNat) := by
  rw [BitVec.setWidth_eq]
  exact applies_lpacknum_num _ _

/-- `$lpacknum_(nt, c) = c` at a float number type, with the lane written as a wrap. -/
theorem applies_lpacknum_float (t : FloatType) (x : BitVec t.width) :
    Applies (simEnv B) "lpacknum_" [.val (Vec.numTypeV (.float t)), .val (floatV t x)]
      (floatV t (x.setWidth t.width)) := by
  rw [BitVec.setWidth_eq]
  exact applies_lpacknum_num _ _

/-- **`$lpacknum_(Lnn, c)`**: the lane the unpacked numeral `c` wraps to. -/
theorem applies_lpacknum {P : Profile} (hF : Floats.FloatB P B) (sh : Shape)
    (x : BitVec sh.unpacked.width) :
    Applies (simEnv B) "lpacknum_" [.val (Vec.laneTypeV sh), .val (numV ⟨sh.unpacked, x⟩)]
      (laneV sh (x.setWidth sh.laneWidth)) := by
  rcases sh with s | s <;> cases s
  · exact applies_lpacknum_pack hF .i8 x
  · exact applies_lpacknum_pack hF .i16 x
  · exact applies_lpacknum_int (.int .i32) 32 x
  · exact applies_lpacknum_int (.int .i64) 64 x
  · exact applies_lpacknum_float .f32 x
  · exact applies_lpacknum_float .f64 x

/-! ## `vsplat` and `vreplace_lane` -/

/-- The lanes of a splat. -/
theorem lanesV_vecSplat (sh : Shape) (x : BitVec sh.unpacked.width) :
    lanesV sh (vecSplat sh x) = List.replicate sh.lanes (laneV sh (x.setWidth sh.laneWidth)) := by
  simp only [lanesV, vecSplat, vsplat]
  rw [Shape.lanesOf_invLanes _ _ (by simp), List.map_replicate]

/-- The lanes of a lane replacement. -/
theorem lanesV_vecReplaceLane (sh : Shape) (k : Nat) (a : V128)
    (x : BitVec sh.unpacked.width) :
    lanesV sh (vecReplaceLane sh k a x) = (lanesV sh a).set k (laneV sh (x.setWidth sh.laneWidth)) := by
  simp only [lanesV, vecReplaceLane, vreplaceLane]
  rw [Shape.lanesOf_invLanes _ _ (by simp [Shape.lanesOf]), List.map_set]

/-- **`VecAgree.splat`** at the concrete builtins. -/
theorem splat (P : Profile) (hn : H → String) (host : HostSemantics H) :
    ∀ (sh : Shape) (x : BitVec sh.unpacked.width), ∃ l,
      Applies (simEnv (BI P hn host)) "lunpack" [.val (Vec.laneTypeV sh)]
        (Vec.numTypeV sh.unpacked) ∧
      Applies (simEnv (BI P hn host)) "lpacknum_"
        [.val (Vec.laneTypeV sh), .val (numV ⟨sh.unpacked, x⟩)] l ∧
      Applies (simEnv (BI P hn host)) "inv_lanes_"
        [.val (Vec.shapeV sh), .val (.list (List.replicate sh.lanes l))]
        (Vec.vecV (vecSplat sh x)) := by
  intro sh x
  refine ⟨laneV sh (x.setWidth sh.laneWidth), applies_lunpack sh,
    applies_lpacknum (Prims.floatB_builtins hn host) sh x, ?_⟩
  rw [← lanesV_vecSplat]
  exact applies_invLanes P hn host sh _

/-- **`VecAgree.replaceLane`** at the concrete builtins. -/
theorem replaceLane (P : Profile) (hn : H → String) (host : HostSemantics H) :
    ∀ (sh : Shape) (a : V128) (k : Nat) (x : BitVec sh.unpacked.width), k < sh.lanes →
      ∃ ls l u, Applies (simEnv (BI P hn host)) "lunpack" [.val (Vec.laneTypeV sh)]
          (Vec.numTypeV sh.unpacked) ∧
        Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.shapeV sh), .val (Vec.vecV a)]
          (.list ls) ∧
        Applies (simEnv (BI P hn host)) "lpacknum_"
          [.val (Vec.laneTypeV sh), .val (numV ⟨sh.unpacked, x⟩)] l ∧
        (Value.list ls).setIdx k l = some u ∧
        Applies (simEnv (BI P hn host)) "inv_lanes_" [.val (Vec.shapeV sh), .val u]
          (Vec.vecV (vecReplaceLane sh k a x)) := by
  intro sh a k x hk
  refine ⟨lanesV sh a, laneV sh (x.setWidth sh.laneWidth),
    .list ((lanesV sh a).set k (laneV sh (x.setWidth sh.laneWidth))), applies_lunpack sh,
    applies_lanes P hn host sh a, applies_lpacknum (Prims.floatB_builtins hn host) sh x, ?_, ?_⟩
  · have : k < (lanesV sh a).length := by simpa [lanesV, Shape.lanesOf] using hk
    simp [Value.setIdx, this]
  · rw [← lanesV_vecReplaceLane]
    exact applies_invLanes P hn host sh _

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
