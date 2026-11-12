module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Defs

/-!
# Round 5: the shape and lane types

The IL types the SIMD instructions carry besides their operators, in every `simEnv B`:

* `typedV_lanetype`, `typedV_jnn`, `typedV_lnn`: the lane types of the shapes;
* `typedV_dim`, `typedV_M`: the lane counts (`dim`'s premise `i ∈ {1, 2, 4, 8, 16}`);
* `applies_size`, `applies_lsize'`, `applies_lanetype`: `$size`, `$lsize`, `$lanetype` by their
  clauses, at every lane type;
* `typedV_shape`: every shape (`shape`'s premise `$lsize(lanetype) * dim = 128`);
* `typedV_ishape`, `typedV_bshape`: the integer shapes, and `I8 X 16` (`ishape`'s quantifier
  `Jnn` is defined by its premise `$lanetype(shape) = Jnn`);
* `typedV_laneidx`, `typedV_half`, `typedV_zero`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Closed enumerations -/

/-- A case of a closed variant, with premises, holds when its payload and premises do. -/
theorem typedV_closedCaseP {x : IL.Id} {cs : List TypCase} {op : MixopS} {t : Typ}
    {prems : List Prem} {w : Value}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (hf : IntNumeric.findCase cs op = some (t, prems)) (hw : HasTyp (simEnv B) VarEnv.empty t w)
    (hp : PremsOk (simEnv B) (caseScope VarEnv.empty t w) prems)
    (hq : IntNumeric.quantFreeAt cs op = true := by rfl) :
    TypedV (simEnv B) (.varT x []) (.case op w) :=
  fun _ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd
    evalArgs_nil matchArgs_nil (IntNumeric.hasTypCase_of_findCase hf hw hp hq)

set_option maxRecDepth 100000 in
theorem typedV_lanetype (sh : Shape) :
    TypedV (simEnv B) (.varT "lanetype" []) (Vec.laneTypeV sh) := fun _ hρ => by
  rcases sh with s | s <;> cases s <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_lnn (sh : Shape) : TypedV (simEnv B) (.varT "Lnn" []) (Vec.laneTypeV sh) :=
  fun _ hρ => by
    rcases sh with s | s <;> cases s <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_jnn (s : IntShape) : TypedV (simEnv B) (.varT "Jnn" []) (Vec.intLaneV s) :=
  fun _ hρ => by cases s <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_half (h : Half) : TypedV (simEnv B) (.varT "half" []) (Vec.halfV h) :=
  fun _ hρ => by cases h <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_zero : TypedV (simEnv B) (.varT "zero" []) (caseNilV "ZERO") :=
  fun _ hρ => IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem findTyp_u8 : (simEnv B).findTyp? "u8" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 8))]))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_laneidx : (simEnv B).findTyp? "laneidx" =
    some ([], [.instD [] [] (.aliasT (.varT "u8" []))]) := rfl

/-- Every lane index is a `laneidx` (`u8`). -/
theorem typedV_laneidx (i : LaneIdx) : TypedV (simEnv B) (.varT "laneidx" []) (Vec.laneIdxV i) :=
  Typing.typedV_alias findTyp_laneidx fun ρ hρ =>
    hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_u8
      evalArgs_nil (hasTypInsts_head matchArgs_nil
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num i.isLt)))

/-! ## `dim` and `M` -/

/-- The premise of `dim`'s case. -/
noncomputable def dimPrem : Exp :=
  .binE .orOp .boolT (.binE .orOp .boolT (.binE .orOp .boolT (.binE .orOp .boolT
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 1)))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 2))))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 4))))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 8))))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 16)))

set_option maxRecDepth 100000 in
theorem findTyp_dim : (simEnv B).findTyp? "dim" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr dimPrem]])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_M : (simEnv B).findTyp? "M" =
    some ([], [.instD [] [] (.aliasT (.varT "dim" []))]) := rfl

/-- `i = k`, for a numeral `i` bound in the scope. -/
theorem evalExp_eqLit {ρ : VarEnv} {n k : Nat} (h : ρ.findVal? "i" = some (.num (.natN n))) :
    EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN k)))
      (.bool (decide (n = k))) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_var h, evalExp_num, by
    by_cases hk : n = k <;> simp [cmpValues, hk]⟩

/-- `dim`'s premise at `n`. -/
theorem evalExp_dimPrem {ρ : VarEnv} {n : Nat} (h : ρ.findVal? "i" = some (.num (.natN n))) :
    EvalExp (simEnv B) ρ dimPrem
      (.bool (decide (((((n = 1) ∨ n = 2) ∨ n = 4) ∨ n = 8) ∨ n = 16))) :=
  evalExp_or (evalExp_or (evalExp_or (evalExp_or (evalExp_eqLit h) (evalExp_eqLit h))
    (evalExp_eqLit h)) (evalExp_eqLit h)) (evalExp_eqLit h)

/-- Every lane count is a `dim`. -/
theorem typedV_dim (sh : Shape) : TypedV (simEnv B) (.varT "dim" []) (pctV sh.lanes) := by
  have htup : HasTyp (simEnv B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN sh.lanes)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hp : EvalExp (simEnv B) (caseScope VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN sh.lanes)])) dimPrem (.bool true) := by
    have h := evalExp_dimPrem (B := B) (ρ := caseScope VarEnv.empty
      (.tupT [.mk "i" (.numT .natT)]) (.tuple [.num (.natN sh.lanes)])) (n := sh.lanes)
      (by simp [caseScope, typBinds])
    rcases sh with s | s <;> cases s <;> simpa [Shape.lanes, IntShape.lanes, FloatShape.lanes]
      using h
  exact typedV_closedCaseP findTyp_dim rfl htup (IntNumeric.premsOk_if hp)

/-- Every lane count is an `M`. -/
theorem typedV_M (sh : Shape) : TypedV (simEnv B) (.varT "M" []) (pctV sh.lanes) :=
  Typing.typedV_alias findTyp_M (typedV_dim sh)

/-! ## `$size`, `$lsize`, `$lanetype` -/

/-- A literal clause pattern `C` fails definitely on another nullary injection. -/
theorem matchArgs_caseNil_undef {X Y : MixopS} (h : Y ≠ X) :
    MatchArgsUndef (simEnv B) VarEnv.empty [.expA (.caseE X (.tupE []))] [.val (caseNilV Y)] :=
  matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef h))

/-- A literal clause pattern `C` matches `C`. -/
theorem matchArgs_caseNil {X : MixopS} :
    MatchArgs (simEnv B) VarEnv.empty [.expA (.caseE X (.tupE []))] [.val (caseNilV X)]
      VarEnv.empty :=
  matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil

/-- **`$size(nt)`** is the width, at every number type. -/
theorem applies_size (t : NumType) :
    Applies (simEnv B) "size" [.val (Vec.numTypeV t)] (natV t.width) := by
  obtain ⟨ps, ty, hd⟩ := Simd.findDef_size' B
  refine ⟨ps, ty, _, hd, Or.inl ?_⟩
  rcases t with t | t <;> cases t
  · exact tryClauses_hit matchArgs_caseNil premsHold_nil RefsGC.evalExp_num'
  · exact tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
      (tryClauses_hit matchArgs_caseNil premsHold_nil RefsGC.evalExp_num')
  · exact tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
      (tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
        (tryClauses_hit matchArgs_caseNil premsHold_nil RefsGC.evalExp_num'))
  · exact tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
      (tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
        (tryClauses_skip_match (matchArgs_caseNil_undef (by decide))
          (tryClauses_hit matchArgs_caseNil premsHold_nil RefsGC.evalExp_num')))

set_option maxRecDepth 100000 in
/-- `$lsize(Fnn)` is the width. -/
theorem applies_lsize_float (t : FloatType) :
    Applies (simEnv B) "lsize" [.val (Vec.numTypeV (.float t))] (natV t.width) := by
  obtain ⟨ps, ty, hd⟩ := Simd.findDef_lsize B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
    (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var (v := Vec.numTypeV (.float t)) (by simp))
      evalArgs_nil) (applies_size (.float t))))⟩
  cases t <;> rfl

/-- **`$lsize(Lnn)`** is the lane width, at every shape. -/
theorem applies_lsize' (sh : Shape) :
    Applies (simEnv B) "lsize" [.val (Vec.laneTypeV sh)] (natV sh.laneWidth) := by
  rcases sh with s | s
  · exact Simd.applies_lsize s
  · cases s
    · exact applies_lsize_float .f32
    · exact applies_lsize_float .f64

set_option maxRecDepth 100000 in
theorem findDef_lanetype (B : Builtins) : ∃ ps t q, (simEnv B).findDef? "lanetype" = some (ps, t,
    [.defD q [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]))] (.varE "Lnn") []]) :=
  ⟨_, _, _, rfl⟩

/-- `%X%(Lnn, M)` binds both. -/
theorem matchExp_shapePat {ρ : VarEnv} (h₁ : ρ.findVal? "Lnn" = none) (l m : Value)
    (hM : (ρ.bindVal "Lnn" l).findVal? "M" = none) :
    MatchExp (simEnv B) ρ (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]))
      (.case "%X%" (.tuple [l, m])) ((ρ.bindVal "Lnn" l).bindVal "M" m) :=
  matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2 ⟨_, rfl,
    Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_varE h₁,
      Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_varE hM,
        Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩)

/-- **`$lanetype(sh)`** is the shape's lane type. -/
theorem applies_lanetype (sh : Shape) :
    Applies (simEnv B) "lanetype" [.val (Vec.shapeV sh)] (Vec.laneTypeV sh) := by
  obtain ⟨ps, ty, q, hd⟩ := findDef_lanetype B
  have hsh : Vec.shapeV sh = .case "%X%" (.tuple [Vec.laneTypeV sh, pctV sh.lanes]) := by
    rcases sh with s | s <;> rfl
  rw [hsh]
  exact ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_shapePat (by simp) _ _ (by simp))) matchArgs_nil) premsHold_nil
    (evalExp_var (by simp)))⟩

/-! ## `shape`, `ishape`, `bshape` -/

/-- The premise of `shape`'s case. -/
noncomputable def shapePrem : Exp :=
  .cmpE .eqOp .boolT (.binE .mulOp (.numT .natT) (.callE "lsize" [.expA (.varE "lanetype")])
    (.projE (.uncaseE (.varE "dim") "%") 0)) (.numE (.natN 128))

/-- The payload type of `shape`'s case. -/
abbrev shapeTup : Typ := .tupT [.mk "lanetype" (.varT "lanetype" []), .mk "dim" (.varT "dim" [])]

set_option maxRecDepth 100000 in
theorem findTyp_shape : (simEnv B).findTyp? "shape" = some ([], [.instD [] []
    (.variantT [.mk "%X%" shapeTup [] [.ifPr shapePrem]])]) := rfl

theorem shapeV_eq (sh : Shape) :
    Vec.shapeV sh = .case "%X%" (.tuple [Vec.laneTypeV sh, pctV sh.lanes]) := by
  rcases sh with s | s <;> rfl

theorem laneWidth_mul_lanes (sh : Shape) : sh.laneWidth * sh.lanes = 128 := by
  rcases sh with s | s <;> cases s <;> rfl

/-- **Every shape is a `shape`.** -/
theorem typedV_shape (sh : Shape) : TypedV (simEnv B) (.varT "shape" []) (Vec.shapeV sh) := by
  rw [shapeV_eq]
  have htup : HasTyp (simEnv B) VarEnv.empty shapeTup
      (.tuple [Vec.laneTypeV sh, pctV sh.lanes]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      typedV_lanetype sh _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl,
        typedV_dim sh _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩
  have hl : EvalExp (simEnv B) (caseScope VarEnv.empty shapeTup
      (.tuple [Vec.laneTypeV sh, pctV sh.lanes])) (.callE "lsize" [.expA (.varE "lanetype")])
      (natV sh.laneWidth) :=
    Vec.evalExp_call rfl
      (evalArgs_cons (evalExp_var (by simp [caseScope, typBinds])) evalArgs_nil) (applies_lsize' sh)
  have hd : EvalExp (simEnv B) (caseScope VarEnv.empty shapeTup
      (.tuple [Vec.laneTypeV sh, pctV sh.lanes])) (.projE (.uncaseE (.varE "dim") "%") 0)
      (.num (.natN sh.lanes)) :=
    IntNumeric.evalExp_pctPayload (by simp [caseScope, typBinds, pctV])
  refine typedV_closedCaseP findTyp_shape rfl htup (IntNumeric.premsOk_if ?_)
  exact evalExp_cmpE_iff.2 ⟨_, _,
    evalExp_binNum (m := .natN (sh.laneWidth * sh.lanes)) hl hd rfl, evalExp_num,
    by simp [cmpValues, laneWidth_mul_lanes]⟩

/-- The premise of `ishape`'s case: `$lanetype(shape) = Jnn`, defining `Jnn`. -/
noncomputable def ishapePrem : Exp :=
  .cmpE .eqOp .boolT (.callE "lanetype" [.expA (.varE "shape")])
    (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))

/-- The payload type of `ishape`'s and `bshape`'s case. -/
abbrev shapeBind : Typ := .tupT [.mk "shape" (.varT "shape" [])]

set_option maxRecDepth 100000 in
theorem findTyp_ishape : (simEnv B).findTyp? "ishape" = some ([], [.instD [] []
    (.variantT [.mk "%" shapeBind [.expP "Jnn" (.varT "Jnn" [])] [.ifPr ishapePrem]])]) := rfl

/-- The premise of `bshape`'s case. -/
noncomputable def bshapePrem : Exp :=
  .cmpE .eqOp .boolT (.callE "lanetype" [.expA (.varE "shape")]) (.caseE "I8" (.tupE []))

set_option maxRecDepth 100000 in
theorem findTyp_bshape : (simEnv B).findTyp? "bshape" = some ([], [.instD [] []
    (.variantT [.mk "%" shapeBind [] [.ifPr bshapePrem]])]) := rfl

/-- The shape payload, typed. -/
theorem hasTyp_shapeBind (sh : Shape) :
    HasTyp (simEnv B) VarEnv.empty shapeBind (.tuple [Vec.shapeV sh]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    typedV_shape sh _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩

/-- `$lanetype(shape)` in a scope binding `shape`. -/
theorem evalExp_lanetypeOf {ρ : VarEnv} (sh : Shape) (h : ρ.findVal? "shape" = some (Vec.shapeV sh))
    (hd : ρ.findDef? "lanetype" = none) :
    EvalExp (simEnv B) ρ (.callE "lanetype" [.expA (.varE "shape")]) (Vec.laneTypeV sh) :=
  Vec.evalExp_call hd (evalArgs_cons (evalExp_var h) evalArgs_nil) (applies_lanetype sh)

/-- **Every integer shape is an `ishape`.** -/
theorem typedV_ishape (s : IntShape) : TypedV (simEnv B) (.varT "ishape" []) (Vec.ishapeV s) :=
  fun _ hρ => by
    show HasTyp _ _ _ (.case "%" (.tuple [Vec.shapeV (.int s)]))
    let σ := caseScope VarEnv.empty shapeBind (.tuple [Vec.shapeV (.int s)])
    have hl : EvalExp (simEnv B) σ (.callE "lanetype" [.expA (.varE "shape")])
        (Vec.intLaneV s) :=
      evalExp_lanetypeOf (.int s) (by simp [σ, caseScope, typBinds]) rfl
    have hq : BindQuants (simEnv B) σ [("Jnn", .varT "Jnn" [], .callE "lanetype"
        [.expA (.varE "shape")])] (σ.bindVal "Jnn" (Vec.intLaneV s)) :=
      bindQuants_cons hl (typedV_jnn s _ ⟨rfl, rfl, rfl⟩) (bindQuants_nil_iff.2 rfl)
    have hp : EvalExp (simEnv B) (σ.bindVal "Jnn" (Vec.intLaneV s)) ishapePrem (.bool true) :=
      evalExp_cmpE_iff.2 ⟨Vec.intLaneV s, Vec.intLaneV s,
        evalExp_lanetypeOf (.int s) (by simp [σ, caseScope, typBinds]) rfl,
        evalExp_subE_iff.2 (evalExp_var (by simp)), by simp [cmpValues]⟩
    exact hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_ishape
      evalArgs_nil matchArgs_nil (Typing.hasTypCase_of_findCaseQ rfl (hasTyp_shapeBind (.int s))
        hq (IntNumeric.premsOk_if hp))

/-- **`I8 X 16` is a `bshape`.** -/
theorem typedV_bshape : TypedV (simEnv B) (.varT "bshape" []) Vec.bshapeV := by
  show TypedV _ _ (.case "%" (.tuple [Vec.shapeV (.int .i8x16)]))
  refine typedV_closedCaseP findTyp_bshape rfl (hasTyp_shapeBind (.int .i8x16))
    (IntNumeric.premsOk_if (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_lanetypeOf (.int .i8x16) (by simp [caseScope, typBinds]) rfl,
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩, rfl⟩, ?_⟩))
  simp [cmpValues, Vec.laneTypeV, Vec.intLaneV, caseNilV]

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
