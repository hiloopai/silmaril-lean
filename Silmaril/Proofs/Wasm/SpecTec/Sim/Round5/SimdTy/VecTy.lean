module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Instr
public import Silmaril.Wasm.SpecTec.Sim.Round5.VecTyL.Defs

/-!
# Round 5: the restated vector typing holds, so `Int.VectorFwd` needs only the
# operator agreement

* `hasTyp_laneInt`, `lanesL`: every lane `$lanes_` returns at an integer shape is a
  `lane_($lanetype(Jnn X M))` (through `num_` at `I32`, `I64` and `pack_` at `I8`, `I16`);
* `typedDep_of_instrTyped`, `typedDep2_of_instrTyped`: a typed SIMD instruction's operator is
  typed at its shape in every scope that binds the shape (inverting `instr`, then moving the
  operator type to the scope's variable names);
* `extractSx_of_instrTyped`: a typed `VEXTRACT_LANE` has a signedness exactly at packed lanes
  (inverting its case premise, `evalExp_extractPrem`);
* `vecTypingL`: `VecTypingL` holds at the concrete builtins;
* `vectorFwd_of_ops`: **`Int.VectorFwd` from `VecAgreeOps` alone**, through family V's forward
  lemmas (`fwd_vectorL`, which takes `VecTypingL` where `Vec.fwd_vector` takes the false
  `Vec.VecTyping`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {H : Type}

/-! ## Closed fields -/

theorem findDef_none {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) : ρ.findDef? x = none := by
  simp [VarEnv.findDef?, hρ.2.1]

/-- Every 32-bit pattern is a `num_(I32)`. -/
theorem typedV_i32 (a : BitVec 32) : TypedV (simEnv B) Vec.i32T (Vec.i32NV a) := fun _ _ =>
  IntNumeric.hasTyp_num (t := .i32) a
    (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩, rfl⟩)

set_option maxRecDepth 100000 in
/-- `I8` and `I16` are `packtype`s. -/
theorem typedV_packtype (s : IntShape) (h : s.laneWidth < 32) :
    TypedV (simEnv B) (.varT "packtype" []) (Vec.intLaneV s) := fun _ hρ => by
  cases s
  · exact IntNumeric.hasTyp_closedNullary hρ rfl rfl
  · exact IntNumeric.hasTyp_closedNullary hρ rfl rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A numeral of a shape's unpacked type is a `num_($lunpack(Lnn))`. -/
theorem numLunpackL (P : Profile) (hn : H → String) (host : HostSemantics H) (s : Shape)
    (x : BitVec s.unpacked.width) :
    Vec.TypedDep (simEnv (BI P hn host)) "Lnn" (Vec.laneTypeV s)
      (.varT "num_" [.expA (.callE "lunpack" [.expA (.varE "Lnn")])])
      (numV ⟨s.unpacked, x⟩) := fun ρ hρ hx => by
  have h₀ : HasTyp (simEnv (BI P hn host)) (VarEnv.empty.bindVal "nt" (Vec.numTypeV s.unpacked))
      (Vec.numT "nt") (numV ⟨s.unpacked, x⟩) :=
    Typing.typedDep_num "nt" ⟨s.unpacked, x⟩ _ ⟨rfl, rfl, rfl⟩ (by simp)
  exact Pos.hasTyp_varT_transfer rfl rfl h₀ (evalArgs_cons (evalExp_var (by simp)) evalArgs_nil)
    (evalArgs_cons (Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons (evalExp_var hx)
      evalArgs_nil) (Simd.applies_lunpack s)) evalArgs_nil)

/-! ## The lanes -/

set_option maxRecDepth 100000 in
theorem findTyp_lane : ∃ ps q₁ q₂ i₃, (simEnv B).findTyp? "lane_" = some (ps,
    [.instD q₁ [.expA Simd.numtypePatL] (.aliasT (.varT "num_" [.expA (.varE "numtype")])),
     .instD q₂ [.expA Simd.packtypePatL] (.aliasT (.varT "pack_" [.expA (.varE "packtype")])),
     i₃]) := ⟨_, _, _, _, rfl⟩

/-- `pack_(pt)` holds the numerals below the packed width. -/
theorem hasTyp_packLane (p : PackType) (x : BitVec p.width) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType)))
      (.varT "pack_" [.expA (.varE "packtype")]) (pctV x.toNat) := by
  obtain ⟨ps', q', htp⟩ := R4Fwd.findTyp_pack B
  obtain ⟨ps'', q'', htn⟩ := IntNumeric.findTyp_iN (B := B)
  refine hasTyp_varT_of_insts (by simp [localTyp?]) htp
    (evalArgs_cons (evalExp_var (v := tyV (Ty.pack p : CStorageType)) (by simp)) evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 ?_))
  exact hasTyp_varT_of_insts (by simp [localTyp?]) htn
    (evalArgs_cons (Vec.evalExp_call rfl (evalArgs_cons
      (evalExp_var (v := tyV (Ty.pack p : CStorageType)) (by simp)) evalArgs_nil)
      (R4Fwd.applies_psizenn p)) evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN (evalExp_var (v := natV p.width) (by simp))
        x.isLt)))

/-- The type `vtestop` quantifies the lanes at. -/
abbrev laneT : Typ :=
  .varT "lane_" [.expA (.callE "lanetype" [.expA (.caseE "%X%" (.tupE
    [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])]

/-- `$lanetype(Jnn X M)`. -/
theorem evalExp_laneTypeArg {ρ : VarEnv} (hρ : ValsOnly ρ) {s : IntShape}
    (hJ : ρ.findVal? "Jnn" = some (Vec.intLaneV s)) (hM : ρ.findVal? "M" = some (pctV s.lanes)) :
    EvalExp (simEnv B) ρ (.callE "lanetype" [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])
      (Vec.intLaneV s) :=
  Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons (evalExp_caseE_iff.2 ⟨_,
    evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_subE_iff.2 (evalExp_var hJ))
      (evalExps_cons (evalExp_var hM) evalExps_nil), rfl⟩, rfl⟩) evalArgs_nil)
    (applies_lanetype (.int s))

set_option maxRecDepth 100000 in
/-- **A lane of an integer shape is a `lane_($lanetype(Jnn X M))`.** -/
theorem hasTyp_laneInt {ρ : VarEnv} (hρ : ValsOnly ρ) (s : IntShape)
    (hJ : ρ.findVal? "Jnn" = some (Vec.intLaneV s)) (hM : ρ.findVal? "M" = some (pctV s.lanes))
    (x : BitVec (Shape.int s).laneWidth) : HasTyp (simEnv B) ρ laneT (pctV x.toNat) := by
  obtain ⟨ps, q₁, q₂, i₃, htd⟩ := findTyp_lane (B := B)
  have harg := evalExp_laneTypeArg (B := B) hρ hJ hM
  have hnum (t : IntType) (ha : EvalExp (simEnv B) ρ (.callE "lanetype" [.expA (.caseE "%X%"
      (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])
      (IntNumeric.ntV t)) (y : BitVec t.width) : HasTyp (simEnv B) ρ laneT (pctV y.toNat) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (evalArgs_cons ha evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
        (matchExp_varE (by simp))) (by cases t <;> rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_num y (evalExp_var (by simp)))))
  have hpack (p : PackType) (ha : EvalExp (simEnv B) ρ (.callE "lanetype" [.expA (.caseE "%X%"
      (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])
      (tyV (Ty.pack p : CStorageType))) (y : BitVec p.width) :
      HasTyp (simEnv B) ρ laneT (pctV y.toNat) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (evalArgs_cons ha evalArgs_nil)
      (R4Fwd.skip_inst (by cases p <;> rfl) (hasTypInsts_head (matchArgs_cons
        (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
          (R4Fwd.argSubOk_packtypePat_pack p rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (hasTyp_packLane p y))))
  cases s
  · exact hpack .i8 harg x
  · exact hpack .i16 harg x
  · exact hnum .i32 harg x
  · exact hnum .i64 harg x

/-- **The lanes `$lanes_` returns at an integer shape are typed** (`VecTypingL.lanes`). -/
theorem lanesL (P : Profile) (hn : H → String) (host : HostSemantics H) (s : IntShape) (a : V128)
    (ls : List Value)
    (hl : Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.ishV s), .val (Vec.vecV a)]
      (.list ls)) :
    Vec.TypedDep2 (simEnv (BI P hn host)) "Jnn" (Vec.intLaneV s) "M" (pctV s.lanes)
      (.iterT laneT .list) (.list ls) := fun ρ hρ hJ hM => by
  have he : Value.list ls = .list (Simd.lanesV (.int s) a) :=
    hl.unique (Simd.applies_lanes P hn host (.int s) a)
  rw [he]
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_laneInt hρ s hJ hM x

/-! ## Inverting a typed SIMD instruction -/

/-- A typed instruction's image is typed by its `instr` case. -/
theorem hasTypCase_of_instrTyped {i : Instr} {op : MixopS} {w : Value}
    (hi : instrToV i = .case op w) (h : Vec.InstrTyped (simEnv B) i) :
    HasTypCase (simEnv B) VarEnv.empty (IntNumeric.recCases Original.d271 0 0) op w := by
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  have hv : HasTyp (simEnv B) VarEnv.empty (.varT "instr" []) (instrToV i) :=
    hasTypList_iff.1 hl _ ((Value.list.inj hvs) ▸ List.mem_cons_self)
  exact Typing.hasTypCase_of_closedVariant (IntNumeric.findTyp_instr' B) (hi ▸ hv)

/-- **The operator of a typed two-field SIMD instruction is typed at its shape**, in every
scope binding `sh` to the shape. -/
theorem typedDep_of_instrTyped {i : Instr} {op : MixopS} {T X : IL.Id} {sv w : Value}
    {prems : List Prem} (hi : instrToV i = .case op (.tuple [sv, w]))
    (hf : IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) op =
      some (.tupT [.mk T (.varT T []), .mk "_" (.varT X [.expA (.varE T)])], prems))
    (hT : T ≠ "_") (h : Vec.InstrTyped (simEnv B) i) :
    Vec.TypedDep (simEnv B) "sh" sv (Vec.opT X "sh") w := fun _ _ hx => by
  have hp := IntNumeric.hasTyp_of_hasTypCase (hasTypCase_of_instrTyped hi h) hf
  exact Pos.hasTyp_varT_transfer rfl rfl (Typing.hasTyp_pair_inv hp).2
    (evalArgs_cons (evalExp_var (by simp [hT])) evalArgs_nil)
    (evalArgs_cons (evalExp_var hx) evalArgs_nil)

/-- **The operator of a typed three-field SIMD instruction is typed at its two shapes.** -/
theorem typedDep2_of_instrTyped {i : Instr} {op : MixopS} {A C K X : IL.Id} {u v w : Value}
    {prems : List Prem} (hi : instrToV i = .case op (.tuple [u, v, w]))
    (hf : IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) op =
      some (.tupT [.mk A (.varT K []), .mk C (.varT K []),
        .mk "_" (.varT X [.expA (.varE C), .expA (.varE A)])], prems))
    (hA : A ≠ "_") (hC : C ≠ "_") (hAC : A ≠ C) (h : Vec.InstrTyped (simEnv B) i) :
    Vec.TypedDep2 (simEnv B) "sh_1" v "sh_2" u (Vec.opT2 X) w := fun _ _ hx hy => by
  have hp := IntNumeric.hasTyp_of_hasTypCase (hasTypCase_of_instrTyped hi h) hf
  exact Pos.hasTyp_varT_transfer rfl rfl (ConfigOk.hasTyp_triple_inv hp).2.2
    (Pos.evalArgs_vars (by simp [hC]) (by simp [hA, hC, hAC.symm]))
    (Pos.evalArgs_vars hx hy)

/-- The premises of a quantifier-free case hold in its payload's scope. -/
theorem premsOk_of_hasTypCase {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ} {prems : List Prem} {w : Value},
      HasTypCase env σ cs op w → IntNumeric.findCase cs op = some (t, prems) →
      IntNumeric.quantFreeAt cs op = true → PremsOk env (caseScope σ t w) prems
  | [], _, _, _, _, h, _, _ => absurd h not_hasTypCase_nil
  | .mk o t' qs prems' :: cs, op, t, prems, w, h, hf, hq => by
      by_cases ho : o = op
      · simp only [IntNumeric.findCase, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        have hq' : quantDefs qs prems' = [] := by
          simpa [IntNumeric.quantFreeAt, ho] using hq
        exact ((hasTypCase_cons_hit_iff ho hq').1 h).2
      · have hf' : IntNumeric.findCase cs op = some (t, prems) := by
          simpa [IntNumeric.findCase, ho] using hf
        have hq' : IntNumeric.quantFreeAt cs op = true := by
          simpa [IntNumeric.quantFreeAt, ho] using hq
        exact premsOk_of_hasTypCase ((hasTypCase_cons_miss_iff ho).1 h) hf' hq'

set_option maxRecDepth 100000 in
/-- **A typed `VEXTRACT_LANE` has a signedness exactly at packed lanes.** -/
theorem extractSx_of_instrTyped (sh : Shape) (sx : Option Signedness) (i : LaneIdx)
    (h : Vec.InstrTyped (simEnv B) (.vecExtractLane sh sx i)) :
    sx = none ↔ 32 ≤ sh.laneWidth := by
  have hc := hasTypCase_of_instrTyped (op := "VEXTRACT_LANE")
    (w := .tuple [Vec.shapeV sh, .opt (sx.map Vec.sxV), Vec.laneIdxV i]) rfl h
  have hp : PremsOk (simEnv B) (extractScope sh sx i) [.ifPr extractPremE] :=
    premsOk_of_hasTypCase hc rfl rfl
  have hb : extractB sh sx = true := by
    have := (ConfigOk.evalExp_of_premsOk_if hp).unique (evalExp_extractPrem sh sx i)
    exact (Value.bool.inj this).symm
  have hsx := (extractB_eq_true sh sx).1 hb
  cases sx with
  | none => simpa [eq_comm] using hsx
  | some x => simpa [eq_comm] using hsx

/-! ## `VecTypingL` at the concrete builtins -/

set_option maxRecDepth 100000 in
/-- **The restated vector typing holds at the concrete builtins.** -/
theorem vecTypingL (P : Profile) (hn : H → String) (host : HostSemantics H) :
    VecTypingL (simEnv (BI P hn host)) where
  vec := Typing.typedV_vecT
  i32 := typedV_i32
  vvunop := FwdSimdAgg.typedV_vvunop
  vvbinop := FwdSimdAgg.typedV_vvbinop
  vvternop := FwdSimdAgg.typedV_vvternop
  sx := typedV_vsx
  shape := typedV_shape
  ishape := typedV_ishape
  bshape := typedV_bshape
  intUnOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  floatUnOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  intBinOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  floatBinOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  intTernOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  floatTernOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  intRelOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  floatRelOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  shiftOp _ _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  swizzle _ h := typedDep_of_instrTyped rfl rfl (by decide) h
  shuffle ls _ := fun _ hρ => hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
    exact typedV_laneidx i _ hρ⟩
  extUnOp _ _ _ h := typedDep2_of_instrTyped rfl rfl (by decide) (by decide) (by decide) h
  extBinOp _ _ _ h := typedDep2_of_instrTyped rfl rfl (by decide) (by decide) (by decide) h
  extTernOp _ _ _ h := typedDep2_of_instrTyped rfl rfl (by decide) (by decide) (by decide) h
  dim := typedV_M
  laneidx := typedV_laneidx
  packtype := typedV_packtype
  lnn := typedV_lnn
  numLunpack := numLunpackL P hn host
  jnn := typedV_jnn
  lanes := lanesL P hn host
  extractSx sh sx i h := extractSx_of_instrTyped sh sx i h
  convert _ _ _ h := typedDep2_of_instrTyped rfl rfl (by decide) (by decide) (by decide) h

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
