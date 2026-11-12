module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Ops

/-!
# Round 5: the shift, swizzle, extending and conversion operator families

* `vshiftop_(ishape)`, `vswizzlop_(bshape)`: every operator;
* `vextunop__`, `vextbinop__`, `vextternop__` (keyed on two integer shapes): every operator Core
  accepts, the premises being Core's `valid` side conditions;
* `vcvtop__(shape, shape)`: its first instance, keyed on `%X%(Jnn_1 <: lanetype, M_1)` and
  `%X%(Jnn_2 <: lanetype, M_2)`, is selected at every pair of shapes; it types `EXTEND` (the
  only conversion Core accepts at two integer shapes) and nothing else.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d241 Original.d242 Original.d243 Original.d244
  Original.d245 Original.d246)
open IntNumeric (instCases)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Patterns -/

/-- `%X%(J <: lanetype, M)`. -/
abbrev shPat (J M : IL.Id) : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE J) (.varT "Jnn" []) (.varT "lanetype" []), .varE M])

/-- `%(%X%(J <: lanetype, M))`. -/
abbrev ishPat (J M : IL.Id) : Exp := .caseE "%" (.tupE [shPat J M])

/-- `%X%(J <: lanetype, M)` matches every shape. -/
theorem matchExp_shPat {ρ : VarEnv} {J M : IL.Id} (hJ : ρ.findVal? J = none) (l m : Value)
    (hM : (ρ.bindVal J l).findVal? M = none) :
    MatchExp (simEnv B) ρ (shPat J M) (.case "%X%" (.tuple [l, m]))
      ((ρ.bindVal J l).bindVal M m) :=
  matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2 ⟨_, rfl,
    Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, Prims.matchExp_subE (matchExp_varE hJ),
      Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_varE hM,
        Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩)

/-- `%(%X%(J <: lanetype, M))` matches every `ishape` image. -/
theorem matchExp_ishPat {ρ : VarEnv} {J M : IL.Id} (hJ : ρ.findVal? J = none) (l m : Value)
    (hM : (ρ.bindVal J l).findVal? M = none) :
    MatchExp (simEnv B) ρ (ishPat J M) (.case "%" (.tuple [.case "%X%" (.tuple [l, m])]))
      ((ρ.bindVal J l).bindVal M m) :=
  matchExp_caseE (matchExp_tupE_one (matchExp_shPat hJ l m hM))

theorem ishapeV_eq (s : IntShape) :
    Vec.ishapeV s = .case "%" (.tuple [.case "%X%" (.tuple [Vec.intLaneV s, pctV s.lanes])]) :=
  rfl

/-! ## `vshiftop_`, `vswizzlop_` -/

set_option maxRecDepth 100000 in
theorem findTyp_vshiftop : ∃ ps q, (simEnv B).findTyp? "vshiftop_" =
    some (ps, [.instD q [.expA (ishPat "Jnn" "M")] (.variantT (instCases Original.d241 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- **`vshiftop_(ishape)`** holds `SHL` and `SHR sx`. -/
theorem hasTyp_vShiftOp {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.ishapeV s)) (op : VecShiftOp) :
    HasTyp (simEnv B) ρ (.varT "vshiftop_" [.expA e]) (Vec.vShiftOpV op) := by
  obtain ⟨ps, q, htd⟩ := findTyp_vshiftop (B := B)
  have hm : MatchArgs (simEnv B) VarEnv.empty [.expA (ishPat "Jnn" "M")] [.val (Vec.ishapeV s)]
      (jnnScope (.int s)) :=
    matchArgs_cons (matchArg_expA (matchExp_ishPat (by simp) _ _ (by simp))) matchArgs_nil
  have hi {op : MixopS} {w : Value}
      (hc : HasTypCase (simEnv B) (jnnScope (.int s)) (instCases Original.d241 0) op w) :
      HasTyp (simEnv B) ρ (.varT "vshiftop_" [.expA e]) (.case op w) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (evalArgs_cons he evalArgs_nil)
      (hasTypInsts_head hm (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))
  cases op with
  | shl => exact hi (IntNumeric.hasTypCase_nullary rfl)
  | shr x =>
    exact hi (IntNumeric.hasTypCase_of_findCase rfl (typedV_vsx x _ (valsOnly_jnnScope _))
      premsOk_nil)

set_option maxRecDepth 100000 in
theorem findTyp_vswizzlop : ∃ ps q, (simEnv B).findTyp? "vswizzlop_" = some (ps,
    [.instD q [.expA (.caseE "%" (.tupE [.caseE "%X%" (.tupE [.caseE "I8" (.tupE []), .varE "M"])]))]
      (.variantT (instCases Original.d242 0))]) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- **`vswizzlop_(bshape)`** holds both swizzles. -/
theorem hasTyp_vSwizzleOp {ρ : VarEnv} {e : Exp} (he : EvalExp (simEnv B) ρ e Vec.bshapeV)
    (op : VecSwizzleOp) :
    HasTyp (simEnv B) ρ (.varT "vswizzlop_" [.expA e]) (Vec.vSwizzleOpV op) := by
  obtain ⟨ps, q, htd⟩ := findTyp_vswizzlop (B := B)
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (.caseE "%" (.tupE [.caseE "%X%" (.tupE [.caseE "I8" (.tupE []), .varE "M"])]))]
      [.val Vec.bshapeV] (VarEnv.empty.bindVal "M" (pctV 16)) :=
    matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE_one (matchExp_caseE
      (Equiv.Validation.matchExp_tup_iff.2 ⟨_, rfl, Equiv.Validation.matchExps_cons_iff.2
        ⟨_, _, _, rfl, matchExp_caseE matchExp_tupE_nil,
          Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl, matchExp_varE (by simp),
            Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩))))) matchArgs_nil
  cases op <;> exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (evalArgs_cons he evalArgs_nil) (hasTypInsts_head hm (hasTypDef_variantT_iff.2
      ⟨_, _, rfl, IntNumeric.hasTypCase_nullary rfl⟩))

/-! ## Families keyed on two integer shapes -/

/-- The scope of an instance keyed on `(Jnn_1, M_1)` and `(Jnn_2, M_2)`. -/
abbrev twoScope (l₁ m₁ l₂ m₂ : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "Jnn_1" l₁).bindVal "M_1" m₁).bindVal "Jnn_2" l₂).bindVal "M_2" m₂

/-- A family whose first instance is keyed on two `ishape` patterns. -/
def IshFam2 (B : Builtins) (x : IL.Id) (d : Def) : Prop :=
  ∃ ps q rest, (simEnv B).findTyp? x = some (ps,
    .instD q [.expA (ishPat "Jnn_1" "M_1"), .expA (ishPat "Jnn_2" "M_2")]
      (.variantT (instCases d 0)) :: rest)

set_option maxRecDepth 100000 in
theorem ishFam2_vextunop : IshFam2 B "vextunop__" Original.d243 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem ishFam2_vextbinop : IshFam2 B "vextbinop__" Original.d244 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem ishFam2_vextternop : IshFam2 B "vextternop__" Original.d245 := ⟨_, _, _, rfl⟩

/-- The scope of a two-`ishape` instance at the shapes `s`, `t`. -/
abbrev ishScope (s t : IntShape) : VarEnv :=
  twoScope (Vec.intLaneV s) (pctV s.lanes) (Vec.intLaneV t) (pctV t.lanes)

/-- A two-`ishape` family types its first instance's cases. -/
theorem hasTyp_ishFam2 {x : IL.Id} {d : Def} (hF : IshFam2 B x d) {ρ : VarEnv} {e₁ e₂ : Exp}
    {s t : IntShape} (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s))
    (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t)) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (ishScope s t) (instCases d 0) op w) :
    HasTyp (simEnv B) ρ (.varT x [.expA e₁, .expA e₂]) (.case op w) := by
  obtain ⟨ps, q, rest, htd⟩ := hF
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (ishPat "Jnn_1" "M_1"), .expA (ishPat "Jnn_2" "M_2")]
      [.val (Vec.ishapeV s), .val (Vec.ishapeV t)] (ishScope s t) :=
    matchArgs_cons (matchArg_expA (matchExp_ishPat (by simp) _ _ (by simp)))
      (matchArgs_cons (matchArg_expA (matchExp_ishPat (by simp) _ _ (by simp))) matchArgs_nil)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (evalArgs_cons he₁ (evalArgs_cons he₂ evalArgs_nil))
    (hasTypInsts_head hm (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

/-! ### Premise arithmetic -/

/-- `$lsizenn1(Jnn_1)` in a scope binding `Jnn_1` to a lane type. -/
theorem evalExp_l1 {ρ : VarEnv} {sh : Shape} (h : ρ.findVal? "Jnn_1" = some (Vec.laneTypeV sh))
    (hd : ρ.findDef? "lsizenn1" = none) :
    EvalExp (simEnv B) ρ (.callE "lsizenn1"
      [.expA (.subE (.varE "Jnn_1") (.varT "Jnn" []) (.varT "lanetype" []))])
      (natV sh.laneWidth) :=
  evalExp_lsizeAlias lsizeAlias_lsizenn1 h hd

/-- `$lsizenn2(Jnn_2)`. -/
theorem evalExp_l2 {ρ : VarEnv} {sh : Shape} (h : ρ.findVal? "Jnn_2" = some (Vec.laneTypeV sh))
    (hd : ρ.findDef? "lsizenn2" = none) :
    EvalExp (simEnv B) ρ (.callE "lsizenn2"
      [.expA (.subE (.varE "Jnn_2") (.varT "Jnn" []) (.varT "lanetype" []))])
      (natV sh.laneWidth) :=
  evalExp_lsizeAlias lsizeAlias_lsizenn2 h hd

/-- `k * e`. -/
theorem evalExp_mulLit {ρ : VarEnv} {e : Exp} {a : Nat} (k : Nat)
    (he : EvalExp (simEnv B) ρ e (natV a)) :
    EvalExp (simEnv B) ρ (.binE .mulOp (.numT .natT) (.numE (.natN k)) e) (natV (k * a)) :=
  evalExp_binNum evalExp_num he rfl

/-- `a ⋈ b`, true. -/
theorem evalExp_cmpTrue {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Nat} {op : CmpOp} {t : OpTyp}
    (h₁ : EvalExp (simEnv B) ρ e₁ (natV a)) (h₂ : EvalExp (simEnv B) ρ e₂ (natV b))
    (hc : cmpValues op (natV a) (natV b) = .ok (.bool true)) :
    EvalExp (simEnv B) ρ (.cmpE op t e₁ e₂) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, h₁, h₂, hc⟩

/-- `a = b`, for equal naturals. -/
theorem cmpValues_eq' {a b : Nat} (h : a = b) :
    cmpValues .eqOp (natV a) (natV b) = .ok (.bool true) := h ▸ cmpValues_eq a

/-- `p /\ q`, both true. -/
theorem evalExp_andT {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp}
    (h₁ : EvalExp (simEnv B) ρ e₁ (.bool true)) (h₂ : EvalExp (simEnv B) ρ e₂ (.bool true)) :
    EvalExp (simEnv B) ρ (.binE .andOp t e₁ e₂) (.bool true) :=
  IntNumeric.evalExp_and h₁ h₂

/-! ### The extending operators -/

theorem ishScope_J1 (s t : IntShape) :
    (ishScope s t).findVal? "Jnn_1" = some (Vec.laneTypeV (.int s)) := by simp [Vec.laneTypeV]

theorem ishScope_J2 (s t : IntShape) :
    (ishScope s t).findVal? "Jnn_2" = some (Vec.laneTypeV (.int t)) := by simp [Vec.laneTypeV]

theorem laneWidth_ge8 (s : IntShape) : 8 ≤ s.laneWidth := by cases s <;> decide

set_option maxRecDepth 100000 in
/-- **`vextunop__(ishape_1, ishape_2)`** holds `EXTADD_PAIRWISE sx` at every valid pair. -/
theorem hasTyp_vExtUnOp {ρ : VarEnv} {e₁ e₂ : Exp} {s t : IntShape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t))
    {op : VecExtUnOp} (hv : op.valid s t = true) :
    HasTyp (simEnv B) ρ (.varT "vextunop__" [.expA e₁, .expA e₂]) (Vec.vExtUnOpV op) := by
  have h₁ := evalExp_l1 (B := B) (ishScope_J1 s t) rfl
  have h₂ := evalExp_l2 (B := B) (ishScope_J2 s t) rfl
  simp only [VecExtUnOp.valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  obtain ⟨ht, ht32⟩ := hv
  cases op with
  | extaddPairwise x =>
    exact hasTyp_ishFam2 ishFam2_vextunop he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl
      (typedV_vsx x _ ⟨rfl, rfl, rfl⟩) (IntNumeric.premsOk_if (evalExp_andT
        (evalExp_cmpTrue evalExp_num (evalExp_mulLit 2 h₁)
          (cmpValues_le _ _ (by have := laneWidth_ge8 s; simp only [Shape.laneWidth]; omega)))
        (evalExp_andT (evalExp_cmpTrue (evalExp_mulLit 2 h₁) h₂ (cmpValues_eq' ht.symm))
          (evalExp_cmpTrue h₂ evalExp_num (cmpValues_le _ _ ht32))))))

/-- The `half; sx` payload, typed. -/
theorem hasTyp_halfSx {σ : VarEnv} (hσ : ValsOnly σ) (h : Half) (x : Signedness) :
    HasTyp (simEnv B) σ (.tupT [.mk "half" (.varT "half" []), .mk "sx" (.varT "sx" [])])
      (.tuple [Vec.halfV h, Vec.sxV x]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, typedV_half h _ hσ,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, typedV_vsx x _ ⟨hσ.1, hσ.2.1, hσ.2.2⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- The scope of a `half; sx` case's premise. -/
abbrev halfSxScope (σ : VarEnv) (h : Half) (x : Signedness) : VarEnv :=
  caseScope σ (.tupT [.mk "half" (.varT "half" []), .mk "sx" (.varT "sx" [])])
    (.tuple [Vec.halfV h, Vec.sxV x])

set_option maxRecDepth 100000 in
/-- `EXTMUL half sx` at a pair whose target doubles the source width. -/
theorem hasTyp_vExtMul {ρ : VarEnv} {e₁ e₂ : Exp} {s t : IntShape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t))
    (h : Half) (x : Signedness) (hv : t.laneWidth = 2 * s.laneWidth) :
    HasTyp (simEnv B) ρ (.varT "vextbinop__" [.expA e₁, .expA e₂])
      (Vec.vExtBinOpV (.extmul h x)) := by
  have h₁ : EvalExp (simEnv B) (halfSxScope (ishScope s t) h x) (.callE "lsizenn1"
      [.expA (.subE (.varE "Jnn_1") (.varT "Jnn" []) (.varT "lanetype" []))])
      (natV s.laneWidth) :=
    evalExp_l1 (sh := .int s) (by simp [caseScope, typBinds, Vec.laneTypeV]) rfl
  have h₂ : EvalExp (simEnv B) (halfSxScope (ishScope s t) h x) (.callE "lsizenn2"
      [.expA (.subE (.varE "Jnn_2") (.varT "Jnn" []) (.varT "lanetype" []))])
      (natV t.laneWidth) :=
    evalExp_l2 (sh := .int t) (by simp [caseScope, typBinds, Vec.laneTypeV]) rfl
  have h16 : 16 ≤ t.laneWidth := by have := laneWidth_ge8 s; omega
  exact hasTyp_ishFam2 ishFam2_vextbinop he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl
    (hasTyp_halfSx ⟨rfl, rfl, rfl⟩ h x) (IntNumeric.premsOk_if (evalExp_andT
      (evalExp_cmpTrue (evalExp_mulLit 2 h₁) h₂ (cmpValues_eq' hv.symm))
      (evalExp_cmpTrue h₂ evalExp_num (cmpValues_ge _ _ h16)))))

set_option maxRecDepth 100000 in
/-- A nullary `vextbinop__` case whose premise is `2 * |Jnn_1| = |Jnn_2| = k`. -/
theorem hasTyp_vExtBinNullary {ρ : VarEnv} {e₁ e₂ : Exp} {s t : IntShape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t))
    {op : VecExtBinOp} (hop : op = .dotS ∨ op = .relaxedDotS) (hv : op.valid s t = true) :
    HasTyp (simEnv B) ρ (.varT "vextbinop__" [.expA e₁, .expA e₂]) (Vec.vExtBinOpV op) := by
  have h₁ := evalExp_l1 (B := B) (ishScope_J1 s t) rfl
  have h₂ := evalExp_l2 (B := B) (ishScope_J2 s t) rfl
  rcases hop with rfl | rfl
  · have hst : s = .i16x8 ∧ t = .i32x4 := by simpa [VecExtBinOp.valid] using hv
    obtain ⟨rfl, rfl⟩ := hst
    exact hasTyp_ishFam2 ishFam2_vextbinop he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl
      hasTyp_tupT_nil (IntNumeric.premsOk_if (evalExp_andT
        (evalExp_cmpTrue (evalExp_mulLit 2 h₁) h₂ (cmpValues_eq' rfl))
        (evalExp_cmpTrue h₂ evalExp_num (cmpValues_eq' rfl)))))
  · have hst : s = .i8x16 ∧ t = .i16x8 := by simpa [VecExtBinOp.valid] using hv
    obtain ⟨rfl, rfl⟩ := hst
    exact hasTyp_ishFam2 ishFam2_vextbinop he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl
      hasTyp_tupT_nil (IntNumeric.premsOk_if (evalExp_andT
        (evalExp_cmpTrue (evalExp_mulLit 2 h₁) h₂ (cmpValues_eq' rfl))
        (evalExp_cmpTrue h₂ evalExp_num (cmpValues_eq' rfl)))))

/-- **`vextbinop__(ishape_1, ishape_2)`** holds every operator Core accepts at the pair. -/
theorem hasTyp_vExtBinOp {ρ : VarEnv} {e₁ e₂ : Exp} {s t : IntShape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t))
    {op : VecExtBinOp} (hv : op.valid s t = true) :
    HasTyp (simEnv B) ρ (.varT "vextbinop__" [.expA e₁, .expA e₂]) (Vec.vExtBinOpV op) := by
  cases op with
  | extmul h x => exact hasTyp_vExtMul he₁ he₂ h x (beq_iff_eq.1 hv)
  | dotS => exact hasTyp_vExtBinNullary he₁ he₂ (.inl rfl) hv
  | relaxedDotS => exact hasTyp_vExtBinNullary he₁ he₂ (.inr rfl) hv

set_option maxRecDepth 100000 in
/-- **`vextternop__(ishape_1, ishape_2)`** holds `RELAXED_DOT_ADDS` at its one valid pair. -/
theorem hasTyp_vExtTernOp {ρ : VarEnv} {e₁ e₂ : Exp} {s t : IntShape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.ishapeV s)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.ishapeV t))
    {op : VecExtTernOp} (hv : op.valid s t = true) :
    HasTyp (simEnv B) ρ (.varT "vextternop__" [.expA e₁, .expA e₂]) (Vec.vExtTernOpV op) := by
  simp only [VecExtTernOp.valid, Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  have h₁ := evalExp_l1 (B := B) (ishScope_J1 .i8x16 .i32x4) rfl
  have h₂ := evalExp_l2 (B := B) (ishScope_J2 .i8x16 .i32x4) rfl
  cases op
  exact hasTyp_ishFam2 ishFam2_vextternop he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl
    hasTyp_tupT_nil (IntNumeric.premsOk_if (evalExp_andT
      (evalExp_cmpTrue (evalExp_mulLit 4 h₁) h₂ (cmpValues_eq' rfl))
      (evalExp_cmpTrue h₂ evalExp_num (cmpValues_eq' rfl)))))

/-! ## `vcvtop__` -/

set_option maxRecDepth 100000 in
theorem findTyp_vcvtop : ∃ ps q rest, (simEnv B).findTyp? "vcvtop__" = some (ps,
    .instD q [.expA (shPat "Jnn_1" "M_1"), .expA (shPat "Jnn_2" "M_2")]
      (.variantT (instCases Original.d246 0)) :: rest) := ⟨_, _, _, rfl⟩

/-- The scope of `vcvtop__`'s first instance at two shapes. -/
abbrev cvtScope (a b : Shape) : VarEnv :=
  twoScope (Vec.laneTypeV a) (pctV a.lanes) (Vec.laneTypeV b) (pctV b.lanes)

/-- **`vcvtop__`'s first instance is selected at every pair of shapes.** -/
theorem hasTyp_vcvtop_inst {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Shape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.shapeV a)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.shapeV b))
    {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (cvtScope a b) (instCases Original.d246 0) op w) :
    HasTyp (simEnv B) ρ (.varT "vcvtop__" [.expA e₁, .expA e₂]) (.case op w) := by
  obtain ⟨ps, q, rest, htd⟩ := findTyp_vcvtop (B := B)
  rw [shapeV_eq] at he₁ he₂
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (shPat "Jnn_1" "M_1"), .expA (shPat "Jnn_2" "M_2")]
      [.val (.case "%X%" (.tuple [Vec.laneTypeV a, pctV a.lanes])),
       .val (.case "%X%" (.tuple [Vec.laneTypeV b, pctV b.lanes]))] (cvtScope a b) :=
    matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) _ _ (by simp)))
      (matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) _ _ (by simp))) matchArgs_nil)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (evalArgs_cons he₁ (evalArgs_cons he₂ evalArgs_nil))
    (hasTypInsts_head hm (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

set_option maxRecDepth 100000 in
/-- **`vcvtop__(shape_1, shape_2)`** holds `EXTEND half sx` at every valid pair. -/
theorem hasTyp_vConvertOp {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Shape}
    (he₁ : EvalExp (simEnv B) ρ e₁ (Vec.shapeV a)) (he₂ : EvalExp (simEnv B) ρ e₂ (Vec.shapeV b))
    {op : VecConvertOp} (hv : op.valid a b = true)
    (hm : FloatMissel (.vecConvert a b op) = false) :
    HasTyp (simEnv B) ρ (.varT "vcvtop__" [.expA e₁, .expA e₂]) (Vec.vConvertOpV op) := by
  cases op with
  | extend h x =>
    rcases a with s | s <;> rcases b with t | t <;>
      simp only [VecConvertOp.valid, beq_iff_eq, Bool.false_eq_true] at hv
    let σ := caseScope (cvtScope (.int s) (.int t))
      (.tupT [.mk "half" (.varT "half" []), .mk "sx" (.varT "sx" [])])
      (.tuple [Vec.halfV h, Vec.sxV x])
    have h₁ := evalExp_l1 (B := B) (ρ := σ) (sh := .int s) (by simp [σ, caseScope, typBinds]) rfl
    have h₂ := evalExp_l2 (B := B) (ρ := σ) (sh := .int t) (by simp [σ, caseScope, typBinds]) rfl
    have htup : HasTyp (simEnv B) (cvtScope (.int s) (.int t))
        (.tupT [.mk "half" (.varT "half" []), .mk "sx" (.varT "sx" [])])
        (.tuple [Vec.halfV h, Vec.sxV x]) :=
      hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, typedV_half h _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, typedV_vsx x _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_nil_iff.2 rfl⟩⟩⟩
    exact hasTyp_vcvtop_inst he₁ he₂ (IntNumeric.hasTypCase_of_findCase rfl htup
      (IntNumeric.premsOk_if (evalExp_cmpTrue h₂ (evalExp_mulLit 2 h₁) (cmpValues_eq' hv))))
  | _ => simp [FloatMissel] at hm

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
