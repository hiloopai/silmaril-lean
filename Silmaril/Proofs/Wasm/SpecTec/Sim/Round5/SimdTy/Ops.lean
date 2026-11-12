module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Types
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Refute

/-!
# Round 5: the lane-wise operator families

`vunop_`, `vbinop_`, `vternop_`, `vtestop_` and `vrelop_` select their first instance, whose
pattern is `%X%(Jnn <: lanetype, M)`, at every shape (`matchArgs_jnnShapePat`). That instance
types every integer operator Core accepts (its premises are Core's `valid` side conditions),
and the float operators of the same name and payload: `ABS`, `NEG` (`vunop_`), `ADD`, `SUB`,
`MUL` (`vbinop_`, `MUL`'s premise `$lsizenn(Fnn) >= 16` holds), `EQ`, `NE` (`vrelop_`).
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
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d236 Original.d237 Original.d238 Original.d239
  Original.d240)
open IntNumeric (instCases)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `$lsizenn` -/

/-- A clause `$x(lt) = $lsize(lt)`. -/
def LsizeAlias (B : Builtins) (x : IL.Id) : Prop :=
  ∃ ps t q, (simEnv B).findDef? x = some (ps, t,
    [.defD q [.expA (.varE "lt")] (.callE "lsize" [.expA (.varE "lt")]) []])

set_option maxRecDepth 100000 in
theorem lsizeAlias_lsizenn : LsizeAlias B "lsizenn" := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem lsizeAlias_lsizenn1 : LsizeAlias B "lsizenn1" := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem lsizeAlias_lsizenn2 : LsizeAlias B "lsizenn2" := ⟨_, _, _, rfl⟩

/-- `$lsizenn(Lnn)` (and its two copies) is the lane width. -/
theorem applies_lsizeAlias {x : IL.Id} (hx : LsizeAlias B x) (sh : Shape) :
    Applies (simEnv B) x [.val (Vec.laneTypeV sh)] (natV sh.laneWidth) := by
  obtain ⟨ps, t, q, hd⟩ := hx
  exact ⟨ps, t, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_varE (by simp))) matchArgs_nil) premsHold_nil (Vec.evalExp_call rfl
      (evalArgs_cons (evalExp_var (by simp)) evalArgs_nil) (applies_lsize' sh)))⟩

/-- `$lsizenn(J <: lanetype)`, for a lane-type variable `J` of the scope. -/
theorem evalExp_lsizeAlias {x J : IL.Id} (hx : LsizeAlias B x) {ρ : VarEnv} {sh : Shape}
    (hJ : ρ.findVal? J = some (Vec.laneTypeV sh)) (hd : ρ.findDef? x = none) :
    EvalExp (simEnv B) ρ
      (.callE x [.expA (.subE (.varE J) (.varT "Jnn" []) (.varT "lanetype" []))])
      (natV sh.laneWidth) :=
  Vec.evalExp_call hd (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var hJ)) evalArgs_nil)
    (applies_lsizeAlias hx sh)

/-! ## Families keyed on `%X%(Jnn <: lanetype, M)` -/

/-- The scope of the `Jnn` instance at a shape. -/
abbrev jnnScope (sh : Shape) : VarEnv :=
  (VarEnv.empty.bindVal "Jnn" (Vec.laneTypeV sh)).bindVal "M" (pctV sh.lanes)

theorem jnnScope_Jnn (sh : Shape) : (jnnScope sh).findVal? "Jnn" = some (Vec.laneTypeV sh) := by
  simp

/-- A family whose first instance is `%X%(Jnn <: lanetype, M)` types that instance's cases at
**every** shape. -/
theorem hasTyp_jnnFam {x : IL.Id} {ps q : List Param} {cs : List TypCase} {rest : List Inst}
    (htd : (simEnv B).findTyp? x = some (ps, .instD q [.expA jnnShapePat] (.variantT cs) :: rest))
    {ρ : VarEnv} {e : Exp} {sh : Shape} (he : EvalExp (simEnv B) ρ e (Vec.shapeV sh))
    {op : MixopS} {w : Value} (hc : HasTypCase (simEnv B) (jnnScope sh) cs op w) :
    HasTyp (simEnv B) ρ (.varT x [.expA e]) (.case op w) := by
  rw [shapeV_eq] at he
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (evalArgs_cons he evalArgs_nil)
    (hasTypInsts_head (matchArgs_jnnShapePat _ _) (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

/-- A family keyed on a shape. -/
def JnnFam (B : Builtins) (x : IL.Id) (d : Def) : Prop :=
  ∃ ps q rest, (simEnv B).findTyp? x =
    some (ps, .instD q [.expA jnnShapePat] (.variantT (instCases d 0)) :: rest)

set_option maxRecDepth 100000 in
theorem jnnFam_vunop : JnnFam B "vunop_" Original.d236 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem jnnFam_vbinop : JnnFam B "vbinop_" Original.d237 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem jnnFam_vternop : JnnFam B "vternop_" Original.d238 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem jnnFam_vtestop : JnnFam B "vtestop_" Original.d239 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem jnnFam_vrelop : JnnFam B "vrelop_" Original.d240 := ⟨_, _, _, rfl⟩

/-- A family keyed on a shape, at an expression evaluating to a shape. -/
theorem hasTyp_ofFam {x : IL.Id} {d : Def} (hF : JnnFam B x d) {ρ : VarEnv} {e : Exp} {sh : Shape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV sh)) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (jnnScope sh) (instCases d 0) op w) :
    HasTyp (simEnv B) ρ (.varT x [.expA e]) (.case op w) := by
  obtain ⟨ps, q, rest, htd⟩ := hF
  exact hasTyp_jnnFam htd he hc

/-- `$lsizenn(Jnn) ⋈ k` in the `Jnn` scope. -/
theorem evalExp_lsizeCmp (sh : Shape) (op : CmpOp) (k : Nat) (b : Bool)
    (hb : cmpValues op (natV sh.laneWidth) (natV k) = .ok (.bool b)) :
    EvalExp (simEnv B) (jnnScope sh) (.cmpE op (.numT .natT)
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN k))) (.bool b) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_lsizeAlias lsizeAlias_lsizenn (jnnScope_Jnn sh) rfl,
    evalExp_num, hb⟩

/-- `cmpValues` on two naturals, for an ordering. -/
theorem cmpValues_le (a b : Nat) (h : a ≤ b) :
    cmpValues .leOp (natV a) (natV b) = .ok (.bool true) := by
  simp [cmpValues, natV, Num.cmp, h]

theorem cmpValues_ge (a b : Nat) (h : b ≤ a) :
    cmpValues .geOp (natV a) (natV b) = .ok (.bool true) := by
  simp [cmpValues, natV, Num.cmp, h]

theorem cmpValues_eq (a : Nat) : cmpValues .eqOp (natV a) (natV a) = .ok (.bool true) := by
  simp [cmpValues]

/-- The same with a boolean operator type. -/
theorem evalExp_lsizeCmpB (sh : Shape) (op : CmpOp) (k : Nat) (b : Bool)
    (hb : cmpValues op (natV sh.laneWidth) (natV k) = .ok (.bool b)) :
    EvalExp (simEnv B) (jnnScope sh) (.cmpE op .boolT
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN k))) (.bool b) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_lsizeAlias lsizeAlias_lsizenn (jnnScope_Jnn sh) rfl,
    evalExp_num, hb⟩

/-! ## `vunop_` -/

set_option maxRecDepth 100000 in
/-- **`vunop_(Jnn X M)`** holds every integer unary operator valid at the shape. -/
theorem hasTyp_vIntUnOp {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.int s))) {op : VecIntUnOp} (hv : op.valid s = true) :
    HasTyp (simEnv B) ρ (.varT "vunop_" [.expA e]) (Vec.vIntUnOpV op) := by
  cases op
  · exact hasTyp_ofFam jnnFam_vunop he (IntNumeric.hasTypCase_nullary rfl)
  · exact hasTyp_ofFam jnnFam_vunop he (IntNumeric.hasTypCase_nullary rfl)
  · obtain rfl : s = .i8x16 := by simpa [VecIntUnOp.valid] using hv
    exact hasTyp_ofFam jnnFam_vunop he (IntNumeric.hasTypCase_of_findCase rfl hasTyp_tupT_nil
      (IntNumeric.premsOk_if (evalExp_lsizeCmpB _ _ _ _ (by simp [cmpValues]; rfl))))

set_option maxRecDepth 100000 in
/-- `vunop_(Fnn X M)` holds `ABS` and `NEG` (through the `Jnn` instance). -/
theorem hasTyp_vFloatUnOp {ρ : VarEnv} {e : Exp} {s : FloatShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.float s))) {op : FloatUnOp}
    (hm : FloatMissel (.vecFloatUnOp s op) = false) :
    HasTyp (simEnv B) ρ (.varT "vunop_" [.expA e]) (Vec.vFloatUnOpV op) := by
  cases op <;> simp [FloatMissel] at hm
  · exact hasTyp_ofFam jnnFam_vunop he (IntNumeric.hasTypCase_nullary rfl)
  · exact hasTyp_ofFam jnnFam_vunop he (IntNumeric.hasTypCase_nullary rfl)

/-! ## `vbinop_`, `vternop_`, `vtestop_` -/

set_option maxRecDepth 100000 in
theorem typedV_vsx (s : Signedness) : TypedV (simEnv B) (.varT "sx" []) (Vec.sxV s) :=
  fun _ hρ => by cases s <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

theorem valsOnly_jnnScope (sh : Shape) : ValsOnly (jnnScope sh) := ⟨rfl, rfl, rfl⟩

/-- `$lsizenn(Jnn) <= k`, from the width. -/
theorem binPrem_le {s : IntShape} {k : Nat} (h : decide (s.laneWidth ≤ k) = true) :
    EvalExp (simEnv B) (jnnScope (.int s)) (.cmpE .leOp (.numT .natT)
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN k))) (.bool true) :=
  evalExp_lsizeCmp _ _ _ _ (cmpValues_le _ _ (of_decide_eq_true h))

/-- `$lsizenn(Jnn) >= k`, from the width. -/
theorem binPrem_ge {s : IntShape} {k : Nat} (h : decide (s.laneWidth ≥ k) = true) :
    EvalExp (simEnv B) (jnnScope (.int s)) (.cmpE .geOp (.numT .natT)
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN k))) (.bool true) :=
  evalExp_lsizeCmp _ _ _ _ (cmpValues_ge _ _ (of_decide_eq_true h))

/-- `$lsizenn(Jnn) = 16` at `I16 X 8`. -/
theorem binPrem_eq16 {s : IntShape} (h : (s == .i16x8) = true) :
    EvalExp (simEnv B) (jnnScope (.int s)) (.cmpE .eqOp .boolT
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN 16))) (.bool true) := by
  have hs : s = .i16x8 := beq_iff_eq.1 h
  exact hs ▸ evalExp_lsizeCmpB _ _ _ _ (cmpValues_eq 16)

set_option maxRecDepth 100000 in
/-- **`vbinop_(Jnn X M)`** holds every integer binary operator valid at the shape. -/
theorem hasTyp_vIntBinOp {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.int s))) {op : VecIntBinOp}
    (hv : op.valid s = true) :
    HasTyp (simEnv B) ρ (.varT "vbinop_" [.expA e]) (Vec.vIntBinOpV op) := by
  have hsx (x : Signedness) : HasTyp (simEnv B) (jnnScope (.int s)) (.varT "sx" []) (Vec.sxV x) :=
    typedV_vsx x _ (valsOnly_jnnScope (.int s))
  cases op with
  | add => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_nullary rfl)
  | sub => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_nullary rfl)
  | mul => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      hasTyp_tupT_nil (IntNumeric.premsOk_if (binPrem_ge hv)))
  | addSat x => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      (hsx x) (IntNumeric.premsOk_if (binPrem_le hv)))
  | subSat x => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      (hsx x) (IntNumeric.premsOk_if (binPrem_le hv)))
  | avgrU => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      hasTyp_tupT_nil (IntNumeric.premsOk_if (binPrem_le hv)))
  | q15mulrSatS => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      hasTyp_tupT_nil (IntNumeric.premsOk_if (binPrem_eq16 hv)))
  | relaxedQ15mulrS => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase
      rfl hasTyp_tupT_nil (IntNumeric.premsOk_if (binPrem_eq16 hv)))
  | min x => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      (hsx x) (IntNumeric.premsOk_if (binPrem_le hv)))
  | max x => exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl
      (hsx x) (IntNumeric.premsOk_if (binPrem_le hv)))

set_option maxRecDepth 100000 in
/-- `vbinop_(Fnn X M)` holds `ADD`, `SUB`, `MUL` (through the `Jnn` instance). -/
theorem hasTyp_vFloatBinOp {ρ : VarEnv} {e : Exp} {s : FloatShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.float s))) {op : VecFloatBinOp}
    (hm : FloatMissel (.vecFloatBinOp s op) = false) :
    HasTyp (simEnv B) ρ (.varT "vbinop_" [.expA e]) (Vec.vFloatBinOpV op) := by
  cases op <;> simp [FloatMissel] at hm
  · exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_nullary rfl)
  · exact hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_nullary rfl)
  · refine hasTyp_ofFam jnnFam_vbinop he (IntNumeric.hasTypCase_of_findCase rfl hasTyp_tupT_nil
      (IntNumeric.premsOk_if (evalExp_lsizeCmp _ _ _ _ ?_)))
    exact cmpValues_ge _ _ (by cases s <;> decide)

set_option maxRecDepth 100000 in
/-- `vternop_(Jnn X M)` holds `RELAXED_LANESELECT`. -/
theorem hasTyp_vIntTernOp {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.int s))) (op : VecIntTernOp) :
    HasTyp (simEnv B) ρ (.varT "vternop_" [.expA e]) (Vec.vIntTernOpV op) := by
  cases op
  exact hasTyp_ofFam jnnFam_vternop he (IntNumeric.hasTypCase_nullary rfl)

set_option maxRecDepth 100000 in
/-- `vtestop_(Jnn X M)` holds `ALL_TRUE`. -/
theorem hasTyp_vAllTrue {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.int s))) :
    HasTyp (simEnv B) ρ (.varT "vtestop_" [.expA e]) (caseNilV "ALL_TRUE") :=
  hasTyp_ofFam jnnFam_vtestop he (IntNumeric.hasTypCase_nullary rfl)

/-! ## `vrelop_` -/

/-- `sx = S`, for `sx` bound in the scope. -/
theorem evalExp_sxIsS {ρ : VarEnv} {x : Signedness} (h : ρ.findVal? "sx" = some (Vec.sxV x)) :
    EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.varE "sx") (.caseE "S" (.tupE [])))
      (.bool (decide (x = .signed))) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_var h,
    evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩, rfl⟩,
    by cases x <;> simp [cmpValues, Vec.sxV, caseNilV]⟩

/-- The scope of a signed comparison's premise. -/
abbrev relScope (s : IntShape) (x : Signedness) : VarEnv :=
  (jnnScope (.int s)).bindVal "sx" (Vec.sxV x)

/-- The premise of the signed integer comparisons: `$lsizenn(Jnn) =/= 64 \/ sx = S`. -/
theorem evalExp_relPrem (s : IntShape) (x : Signedness) (hv : (s != .i64x2 || x == .signed) = true) :
    EvalExp (simEnv B) (relScope s x) (.binE .orOp .boolT (.cmpE .neOp .boolT
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN 64))) (.cmpE .eqOp .boolT (.varE "sx") (.caseE "S" (.tupE []))))
      (.bool true) := by
  have h₁ : EvalExp (simEnv B) (relScope s x) (.cmpE .neOp .boolT
      (.callE "lsizenn" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))])
      (.numE (.natN 64))) (.bool (decide ((Shape.int s).laneWidth ≠ 64))) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_lsizeAlias (sh := .int s) lsizeAlias_lsizenn (by simp) rfl,
      evalExp_num, by cases s <;> simp [cmpValues, natV, Shape.laneWidth, IntShape.laneWidth]⟩
  have h := evalExp_or (t := .boolT) h₁ (evalExp_sxIsS (B := B) (x := x) (by simp))
  cases s <;> cases x <;> first | exact h | simp at hv

set_option maxRecDepth 100000 in
/-- **`vrelop_(Jnn X M)`** holds every integer comparison valid at the shape. -/
theorem hasTyp_vIntRelOp {ρ : VarEnv} {e : Exp} {s : IntShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.int s))) {op : IntRelOp}
    (hv : op.validShape s = true) :
    HasTyp (simEnv B) ρ (.varT "vrelop_" [.expA e]) (Vec.vIntRelOpV op) := by
  have htup (x : Signedness) : HasTyp (simEnv B) (jnnScope (.int s))
      (.tupT [.mk "sx" (.varT "sx" [])]) (.tuple [Vec.sxV x]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      typedV_vsx x _ (valsOnly_jnnScope _), hasTypTup_nil_iff.2 rfl⟩⟩
  cases op with
  | eq => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_nullary rfl)
  | ne => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_nullary rfl)
  | lt x => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_of_findCase rfl (htup x)
      (IntNumeric.premsOk_if (evalExp_relPrem s x hv)))
  | gt x => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_of_findCase rfl (htup x)
      (IntNumeric.premsOk_if (evalExp_relPrem s x hv)))
  | le x => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_of_findCase rfl (htup x)
      (IntNumeric.premsOk_if (evalExp_relPrem s x hv)))
  | ge x => exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_of_findCase rfl (htup x)
      (IntNumeric.premsOk_if (evalExp_relPrem s x hv)))

set_option maxRecDepth 100000 in
/-- `vrelop_(Fnn X M)` holds `EQ`, `NE` (through the `Jnn` instance). -/
theorem hasTyp_vFloatRelOp {ρ : VarEnv} {e : Exp} {s : FloatShape}
    (he : EvalExp (simEnv B) ρ e (Vec.shapeV (.float s))) {op : FloatRelOp}
    (hm : FloatMissel (.vecFloatRelOp s op) = false) :
    HasTyp (simEnv B) ρ (.varT "vrelop_" [.expA e]) (Vec.vFloatRelOpV op) := by
  cases op <;> simp [FloatMissel] at hm
  · exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_nullary rfl)
  · exact hasTyp_ofFam jnnFam_vrelop he (IntNumeric.hasTypCase_nullary rfl)

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
