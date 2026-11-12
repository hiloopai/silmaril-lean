module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Ops2

/-!
# Round 5: the SIMD instructions are typed `instr`s

Each non-memory SIMD instruction other than `v128.const` is a typed `instr` in every
`simEnv B` when Core accepts it and it is not `FloatMissel`:

* the payloads: the shapes (`Types.lean`) and the operators (`Ops.lean`, `Ops2.lean`), the
  operator read in the scope that binds the shape;
* the case premises of `VSHUFFLE` (`|laneidx*| = $dim(bshape)`), `VEXTRACT_LANE`
  (`sx? = eps <=> $lanetype(shape) ∈ [I32, I64, F32, F64]`) and `VNARROW`
  (`|lanetype(ishape_2)| = 2 * |lanetype(ishape_1)| <= 32`) from Core's validity.

`simdTypingSel`: the restated `SimdTypingSel B` holds for every `B`. The memory SIMD
instructions are not bounded (`Round4.instrBnd`), so they are excluded already.
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
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Payload helpers -/

/-- A two-field payload whose second type reads the first field. -/
theorem hasTyp_pair {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h₁ : HasTyp (simEnv B) VarEnv.empty τ₁ u)
    (h₂ : HasTyp (simEnv B) (VarEnv.empty.bindVal a u) τ₂ v) :
    HasTyp (simEnv B) VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂, hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- A three-field payload whose third type reads the first two. -/
theorem hasTyp_triple {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : HasTyp (simEnv B) VarEnv.empty τ₁ u)
    (h₂ : HasTyp (simEnv B) (VarEnv.empty.bindVal a u) τ₂ v)
    (h₃ : HasTyp (simEnv B) ((VarEnv.empty.bindVal a u).bindVal b v) τ₃ w) :
    HasTyp (simEnv B) VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

/-- An `instr` case with premises. -/
theorem typedV_instrCaseP {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) op = some (t, prems))
    (hq : IntNumeric.quantFreeAt (IntNumeric.recCases Original.d271 0 0) op = true)
    (h : HasTyp (simEnv B) VarEnv.empty t w)
    (hp : PremsOk (simEnv B) (caseScope VarEnv.empty t w) prems) :
    TypedV (simEnv B) (.varT "instr" []) (.case op w) := fun ρ hρ =>
  hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) (IntNumeric.findTyp_instr' B)
    evalArgs_nil matchArgs_nil (IntNumeric.hasTypCase_of_findCase hf h hp hq)

theorem empty_valsOnly : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem typedV_vectype : TypedV (simEnv B) (.varT "vectype" []) Vec.vecTypeV :=
  fun _ hρ => IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_vvtestop (op : VecTestOp) :
    TypedV (simEnv B) (.varT "vvtestop" []) (Vec.vvtestopV op) :=
  fun _ hρ => by cases op; exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

/-- `x` in the scope binding it last. -/
theorem evalExp_last {ρ : VarEnv} {x : IL.Id} {v : Value} (hx : x ≠ "_" := by decide) :
    EvalExp (simEnv B) (ρ.bindVal x v) (.varE x) v :=
  evalExp_var (by simp [Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit hx])

/-! ## The bitwise and lane-wise instructions -/

set_option maxRecDepth 100000 in
/-- The four bitwise instructions. -/
theorem typedV_bitwise (i : Instr)
    (hi : (∃ op, i = .vecUnOp op) ∨ (∃ op, i = .vecBinOp op) ∨ (∃ op, i = .vecTernOp op) ∨
      (∃ op, i = .vecTestOp op)) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  have hv := typedV_vectype (B := B) _ empty_valsOnly
  rcases hi with ⟨op, rfl⟩ | ⟨op, rfl⟩ | ⟨op, rfl⟩ | ⟨op, rfl⟩
  · exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_pair hv (FwdSimdAgg.typedV_vvunop op _ ⟨rfl, rfl, rfl⟩))
  · exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_pair hv (FwdSimdAgg.typedV_vvbinop op _ ⟨rfl, rfl, rfl⟩))
  · exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_pair hv (FwdSimdAgg.typedV_vvternop op _ ⟨rfl, rfl, rfl⟩))
  · exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_pair hv (typedV_vvtestop op _ ⟨rfl, rfl, rfl⟩))

/-- A shape, typed in the empty scope. -/
theorem hasTyp_shape0 (sh : Shape) :
    HasTyp (simEnv B) VarEnv.empty (.varT "shape" []) (Vec.shapeV sh) :=
  typedV_shape sh _ empty_valsOnly

set_option maxRecDepth 100000 in
/-- `VUNOP` at an integer shape. -/
theorem typedV_vecIntUnOp {s : IntShape} {op : VecIntUnOp} (hv : op.valid s = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecIntUnOp s op)) :=
  FwdMem.typedV_instrCase (op := "VUNOP") (w := .tuple [Vec.shapeV (.int s), Vec.vIntUnOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vIntUnOp evalExp_last hv))

set_option maxRecDepth 100000 in
/-- `VUNOP` at a float shape. -/
theorem typedV_vecFloatUnOp {s : FloatShape} {op : FloatUnOp}
    (hm : FloatMissel (.vecFloatUnOp s op) = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatUnOp s op)) :=
  FwdMem.typedV_instrCase (op := "VUNOP") (w := .tuple [Vec.shapeV (.float s), Vec.vFloatUnOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vFloatUnOp evalExp_last hm))

set_option maxRecDepth 100000 in
/-- `VBINOP` at an integer shape. -/
theorem typedV_vecIntBinOp {s : IntShape} {op : VecIntBinOp} (hv : op.valid s = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecIntBinOp s op)) :=
  FwdMem.typedV_instrCase (op := "VBINOP") (w := .tuple [Vec.shapeV (.int s), Vec.vIntBinOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vIntBinOp evalExp_last hv))

set_option maxRecDepth 100000 in
/-- `VBINOP` at a float shape. -/
theorem typedV_vecFloatBinOp {s : FloatShape} {op : VecFloatBinOp}
    (hm : FloatMissel (.vecFloatBinOp s op) = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatBinOp s op)) :=
  FwdMem.typedV_instrCase (op := "VBINOP")
    (w := .tuple [Vec.shapeV (.float s), Vec.vFloatBinOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vFloatBinOp evalExp_last hm))

set_option maxRecDepth 100000 in
/-- `VTERNOP` at an integer shape. -/
theorem typedV_vecIntTernOp (s : IntShape) (op : VecIntTernOp) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecIntTernOp s op)) :=
  FwdMem.typedV_instrCase (op := "VTERNOP")
    (w := .tuple [Vec.shapeV (.int s), Vec.vIntTernOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vIntTernOp evalExp_last op))

set_option maxRecDepth 100000 in
/-- `VTESTOP` (`all_true`). -/
theorem typedV_vecAllTrue (s : IntShape) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecAllTrue s)) :=
  FwdMem.typedV_instrCase (op := "VTESTOP")
    (w := .tuple [Vec.shapeV (.int s), caseNilV "ALL_TRUE"])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vAllTrue evalExp_last))

set_option maxRecDepth 100000 in
/-- `VRELOP` at an integer shape. -/
theorem typedV_vecIntRelOp {s : IntShape} {op : IntRelOp} (hv : op.validShape s = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecIntRelOp s op)) :=
  FwdMem.typedV_instrCase (op := "VRELOP") (w := .tuple [Vec.shapeV (.int s), Vec.vIntRelOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vIntRelOp evalExp_last hv))

set_option maxRecDepth 100000 in
/-- `VRELOP` at a float shape. -/
theorem typedV_vecFloatRelOp {s : FloatShape} {op : FloatRelOp}
    (hm : FloatMissel (.vecFloatRelOp s op) = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatRelOp s op)) :=
  FwdMem.typedV_instrCase (op := "VRELOP")
    (w := .tuple [Vec.shapeV (.float s), Vec.vFloatRelOpV op])
    rfl rfl (hasTyp_pair (hasTyp_shape0 _) (hasTyp_vFloatRelOp evalExp_last hm))

set_option maxRecDepth 100000 in
/-- `VSHIFTOP`. -/
theorem typedV_vecShiftOp (s : IntShape) (op : VecShiftOp) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecShiftOp s op)) :=
  FwdMem.typedV_instrCase rfl rfl
    (hasTyp_pair (typedV_ishape s _ empty_valsOnly) (hasTyp_vShiftOp evalExp_last op))

set_option maxRecDepth 100000 in
/-- `VBITMASK`. -/
theorem typedV_vecBitmask (s : IntShape) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecBitmask s)) :=
  FwdMem.typedV_instrCase rfl rfl (typedV_ishape s _ empty_valsOnly)

set_option maxRecDepth 100000 in
/-- `VSWIZZLOP`. -/
theorem typedV_vecSwizzle (op : VecSwizzleOp) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecSwizzle op)) :=
  FwdMem.typedV_instrCase rfl rfl
    (hasTyp_pair (typedV_bshape _ empty_valsOnly) (hasTyp_vSwizzleOp evalExp_last op))

set_option maxRecDepth 100000 in
/-- `VSPLAT`. -/
theorem typedV_vecSplat (s : Shape) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecSplat s)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_shape0 s)

set_option maxRecDepth 100000 in
/-- `VREPLACE_LANE`. -/
theorem typedV_vecReplaceLane (s : Shape) (i : LaneIdx) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecReplaceLane s i)) :=
  FwdMem.typedV_instrCase rfl rfl
    (hasTyp_pair (hasTyp_shape0 s) (typedV_laneidx i _ ⟨rfl, rfl, rfl⟩))

/-! ## The extending instructions and conversions -/

/-- The scope of the third field of `VEXT*OP`: `ishape_1`, then `ishape_2`. -/
theorem evalExp_ish2 {u v : Value} :
    EvalExp (simEnv B) ((VarEnv.empty.bindVal "ishape_1" u).bindVal "ishape_2" v)
      (.varE "ishape_2") v := evalExp_last

theorem evalExp_ish1 {u v : Value} :
    EvalExp (simEnv B) ((VarEnv.empty.bindVal "ishape_1" u).bindVal "ishape_2" v)
      (.varE "ishape_1") u := evalExp_var (by simp)

set_option maxRecDepth 100000 in
/-- `VEXTUNOP`. -/
theorem typedV_vecExtUnOp {s t : IntShape} {op : VecExtUnOp} (hv : op.valid s t = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecExtUnOp s t op)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_triple (typedV_ishape t _ empty_valsOnly)
    (typedV_ishape s _ ⟨rfl, rfl, rfl⟩) (hasTyp_vExtUnOp evalExp_ish2 evalExp_ish1 hv))

set_option maxRecDepth 100000 in
/-- `VEXTBINOP`. -/
theorem typedV_vecExtBinOp {s t : IntShape} {op : VecExtBinOp} (hv : op.valid s t = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecExtBinOp s t op)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_triple (typedV_ishape t _ empty_valsOnly)
    (typedV_ishape s _ ⟨rfl, rfl, rfl⟩) (hasTyp_vExtBinOp evalExp_ish2 evalExp_ish1 hv))

set_option maxRecDepth 100000 in
/-- `VEXTTERNOP`. -/
theorem typedV_vecExtTernOp {s t : IntShape} {op : VecExtTernOp} (hv : op.valid s t = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecExtTernOp s t op)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_triple (typedV_ishape t _ empty_valsOnly)
    (typedV_ishape s _ ⟨rfl, rfl, rfl⟩) (hasTyp_vExtTernOp evalExp_ish2 evalExp_ish1 hv))

set_option maxRecDepth 100000 in
/-- `VCVTOP`. -/
theorem typedV_vecConvert {s t : Shape} {op : VecConvertOp} (hv : op.valid s t = true)
    (hm : FloatMissel (.vecConvert s t op) = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecConvert s t op)) :=
  FwdMem.typedV_instrCase rfl rfl (hasTyp_triple (hasTyp_shape0 t)
    (typedV_shape s _ ⟨rfl, rfl, rfl⟩)
    (hasTyp_vConvertOp evalExp_last (evalExp_var (by simp)) hv hm))

/-! ## The instructions with case premises -/

set_option maxRecDepth 100000 in
theorem findDef_dim (B : Builtins) : ∃ ps t q, (simEnv B).findDef? "dim" = some (ps, t,
    [.defD q [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]))] (.varE "M") []]) :=
  ⟨_, _, _, rfl⟩

/-- **`$dim(sh)`** is the shape's lane count. -/
theorem applies_dim (sh : Shape) :
    Applies (simEnv B) "dim" [.val (Vec.shapeV sh)] (pctV sh.lanes) := by
  obtain ⟨ps, ty, q, hd⟩ := findDef_dim B
  rw [shapeV_eq]
  exact ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_shapePat (by simp) _ _ (by simp))) matchArgs_nil) premsHold_nil
    (evalExp_var (by simp)))⟩

/-- The payload of `VSHUFFLE`. -/
abbrev shuffleTup : Typ :=
  .tupT [.mk "bshape" (.varT "bshape" []), .mk "laneidx*" (.iterT (.varT "laneidx" []) .list)]

/-- The scope of `VSHUFFLE`'s premise. -/
abbrev shuffleScope (ls : List LaneIdx) : VarEnv :=
  caseScope VarEnv.empty shuffleTup (.tuple [Vec.bshapeV, .list (ls.map Vec.laneIdxV)])

/-- `%(|laneidx*|)`. -/
theorem evalExp_shuffleLen (ls : List LaneIdx) :
    EvalExp (simEnv B) (shuffleScope ls) (.caseE "%" (.tupE [.lenE (.iterE (.varE "laneidx")
      (.mk .list [.mk "laneidx" (.varE "laneidx*")]))])) (pctV ls.length) := by
  have hl : EvalExp (simEnv B) (shuffleScope ls) (.iterE (.varE "laneidx")
      (.mk .list [.mk "laneidx" (.varE "laneidx*")])) (.list (ls.map Vec.laneIdxV)) :=
    Equiv.Execution.evalExp_iterPat (x := "laneidx") (y := "laneidx*") (by decide)
      (by simp [caseScope, typBinds])
  have hn : EvalExp (simEnv B) (shuffleScope ls) (.lenE (.iterE (.varE "laneidx")
      (.mk .list [.mk "laneidx" (.varE "laneidx*")]))) (.num (.natN ls.length)) :=
    evalExp_lenE_iff.2 ⟨_, hl, by simp⟩
  exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[_], evalExps_cons hn evalExps_nil, rfl⟩, rfl⟩

/-- `$dim(bshape.0)`. -/
theorem evalExp_shuffleDim (ls : List LaneIdx) :
    EvalExp (simEnv B) (shuffleScope ls)
      (.callE "dim" [.expA (.projE (.uncaseE (.varE "bshape") "%") 0)]) (pctV 16) :=
  Vec.evalExp_call rfl (evalArgs_cons (evalExp_projE_iff.2 ⟨[Vec.shapeV (.int .i8x16)],
    evalExp_uncaseE_iff.2 (evalExp_var (by simp [caseScope, typBinds]; rfl)), le_refl _, rfl⟩)
    evalArgs_nil) (applies_dim (.int .i8x16))

set_option maxRecDepth 100000 in
/-- `VSHUFFLE` with sixteen lane indices. -/
theorem typedV_vecShuffle {ls : List LaneIdx} (hlen : ls.length = 16) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecShuffle ls)) := by
  have hl : HasTyp (simEnv B) (VarEnv.empty.bindVal "bshape" Vec.bshapeV)
      (.iterT (.varT "laneidx" []) .list) (.list (ls.map Vec.laneIdxV)) :=
    hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hw
      exact typedV_laneidx i _ ⟨rfl, rfl, rfl⟩⟩
  have hp : EvalExp (simEnv B) (shuffleScope ls) (.cmpE .eqOp .boolT
      (.caseE "%" (.tupE [.lenE (.iterE (.varE "laneidx")
        (.mk .list [.mk "laneidx" (.varE "laneidx*")]))]))
      (.callE "dim" [.expA (.projE (.uncaseE (.varE "bshape") "%") 0)])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_shuffleLen ls, evalExp_shuffleDim ls, by simp [cmpValues, hlen]⟩
  exact typedV_instrCaseP rfl rfl (hasTyp_pair (typedV_bshape _ empty_valsOnly) hl)
    (IntNumeric.premsOk_if hp)

/-- The payload of `VEXTRACT_LANE`. -/
abbrev extractTup : Typ :=
  .tupT [.mk "shape" (.varT "shape" []), .mk "sx?" (.iterT (.varT "sx" []) .opt),
    .mk "laneidx" (.varT "laneidx" [])]

/-- The scope of `VEXTRACT_LANE`'s premise. -/
abbrev extractScope (sh : Shape) (sx : Option Signedness) (i : LaneIdx) : VarEnv :=
  caseScope VarEnv.empty extractTup
    (.tuple [Vec.shapeV sh, .opt (sx.map Vec.sxV), Vec.laneIdxV i])

/-- The unpacked lane types. -/
abbrev unpackedLanes : Exp :=
  .listE [.caseE "I32" (.tupE []), .caseE "I64" (.tupE []), .caseE "F32" (.tupE []),
    .caseE "F64" (.tupE [])]

theorem evalExp_unpackedLanes {ρ : VarEnv} : EvalExp (simEnv B) ρ unpackedLanes
    (.list [caseNilV "I32", caseNilV "I64", caseNilV "F32", caseNilV "F64"]) := by
  have hc (X : MixopS) : EvalExp (simEnv B) ρ (.caseE X (.tupE [])) (caseNilV X) :=
    evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩, rfl⟩
  exact evalExp_listE_iff.2 ⟨_, evalExps_cons (hc _) (evalExps_cons (hc _) (evalExps_cons (hc _)
    (evalExps_cons (hc _) evalExps_nil))), rfl⟩

/-- The value of `VEXTRACT_LANE`'s premise. -/
def extractB (sh : Shape) (sx : Option Signedness) : Bool :=
  (Value.opt (sx.map Vec.sxV) == Value.opt none) ==
    [caseNilV "I32", caseNilV "I64", caseNilV "F32", caseNilV "F64"].contains (Vec.laneTypeV sh)

/-- `VEXTRACT_LANE`'s premise. -/
abbrev extractPremE : Exp :=
  .binE .equivOp .boolT (.cmpE .eqOp .boolT (.iterE (.varE "sx")
    (.mk .opt [.mk "sx" (.varE "sx?")])) (.optE none))
    (.memE (.callE "lanetype" [.expA (.varE "shape")]) unpackedLanes)

/-- The signedness is absent exactly at the unpacked lane types. -/
theorem extractB_eq_true (sh : Shape) (sx : Option Signedness) :
    extractB sh sx = true ↔ sx.isSome = decide (sh.laneWidth < 32) := by
  rcases sh with s | s <;> cases s <;> cases sx <;>
    simp [extractB, Vec.laneTypeV, Vec.intLaneV, Vec.floatLaneV, Shape.laneWidth,
      IntShape.laneWidth, FloatShape.laneWidth, caseNilV]

/-- **`VEXTRACT_LANE`'s premise evaluates to `extractB`.** -/
theorem evalExp_extractPrem (sh : Shape) (sx : Option Signedness) (i : LaneIdx) :
    EvalExp (simEnv B) (extractScope sh sx i) extractPremE (.bool (extractB sh sx)) := by
  have h₁ : EvalExp (simEnv B) (extractScope sh sx i) (.iterE (.varE "sx")
      (.mk .opt [.mk "sx" (.varE "sx?")])) (.opt (sx.map Vec.sxV)) :=
    IntNumeric.evalExp_iterOpt (by simp [caseScope, typBinds])
      (fun w hw => ⟨w, hw, evalExp_var rfl⟩) id
  have h₂ : EvalExp (simEnv B) (extractScope sh sx i)
      (.memE (.callE "lanetype" [.expA (.varE "shape")]) unpackedLanes)
      (.bool ([caseNilV "I32", caseNilV "I64", caseNilV "F32", caseNilV "F64"].contains
        (Vec.laneTypeV sh))) :=
    evalExp_memE_iff.2 ⟨_, _, evalExp_lanetypeOf sh (by simp [caseScope, typBinds]) rfl,
      evalExp_unpackedLanes, rfl⟩
  have h₃ : EvalExp (simEnv B) (extractScope sh sx i) (.cmpE .eqOp .boolT (.iterE (.varE "sx")
      (.mk .opt [.mk "sx" (.varE "sx?")])) (.optE none))
      (.bool (Value.opt (sx.map Vec.sxV) == Value.opt none)) :=
    evalExp_cmpE_iff.2 ⟨_, _, h₁, evalExp_optE_none_iff.2 rfl, rfl⟩
  exact evalExp_binE_iff.2 ⟨_, h₃, .inr ⟨rfl, _, h₂, rfl⟩⟩

set_option maxRecDepth 100000 in
/-- `VEXTRACT_LANE` with a signedness exactly at packed lanes. -/
theorem typedV_vecExtractLane {sh : Shape} {sx : Option Signedness} {i : LaneIdx}
    (hsx : sx.isSome = decide (sh.laneWidth < 32)) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecExtractLane sh sx i)) := by
  have hopt : HasTyp (simEnv B) (VarEnv.empty.bindVal "shape" (Vec.shapeV sh))
      (.iterT (.varT "sx" []) .opt) (.opt (sx.map Vec.sxV)) := by
    rcases sx with _ | x
    · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, typedV_vsx x _ ⟨rfl, rfl, rfl⟩⟩)
  have hp : EvalExp (simEnv B) (extractScope sh sx i) extractPremE (.bool true) :=
    (extractB_eq_true sh sx).2 hsx ▸ evalExp_extractPrem sh sx i
  exact typedV_instrCaseP rfl rfl (hasTyp_triple (hasTyp_shape0 sh) hopt
    (typedV_laneidx i _ ⟨rfl, rfl, rfl⟩)) (IntNumeric.premsOk_if hp)

/-- `$lsize($lanetype(x.0))` for an `ishape` bound to `x`. -/
theorem evalExp_lsizeOfIsh {ρ : VarEnv} {x : IL.Id} {s : IntShape}
    (h : ρ.findVal? x = some (Vec.ishapeV s)) (hd₁ : ρ.findDef? "lsize" = none)
    (hd₂ : ρ.findDef? "lanetype" = none) :
    EvalExp (simEnv B) ρ (.callE "lsize" [.expA (.callE "lanetype"
      [.expA (.projE (.uncaseE (.varE x) "%") 0)])]) (natV s.laneWidth) :=
  Vec.evalExp_call hd₁ (evalArgs_cons (Vec.evalExp_call hd₂ (evalArgs_cons
    (evalExp_projE_iff.2 ⟨[Vec.shapeV (.int s)], evalExp_uncaseE_iff.2 (evalExp_var h),
      le_refl _, rfl⟩) evalArgs_nil) (applies_lanetype (.int s))) evalArgs_nil)
    (applies_lsize' (.int s))

/-- The payload of `VNARROW`. -/
abbrev narrowTup : Typ :=
  .tupT [.mk "ishape_1" (.varT "ishape" []), .mk "ishape_2" (.varT "ishape" []),
    .mk "sx" (.varT "sx" [])]

set_option maxRecDepth 100000 in
/-- `VNARROW` at a pair Core accepts. -/
theorem typedV_vecNarrow {s t : IntShape} (x : Signedness)
    (hv : s.laneWidth = 2 * t.laneWidth ∧ s.laneWidth ≤ 32) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecNarrow s t x)) := by
  let σ := caseScope VarEnv.empty narrowTup (.tuple [Vec.ishapeV t, Vec.ishapeV s, Vec.sxV x])
  have hS : EvalExp (simEnv B) σ (.callE "lsize" [.expA (.callE "lanetype"
      [.expA (.projE (.uncaseE (.varE "ishape_2") "%") 0)])]) (natV s.laneWidth) :=
    evalExp_lsizeOfIsh (by simp [σ, caseScope, typBinds]) rfl rfl
  have hT : EvalExp (simEnv B) σ (.callE "lsize" [.expA (.callE "lanetype"
      [.expA (.projE (.uncaseE (.varE "ishape_1") "%") 0)])]) (natV t.laneWidth) :=
    evalExp_lsizeOfIsh (by simp [σ, caseScope, typBinds]) rfl rfl
  have h32 : 2 * t.laneWidth ≤ 32 := hv.1 ▸ hv.2
  exact typedV_instrCaseP rfl rfl (hasTyp_triple (typedV_ishape t _ empty_valsOnly)
    (typedV_ishape s _ ⟨rfl, rfl, rfl⟩) (typedV_vsx x _ ⟨rfl, rfl, rfl⟩))
    (IntNumeric.premsOk_if (evalExp_andT
      (evalExp_cmpTrue hS (evalExp_mulLit 2 hT) (cmpValues_eq' hv.1))
      (evalExp_cmpTrue (evalExp_mulLit 2 hT) evalExp_num (cmpValues_le _ _ h32))))

/-! ## `SimdTypingSel` -/

/-- **Every SIMD instruction Core accepts that is bounded and not `FloatMissel` is typed.** -/
theorem typedV_of_vectorOk {C : Context} {i : Instr} {it : InstrType}
    (h : VectorInstrOk C i it) (hs : Pos.InstrSimd i = true) (hm : FloatMissel i = false) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  cases h with
  | vecConst b => exact absurd hs (by simp [Pos.InstrSimd])
  | vecUnOp op => exact typedV_bitwise _ (.inl ⟨op, rfl⟩)
  | vecBinOp op => exact typedV_bitwise _ (.inr (.inl ⟨op, rfl⟩))
  | vecTernOp op => exact typedV_bitwise _ (.inr (.inr (.inl ⟨op, rfl⟩)))
  | vecTestOp op => exact typedV_bitwise _ (.inr (.inr (.inr ⟨op, rfl⟩)))
  | vecIntUnOp hv => exact typedV_vecIntUnOp hv
  | vecFloatUnOp sh op => exact typedV_vecFloatUnOp hm
  | vecIntBinOp hv => exact typedV_vecIntBinOp hv
  | vecFloatBinOp sh op => exact typedV_vecFloatBinOp hm
  | vecIntTernOp sh op => exact typedV_vecIntTernOp sh op
  | vecFloatTernOp sh op => exact absurd hm (by simp [FloatMissel])
  | vecAllTrue sh => exact typedV_vecAllTrue sh
  | vecIntRelOp hv => exact typedV_vecIntRelOp hv
  | vecFloatRelOp sh op => exact typedV_vecFloatRelOp hm
  | vecShiftOp sh op => exact typedV_vecShiftOp sh op
  | vecBitmask sh => exact typedV_vecBitmask sh
  | vecSwizzle op => exact typedV_vecSwizzle op
  | vecShuffle hlen _ => exact typedV_vecShuffle hlen
  | vecSplat sh => exact typedV_vecSplat sh
  | vecExtractLane _ hsx => exact typedV_vecExtractLane hsx
  | vecReplaceLane _ => exact typedV_vecReplaceLane _ _
  | vecExtUnOp hv => exact typedV_vecExtUnOp hv
  | vecExtBinOp hv => exact typedV_vecExtBinOp hv
  | vecExtTernOp hv => exact typedV_vecExtTernOp hv
  | vecNarrow hv => exact typedV_vecNarrow _ hv
  | vecConvert hv => exact typedV_vecConvert hv hm

/-- A SIMD instruction is accepted by Core's vector family. -/
theorem vectorOk_of_instrOk {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (hs : Pos.InstrSimd i = true) (hb : Round4.instrBnd i = true) :
    VectorInstrOk C i it := by
  cases h with
  | vector hp => exact hp
  | parametric hp => cases hp <;> simp [Pos.InstrSimd] at hs
  | numeric hp => cases hp <;> simp [Pos.InstrSimd] at hs
  | «variable» hp => cases hp <;> simp [Pos.InstrSimd] at hs
  | memory hp => cases hp <;> simp [Pos.InstrSimd, Round4.instrBnd] at hs hb
  | table hp => cases hp <;> simp [Pos.InstrSimd] at hs
  | reference hp => cases hp <;> simp [Pos.InstrSimd] at hs
  | _ => simp [Pos.InstrSimd] at hs

/-- **The restated SIMD typing holds**, for every `B`. -/
theorem simdTypingSel (B : Builtins) : SimdTypingSel B := fun _ _ _ hok hb hs hm =>
  typedV_of_vectorOk (vectorOk_of_instrOk hok hs hb) hs hm

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
