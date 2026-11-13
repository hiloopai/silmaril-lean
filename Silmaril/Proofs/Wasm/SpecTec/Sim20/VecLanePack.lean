module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFwd
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# `Step_pure/vextract_lane-pack` forward, in any environment with the right facts

Rule 47 of the 2.0 `Step_pure`,

  `VCONST V128 c_1; VEXTRACT_LANE (pt X N) sx i ~> CONST I32 c_2`
  `  -- if c_2 = $extend__($psize(pt), 32, sx, $lanes_(pt X N, c_1)[i])`,

is V2's `vecExtractLane` at the packed shapes `i8x16` and `i16x8`. As for rule 46
(`VecFix.ExtractEnv`), the firing argument needs of an environment only the facts collected in
`PackEnv`: the rule, the typing of its six quantifiers, `$psize` at `I8` and `I16`, and the two
clause-free primitives `$lanes_` and `$extend__` answering as V2 computes.

**`fwd_vextractLanePack`**: every V2 pure step from `v128.const c; i8x16.extract_lane_sx i` (or
`i16x8`) is matched by rule 47, from the image of the source to the image of V2's successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV bvV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim20.Whole (shapeV20 lanesV20 jnnV20 getElem?_lanesV20 evalExp_eqTrue)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (pureStep_extract_inv)

/-! ## The rule -/

/-- The shape `pt X N` of the rule. -/
abbrev ptShapeE : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE "pt") (.varT "packtype" []) (.varT "lanetype" []),
    .caseE "%" (.tupE [.varE "N"])])

/-- The premise's right-hand side. -/
abbrev packRhsE : Exp :=
  .callE "extend__" [.expA (.callE "psize" [.expA (.varE "pt")]), .expA (.numE (.natN 32)),
    .expA (.varE "sx"), .expA (.idxE (.callE "lanes_" [.expA ptShapeE, .expA (.varE "c_1")])
      (.projE (.uncaseE (.varE "i") "%") (0 : Int)))]

/-- `Step_pure/vextract_lane-pack`, rule 47 of `Step_pure` (verbatim). -/
def vextractLanePackRule : Rule :=
  .ruleD "vextract_lane-pack" [.expP "c_1" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "pt" (.varT "packtype" []), .expP "N" (.varT "N" []), .expP "sx" (.varT "sx" []),
    .expP "i" (.varT "laneidx" []),
    .expP "c_2" (.varT "num_" [.expA (.caseE "I32" (.tupE []))])] "%~>%"
    (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"]),
        .caseE "VEXTRACT_LANE" (.tupE [ptShapeE, .optE (some (.varE "sx")), .varE "i"])],
      .listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c_2"])]])
    [.ifPr (.cmpE .eqOp .boolT (.varE "c_2") packRhsE)]

/-! ## What the argument needs of an environment -/

/-- The packed lane sizes. -/
def Packed (sz : PackSize) : Prop := sz = .i8 ∨ sz = .i16

/-- **The facts about `env` that make rule 47 fire forward.** -/
structure PackEnv (env : Env) : Prop where
  rule : HasRuleAt env "Step_pure" "%~>%" 47 vextractLanePackRule
  vec : ∀ c : BitVec 128, TypedV env (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV c.toNat)
  packtype : ∀ sz, Packed sz → TypedV env (.varT "packtype" []) (jnnV20 sz)
  N : ∀ k : Nat, TypedV env (.varT "N" []) (.num (.natN k))
  sx : ∀ s, TypedV env (.varT "sx" []) (sxV s)
  laneidx : ∀ j : LaneIdx, TypedV env (.varT "laneidx" []) (pctV j.val)
  num32 : ∀ (x : BitVec 32) (ρ : VarEnv), ValsOnly ρ →
    HasTyp env ρ (.varT "num_" [.expA (.caseE "I32" (.tupE []))]) (pctV x.toNat)
  psize : ∀ sz, Packed sz → ∀ {ρ : VarEnv} {args : List Arg}, ρ.findDef? "psize" = none →
    EvalArgs env ρ args [.val (jnnV20 sz)] → CallDef env ρ "psize" args (natV sz.width)
  lanesDef : ∃ ps t, env.findDef? "lanes_" = some (ps, t, [])
  lanes : ∀ (sz : PackSize) (c : BitVec 128),
    env.builtins.call "lanes_" [.val (shapeV20 sz), .val (pctV c.toNat)] = some (.list (lanesV20 sz c))
  extendDef : ∃ ps t, env.findDef? "extend__" = some (ps, t, [])
  extend : ∀ (N N' : Nat) (s : Signedness) (x : BitVec N),
    env.builtins.call "extend__" [.val (natV N), .val (natV N'), .val (sxV s), .val (pctV x.toNat)] =
      some (bvV (match s with | .signed => x.signExtend N' | .unsigned => x.setWidth N'))

/-! ## The firing -/

/-- The lane `i` of `c` at the packed size `sz`. -/
def packLane (sz : PackSize) (c : BitVec 128) (i : Nat) : BitVec sz.width :=
  (Numerics.lanes sz.width (128 / sz.width) c).getD i 0

/-- The lane extended to `i32`. -/
def packExt (sz : PackSize) (s : Signedness) (c : BitVec 128) (i : Nat) : BitVec 32 :=
  match s with
  | .signed => (packLane sz c i).signExtend 32
  | .unsigned => (packLane sz c i).setWidth 32

/-- The evaluation of the premise's right-hand side, in the rule's scope. -/
theorem evalExp_packRhs {env : Env} (E : PackEnv env) {sz : PackSize} (hp : Packed sz)
    {s : Signedness} {c : BitVec 128} {i : LaneIdx} (hi : i.val < 128 / sz.width)
    {σ : List (IL.Id × Value)}
    (fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat))
    (fp : (VarEnv.empty.bindVals σ).findVal? "pt" = some (jnnV20 sz))
    (fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN (128 / sz.width))))
    (fs : (VarEnv.empty.bindVals σ).findVal? "sx" = some (sxV s))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.val)) :
    EvalExp env (VarEnv.empty.bindVals σ) packRhsE (pctV (packExt sz s c i.val).toNat) := by
  have hρd : ∀ x, (VarEnv.empty.bindVals σ).findDef? x = none := by
    intro x; simp [VarEnv.findDef?, VarEnv.bindVals, VarEnv.empty, Map.empty]
  have eSh : EvalExp env (VarEnv.empty.bindVals σ) ptShapeE (shapeV20 sz) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fp))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2
        ⟨_, _, rfl, evalExp_var fN, Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩)))
  have eLanes : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "lanes_" [.expA ptShapeE, .expA (.varE "c_1")]) (.list (lanesV20 sz c)) := by
    obtain ⟨ps, ty, hdl⟩ := E.lanesDef
    exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil (hρd _) hdl
      (evalArgs_cons eSh (evalArgs_cons (evalExp_var fc) evalArgs_nil)) (E.lanes sz c))
  have eLane : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.callE "lanes_" [.expA ptShapeE, .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") (0 : Int))) (pctV (packLane sz c i.val).toNat) :=
    Sim.RefsGC.evalExp_idx eLanes (Sim.RefsGC.evalExp_unpct (evalExp_var fi))
      (getElem?_lanesV20 sz c hi)
  have ePs : EvalExp env (VarEnv.empty.bindVals σ) (.callE "psize" [.expA (.varE "pt")])
      (natV sz.width) :=
    evalExp_callE_iff.2 (E.psize sz hp (hρd _) (evalArgs_cons (evalExp_var fp) evalArgs_nil))
  obtain ⟨ps, ty, hde⟩ := E.extendDef
  have hb := E.extend sz.width 32 s (packLane sz c i.val)
  refine evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil (hρd _) hde
    (evalArgs_cons ePs (evalArgs_cons evalExp_num (evalArgs_cons (evalExp_var fs)
      (evalArgs_cons eLane evalArgs_nil)))) ?_)
  show env.builtins.call "extend__" [.val (natV sz.width), .val (natV 32), .val (sxV s),
    .val (pctV (packLane sz c i.val).toNat)] = _
  rw [hb]
  cases s <;> rfl

/-- **Rule 47 fires** at `VCONST V128 c; VEXTRACT_LANE (pt X N) sx i`, for a packed lane size,
a lane `i` in range, to `CONST I32` of the extended lane. -/
theorem fires_vextractLanePack {env : Env} (E : PackEnv env) {sz : PackSize} (hp : Packed sz)
    (s : Signedness) (c : BitVec 128) (i : LaneIdx) (hi : i.val < 128 / sz.width) :
    Fires env "Step_pure" 47 (.tuple [
      .list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [shapeV20 sz, .opt (some (sxV s)),
        pctV i.val])],
      .list [.case "CONST" (.tuple [numTypeV (.int .i32), pctV (packExt sz s c i.val).toNat])]]) := by
  let σ : List (IL.Id × Value) := [("c_1", pctV c.toNat), ("pt", jnnV20 sz),
    ("N", .num (.natN (128 / sz.width))), ("sx", sxV s), ("i", pctV i.val),
    ("c_2", pctV (packExt sz s c i.val).toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat) := rfl
  have fp : (VarEnv.empty.bindVals σ).findVal? "pt" = some (jnnV20 sz) := rfl
  have fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN (128 / sz.width))) := rfl
  have fs : (VarEnv.empty.bindVals σ).findVal? "sx" = some (sxV s) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.val) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV (packExt sz s c i.val).toNat) :=
    rfl
  have hq : QuantsOk env (VarEnv.empty.bindVals σ)
      (match vextractLanePackRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fc (E.vec c _ hρ) (QuantsOk.cons fp (E.packtype sz hp _ hρ)
      (QuantsOk.cons fN (E.N _ _ hρ) (QuantsOk.cons fs (E.sx s _ hρ)
        (QuantsOk.cons fi (E.laneidx i _ hρ) (QuantsOk.cons fx (E.num32 _ _ hρ) QuantsOk.nil)))))
  have eSh : EvalExp env (VarEnv.empty.bindVals σ) ptShapeE (shapeV20 sz) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fp))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2
        ⟨_, _, rfl, evalExp_var fN, Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩)))
  have eC : EvalExp env (VarEnv.empty.bindVals σ)
      (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"])) (adminToV (vconst c)) :=
    evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_var fc))
  have hl : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"]),
        .caseE "VEXTRACT_LANE" (.tupE [ptShapeE, .optE (some (.varE "sx")), .varE "i"])])
      (.list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [shapeV20 sz,
        .opt (some (sxV s)), pctV i.val])]) :=
    evalExp_listE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, eC,
      Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
        evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, eSh,
          Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_optE_some_iff.2 ⟨_, evalExp_var fs, rfl⟩,
            Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_var fi,
              Equiv.Validation.evalExps_nil_iff.2 rfl⟩⟩⟩, rfl⟩),
        Equiv.Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
  have hr : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c_2"])])
      (.list [.case "CONST" (.tuple [numTypeV (.int .i32), pctV (packExt sz s c i.val).toNat])]) :=
    evalExp_listE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
      evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        (evalExp_var fx)),
      Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩
  have p₁ : EvalExp env (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT (.varE "c_2") packRhsE)
      (.bool true) :=
    evalExp_eqTrue (evalExp_var fx) (evalExp_packRhs E hp hi fc fp fN fs fi)
  refine Pure.fires_of_ruleAt E.rule σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  have e : pr = .ifPr (.cmpE .eqOp .boolT (.varE "c_2") packRhsE) := List.mem_singleton.1 hpr
  subst e
  exact .ifPr p₁

/-! ## Forward from V2 -/

/-- The only V2 step from `v128.const c; sh.extract_lane sx i`. -/
theorem pureStep_extractSx_inv {P : Numerics.Profile} {sh : Shape} {s : Signedness} {c : BitVec 128}
    {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane sh (some s) i)] code') :
    i.val < sh.lanes ∧
      code' = [(Val.num ⟨sh.unpacked, VecExtractLane sh (some s) i.val c⟩).toAdmin] := by
  generalize hl : [vconst c, Admin.plain (V2.Instr.vecExtractLane sh (some s) i)] = l at h
  cases h with
  | vecExtractLane hi =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecExtractLane.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨hi, rfl⟩
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c, Admin.plain (V2.Instr.vecExtractLane sh (some s) i)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- The integer shape of a pack size. -/
def packShape : PackSize → IntShape
  | .i8 => .i8x16
  | .i16 => .i16x8
  | .i32 => .i32x4
  | .i64 => .i64x2

/-- The image of the source, at a packed shape. -/
theorem adminsToV_extractPack {sz : PackSize} (hp : Packed sz) (s : Signedness) (c : BitVec 128)
    (i : LaneIdx) :
    adminsToV [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)] =
      [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [shapeV20 sz, .opt (some (sxV s)),
        pctV i.val])] := by
  rcases hp with rfl | rfl <;> rfl

/-- The image of V2's successor: `CONST I32` of the extended lane. -/
theorem adminsToV_extractPackRes {sz : PackSize} (hp : Packed sz) (s : Signedness) (c : BitVec 128)
    (i : LaneIdx) :
    adminsToV [(Val.num ⟨(Shape.int (packShape sz)).unpacked,
      VecExtractLane (.int (packShape sz)) (some s) i.val c⟩).toAdmin] =
      [.case "CONST" (.tuple [numTypeV (.int .i32), pctV (packExt sz s c i.val).toNat])] := by
  rcases hp with rfl | rfl <;> cases s <;> rfl

/-- **`vextract_lane` at `i8x16` and `i16x8`, forward**: rule 47 fires from the image of every V2
pure step's source to the image of its successor. -/
theorem fwd_vextractLanePack {env : Env} (E : PackEnv env) {P : Numerics.Profile} {sz : PackSize}
    (hp : Packed sz) {s : Signedness} {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)] code') :
    Fires env "Step_pure" 47 (.tuple [.list (adminsToV [vconst c, .plain (.vecExtractLane
      (.int (packShape sz)) (some s) i)]), .list (adminsToV code')]) := by
  obtain ⟨hi, rfl⟩ := pureStep_extractSx_inv h
  rw [adminsToV_extractPack hp, adminsToV_extractPackRes hp]
  have hi' : i.val < 128 / sz.width := by rcases hp with rfl | rfl <;> exact hi
  exact fires_vextractLanePack E hp s c i hi'

end Silmaril.Wasm.SpecTec.Sim20.VecLane
