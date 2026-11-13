module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# `Step_pure/vextract_lane-num` forward, in any environment with the right facts

Rule 46 of the 2.0 `Step_pure`,

  `VCONST V128 c_1; VEXTRACT_LANE (nt X N) eps i ~> CONST nt c_2  -- if c_2 = $lanes_(nt X N, c_1)[i]`,

is V2's `vecExtractLane` at the two integer shapes whose lanes are numbers, `i32x4` and `i64x2`.
The firing argument needs of an environment only the facts collected in `ExtractEnv`: the rule
itself, the typing of its five quantifiers, and `$lanes_` as a clause-free builtin answering as
V2 computes lanes (`Whole.LaneCalls20`'s `lanes` field). So it is proved once
(**`fwd_vextractLaneNum`**) and instantiated at the original script (`extractEnv20`, in
`VecFixFire20`) and at the corrected one (`extractEnv20V`, in `VecFixFireV`).

**`fwd_vextractLaneNum`**: every V2 pure step from `v128.const c; i32x4.extract_lane i` (or
`i64x2`) is matched by rule 46, from the image of the source to the image of V2's successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim20.Whole (shapeV20 lanesV20 jnnV20 getElem?_lanesV20 evalExp_eqTrue)

/-! ## The rule -/

/-- The shape `nt X N` of the rule. -/
abbrev ntShapeE : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE "nt") (.varT "numtype" []) (.varT "lanetype" []),
    .caseE "%" (.tupE [.varE "N"])])

/-- `Step_pure/vextract_lane-num`, rule 46 of `Step_pure` (verbatim). -/
def vextractLaneNumRule : Rule :=
  .ruleD "vextract_lane-num" [.expP "c_1" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "nt" (.varT "numtype" []), .expP "N" (.varT "N" []), .expP "i" (.varT "laneidx" []),
    .expP "c_2" (.varT "num_" [.expA (.varE "nt")])] "%~>%"
    (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"]),
        .caseE "VEXTRACT_LANE" (.tupE [ntShapeE, .optE none, .varE "i"])],
      .listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c_2"])]])
    [.ifPr (.cmpE .eqOp .boolT (.varE "c_2") (.idxE (.callE "lanes_" [.expA ntShapeE,
      .expA (.varE "c_1")]) (.projE (.uncaseE (.varE "i") "%") (0 : Int))))]

/-! ## What the argument needs of an environment -/

/-- **The facts about `env` that make rule 46 fire forward.** -/
structure ExtractEnv (env : Env) : Prop where
  rule : HasRuleAt env "Step_pure" "%~>%" 46 vextractLaneNumRule
  vec : ∀ c : BitVec 128, TypedV env (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV c.toNat)
  numtype : ∀ t, TypedV env (.varT "numtype" []) (numTypeV t)
  num : ∀ (t : IntType) (x : BitVec t.width), Pure.TypedAt env "num_" "nt" (numTypeV (.int t))
    (pctV x.toNat)
  N : ∀ k : Nat, TypedV env (.varT "N" []) (.num (.natN k))
  laneidx : ∀ j : LaneIdx, TypedV env (.varT "laneidx" []) (pctV j.val)
  lanesDef : ∃ ps t, env.findDef? "lanes_" = some (ps, t, [])
  lanes : ∀ (sz : PackSize) (c : BitVec 128),
    env.builtins.call "lanes_" [.val (shapeV20 sz), .val (pctV c.toNat)] = some (.list (lanesV20 sz c))

/-! ## The firing -/

/-- The integer lane types with number lanes, and their pack sizes. -/
def numPack : IntType → PackSize
  | .i32 => .i32
  | .i64 => .i64

theorem jnnV20_numPack (t : IntType) : jnnV20 (numPack t) = numTypeV (.int t) := by
  cases t <;> rfl

/-- **Rule 46 fires** at `VCONST V128 c; VEXTRACT_LANE (nt X N) eps i`, for an integer number
type `nt`, a lane `i` in range, to `CONST nt` of the lane. -/
theorem fires_vextractLaneNum {env : Env} (E : ExtractEnv env) (t : IntType) (c : BitVec 128)
    (i : LaneIdx) (hi : i.val < 128 / (numPack t).width) :
    Fires env "Step_pure" 46 (.tuple [
      .list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [shapeV20 (numPack t), .opt none,
        pctV i.val])],
      .list [.case "CONST" (.tuple [numTypeV (.int t),
        pctV ((Numerics.lanes (numPack t).width (128 / (numPack t).width) c).getD i.val 0).toNat])]]) := by
  let sz := numPack t
  let x := (Numerics.lanes sz.width (128 / sz.width) c).getD i.val 0
  have hx : x.toNat < 2 ^ t.width := by
    have h := x.isLt
    cases t <;> exact h
  let y : BitVec t.width := BitVec.ofNat _ x.toNat
  have hy : y.toNat = x.toNat := by simp [y, Nat.mod_eq_of_lt hx]
  let σ : List (IL.Id × Value) := [("c_1", pctV c.toNat), ("nt", numTypeV (.int t)),
    ("N", .num (.natN (128 / sz.width))), ("i", pctV i.val), ("c_2", pctV x.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV (.int t)) := rfl
  have fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN (128 / sz.width))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.val) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV x.toNat) := rfl
  have hnum : HasTyp env (VarEnv.empty.bindVals σ) (.varT "num_" [.expA (.varE "nt")])
      (pctV x.toNat) := by
    have h := E.num t y _ hρ ft
    rwa [hy] at h
  have hq : QuantsOk env (VarEnv.empty.bindVals σ)
      (match vextractLaneNumRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fc (E.vec c _ hρ) (QuantsOk.cons ft (E.numtype _ _ hρ)
      (QuantsOk.cons fN (E.N _ _ hρ) (QuantsOk.cons fi (E.laneidx i _ hρ)
        (QuantsOk.cons fx hnum QuantsOk.nil))))
  -- the shape `nt X N`
  have eSh : EvalExp env (VarEnv.empty.bindVals σ) ntShapeE (shapeV20 sz) := by
    have h : EvalExp env (VarEnv.empty.bindVals σ) ntShapeE
        (.case "%X%" (.tuple [numTypeV (.int t), pctV (128 / sz.width)])) :=
      evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var ft))
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2
          ⟨_, _, rfl, evalExp_var fN, Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩)))
    have e : shapeV20 sz = .case "%X%" (.tuple [numTypeV (.int t), pctV (128 / sz.width)]) := by
      simp only [shapeV20, sz, jnnV20_numPack]
    rw [e]
    exact h
  -- the two sides
  have eC : EvalExp env (VarEnv.empty.bindVals σ)
      (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"])) (adminToV (vconst c)) :=
    evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_var fc))
  have hl : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"]),
        .caseE "VEXTRACT_LANE" (.tupE [ntShapeE, .optE none, .varE "i"])])
      (.list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [shapeV20 sz, .opt none,
        pctV i.val])]) :=
    evalExp_listE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, eC,
      Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
        evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, eSh,
          Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_optE_none_iff.2 rfl,
            Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_var fi,
              Equiv.Validation.evalExps_nil_iff.2 rfl⟩⟩⟩, rfl⟩),
        Equiv.Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
  have hr : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c_2"])])
      (.list [.case "CONST" (.tuple [numTypeV (.int t), pctV x.toNat])]) :=
    evalExp_listE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
      evalExp_case (evalExp_tup2 (evalExp_var ft) (evalExp_var fx)),
      Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩
  -- the premise
  have eLanes : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")]) (.list (lanesV20 sz c)) := by
    obtain ⟨ps, ty, hd⟩ := E.lanesDef
    exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil rfl hd
      (evalArgs_cons eSh (evalArgs_cons (evalExp_var fc) evalArgs_nil)) (E.lanes sz c))
  have eLane : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") (0 : Int))) (pctV x.toNat) :=
    Sim.RefsGC.evalExp_idx eLanes (Sim.RefsGC.evalExp_unpct (evalExp_var fi))
      (getElem?_lanesV20 sz c hi)
  have p₁ : EvalExp env (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT (.varE "c_2")
      (.idxE (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") (0 : Int)))) (.bool true) :=
    evalExp_eqTrue (evalExp_var fx) eLane
  refine Pure.fires_of_ruleAt E.rule σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  have e : pr = .ifPr (.cmpE .eqOp .boolT (.varE "c_2")
      (.idxE (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") (0 : Int)))) := List.mem_singleton.1 hpr
  subst e
  exact .ifPr p₁

end Silmaril.Wasm.SpecTec.Sim20.VecFix
