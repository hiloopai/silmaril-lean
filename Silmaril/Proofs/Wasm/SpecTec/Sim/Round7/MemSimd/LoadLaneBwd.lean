module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadSplatBwd

/-!
# Round 7, memory SIMD: `v128.loadN_lane`, in bounds (`Step_read` 51), backward

Read back at `withVBytes (Prims.builtins …)`: the update `$lanes_(Jnn X M, c_1)[[j] = %(k.0)]`
succeeds only at an in-range lane, `$lanes_` answers only at the image of a shape (`lanes_inv`),
and `$inv_lanes_` only at the image of that shape's lanes (`invLanes_inv`). The new lane is a
`%`-numeral, so the shape is an integer shape `s` (`laneV_pct`); `N = $jsize(Jnn)` makes the
instruction's pack size `packOf s`, and `$ibytes_(N, k)` makes `k` Core's loaded word.

* `updLanes_inv`, `lanePrem_inv`: the fourth premise, inverted.
* `bwd_vloadLaneVal`, `bwdB_vecLoadLane`: if rule 51 fires at the image of a lane load, the
  result is the image of Core's lane replacement, and Core's `vecLoadLaneVal` steps there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (invLanes)
open State (aconstV idxV)
open FwdMem (leBytesV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H} {F : Value}

/-- The shape `Jnn X M` of the lane rules. -/
abbrev shapeE : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])

/-- `$lanes_(Jnn X M, c_1)[[j] = %(k.0)]`. -/
abbrev updLanesE : Exp :=
  .updE (.callE "lanes_" [.expA shapeE, .expA (.varE "c_1")])
    (.idxP .rootP (.projE (.uncaseE (.varE "j") "%") 0))
    (.caseE "%" (.tupE [.projE (.uncaseE (.varE "k") "%") 0]))

/-- **The lane update, inverted**: at a shape image `shapeV sh` for `Jnn X M`, the update is the
lanes of `c₁` with lane `l` set to `k`, and `l` is in range. -/
theorem updLanes_inv {σ : List (IL.Id × Value)} {sh : Shape} {c₁ : BitVec 128} {l kk : Nat}
    {u : Value}
    (eSh : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      shapeE (Vec.shapeV sh))
    (fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV l))
    (fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (pctV kk))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      updLanesE u) :
    l < (Round5.Simd.lanesV sh c₁).length ∧
      u = .list ((Round5.Simd.lanesV sh c₁).set l (pctV kk)) := by
  obtain ⟨base, nv, eB, eN, hps⟩ := evalExp_updE_iff.1 h
  obtain ⟨u₁, u₂, eu₁, eu₂, hL⟩ := applies_of_call2 ⟨rfl, rfl, rfl⟩ eB
  obtain rfl := EvalExp.unique eu₁ eSh
  obtain rfl := EvalExp.unique eu₂ (evalExp_var fc)
  obtain ⟨sh', hsh, rfl⟩ := lanes_inv hL
  obtain rfl := Round5.Simd.shapeV_injective hsh
  have hnv : nv = pctV kk := EvalExp.unique eN (evalExp_case (RefsGC.evalExp_tupE_of
    (RefsGC.evalExps_cons' (RefsGC.evalExp_unpct (evalExp_var fk)) RefsGC.evalExps_nil')))
  obtain ⟨l', el, hset⟩ := Round5.Simd.pathSet_idxRoot_inv hps
  have hl : l' = l := by
    simpa using EvalExp.unique el (RefsGC.evalExp_unpct (evalExp_var fj))
  subst hl hnv
  simp only [Value.setIdx] at hset
  split at hset
  · exact ⟨by assumption, (Option.some.inj hset).symm⟩
  · cases hset

/-- **The fourth premise of rule 51, inverted**: `Jnn` is the lane type of an integer shape `s`,
the lane is in range, and `c` is the pattern whose lanes are `c₁`'s with lane `l` set to `k`. -/
theorem lanePrem_inv {σ : List (IL.Id × Value)} {c₁ : BitVec 128} {l kk : Nat} {C : Value}
    (fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV l))
    (fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (pctV kk))
    (h : EvalExp (simEnv (withVBytes (Prims.builtins P hn host))) (VarEnv.empty.bindVals σ)
      (.callE "inv_lanes_" [.expA shapeE, .expA updLanesE]) C) :
    ∃ (s : IntShape) (v : BitVec 128),
      (VarEnv.empty.bindVals σ).findVal? "Jnn" = some (Vec.intLaneV s) ∧ l < s.lanes ∧
      Round5.Simd.lanesV (.int s) v = (Round5.Simd.lanesV (.int s) c₁).set l (pctV kk) ∧
      C = Vec.vecV v := by
  obtain ⟨v₁, v₂, e₁, e₂, hA⟩ := applies_of_call2 ⟨rfl, rfl, rfl⟩ h
  obtain ⟨sh, v, rfl, rfl, rfl⟩ := invLanes_inv hA
  obtain ⟨hl, hu⟩ := updLanes_inv e₁ fc fj fk e₂
  have hlv : Round5.Simd.lanesV sh v = (Round5.Simd.lanesV sh c₁).set l (pctV kk) :=
    Value.list.inj hu
  have hget : (Round5.Simd.lanesV sh v)[l]? = some (pctV kk) := by
    rw [hlv, List.getElem?_set_self hl]
  simp only [Round5.Simd.lanesV, List.getElem?_map] at hget
  obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 hget
  obtain ⟨s, rfl⟩ := laneV_pct hx
  obtain ⟨u, hu', hv⟩ := evalExp_caseE_iff.1 e₁
  obtain ⟨Jv, Mv, rfl, hJ, -⟩ := Vec.inv_tup2 hu'
  have hJM : Vec.laneTypeV (.int s) = Jv ∧ pctV (Shape.int s).lanes = Mv := by
    simpa using (Vec.shapeV_eq (.int s)).symm.trans hv
  have fJ : (VarEnv.empty.bindVals σ).findVal? "Jnn" = some (Vec.intLaneV s) := by
    rw [evalExp_varE_iff.1 (evalExp_subE_iff.1 hJ), ← hJM.1]; rfl
  refine ⟨s, v, fJ, ?_, hlv, rfl⟩
  simpa [Round5.Simd.lanesV, Shape.lanesOf, Shape.lanes] using hl

/-- The operand `j` of a `VLOAD_LANE` element of a left-hand side. -/
theorem vloadLane_fj {env : Env} {ρ : VarEnv} {w n : Nat} {arg : MemArg} {j : Nat}
    (h : EvalExp env ρ (.caseE "VLOAD_LANE" (.tupE [.caseE "V128" (.tupE []),
      .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])) (vloadLaneV w n arg j)) :
    ρ.findVal? "j" = some (pctV j) := by
  have hx₂ := RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2
  have hx₃ := RefsGC.evalExps_cons_inv hx₂.2
  exact evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hx₃.2).2).1

/-- **A firing `Step_read` rule at `CONST at i; VCONST V128 c_1; VLOAD_LANE V128 N x ao j`,
inverted**, with its quantifier typing: the scope binds the operands. -/
theorem fires_vloadLane_inv {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {rh : Exp}
    {prems : List Prem} {s : Store H} {f : Frame} {A : Value} {I w n l : Nat} {arg : MemArg}
    {c₁ : BitVec 128} {W : Value}
    (h : Equiv.Validation.HasRuleAt env "Step_read" "%~>%" k (.ruleD nm qs "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]), .caseE "VCONST" (.tupE
        [.caseE "V128" (.tupE []), .varE "c_1"]), .caseE "VLOAD_LANE" (.tupE [.caseE "V128"
        (.tupE []), .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])]]), rh])
      prems))
    (hf : Fires env "Step_read" k
      (.tuple [cfgV (stateVF F s f) [aconstV A I, vconstV c₁, vloadLaneV w n arg l], W])) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f) ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I) ∧
      (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN w)) ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV n) ∧
      (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg) ∧
      (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV l) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh W ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env "Step_read" [] k
          (.tuple [cfgV (stateVF F s f) [aconstV A I, vconstV c₁, vloadLaneV w n arg l], W]))
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq h hf
  obtain ⟨hz, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  have h₁ := RefsGC.evalExps_cons_inv (RefsGC.elems_of_list hc)
  have h₂ := RefsGC.evalExps_cons_inv h₁.2
  have h₃ := (RefsGC.evalExps_cons_inv h₂.2).1
  obtain ⟨fN, fx, fao⟩ := vloadLane_fvs h₃
  have fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) :=
    evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
      (RefsGC.elems_of_tup (RefsGC.case_inv h₂.1))).2).1
  exact ⟨σ, hq, evalExp_varE_iff.1 hz, fi_of_aconst h₁.1, fc, fN, fx, fao, vloadLane_fj h₃,
    RefsGC.rhs_of_concl he, hp⟩

/-- The pattern whose lanes are `c₁`'s with lane `l` set to `kk` is Core's lane replacement. -/
theorem eq_setLane_of_lanesV {s : IntShape} {v c₁ : BitVec 128} {l kk : Nat}
    (hk : kk < 2 ^ s.laneWidth)
    (h : Round5.Simd.lanesV (.int s) v = (Round5.Simd.lanesV (.int s) c₁).set l (pctV kk)) :
    v = Shape.invLanes (.int s) ((Shape.lanesOf (.int s) c₁).set l
      (BitVec.ofNat (Shape.int s).laneWidth kk)) := by
  have hk' : (BitVec.ofNat (Shape.int s).laneWidth kk).toNat = kk := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  apply Round5.Simd.lanesV_injective (.int s)
  rw [h, lanesV_setLane, hk']

/-- **`Step_read/vload_lane-val`, backward** (rule 51), at the concrete primitives with
`$vbytes_` answered: the memory resolves, Core's load succeeds at the instruction's width, and
the result is `VCONST` of Core's lane replacement; the pack size is an integer shape's. -/
theorem bwd_vloadLaneVal {p : PackSize} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {c₁ : BitVec 128} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 51
      (.tuple [cfgV (stateVF F s f) [aconstV (Encode.toValue a) i.toNat, vconstV c₁,
        vloadLaneV p.width x.toNat arg j.val], w])) :
    ∃ (sh : IntShape) (ma : Nat) (mi : MemInst) (c : BitVec (8 * (p.width / 8))),
      p = packOf sh ∧ s.mem? f x = some (ma, mi) ∧
      Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (p.width / 8) = some c ∧
      w = .list [.case "VCONST" (.tuple [caseNilV "V128", pctV (Shape.invLanes (.int sh)
        ((Shape.lanesOf (.int sh) c₁).set j.val
          (BitVec.ofNat (Shape.int sh).laneWidth c.toNat))).toNat])] := by
  obtain ⟨σ, hq, fz, fi, fc, fN, fx, fao, fj, hr, hp⟩ :=
    fires_vloadLane_inv (State.hasReadRules_simEnv _).vloadLaneVal hf
  obtain ⟨K, fK, hK⟩ := hq "k" (.varT "iN" [.expA (.varE "N")]) (by simp)
  obtain ⟨kk, rfl, hk⟩ := iN_inv_lt (evalExp_var fN) hK
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  obtain ⟨ma, mi, c, hm, hl, hcn⟩ := ibytesPrem_load hw8 fz fx fi fao fN fK hk
    (RefsGC.premW_if (hp _ List.mem_cons_self))
  obtain ⟨C, eC, eInv⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))))
  obtain ⟨sh, v, fJnn, -, hl', rfl⟩ := lanePrem_inv fc fj fK eInv
  have hpw : p = packOf sh := packOf_of_jsize ⟨rfl, rfl, rfl⟩ fN fJnn
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hk' : kk < 2 ^ sh.laneWidth := by rw [← packOf_width sh, ← hpw]; exact hk
  refine ⟨sh, ma, mi, c, hpw, hm, hl, ?_⟩
  rw [rhs_vconst (evalExp_varE_iff.1 eC) hr, hcn, ← eq_setLane_of_lanesV hk' hl']

/-- Core's lane replacement of a loaded word, at the pack size of an integer shape. -/
theorem vecLoadLaneResult (sh : IntShape) (v : BitVec 128) (l : Nat)
    (c : BitVec (8 * ((packOf sh).width / 8))) :
    invLanes (packOf sh).width ((Numerics.lanes (packOf sh).width (128 / (packOf sh).width) v).set
      l (c.setWidth (packOf sh).width)) =
      Shape.invLanes (.int sh) ((Shape.lanesOf (.int sh) v).set l
        (BitVec.ofNat (Shape.int sh).laneWidth c.toNat)) := by
  cases sh <;>
  · simp only [packOf, PackSize.width]
    congr 2
    exact setWidth_eq_ofNat c

/-- **`v128.loadN_lane` in bounds at round 6's backend reading, backward**, at the concrete
primitives with `$vbytes_` answered: the result is the image of Core's lane replacement, and
Core's `vecLoadLaneVal` steps there. -/
theorem bwdB_vecLoadLane {p : PackSize} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {c₁ : BitVec 128} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 51
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c₁),
        Round6.MemSimd.instrToVM (.vecLoadLane p x arg j)], w])) :
    ∃ v : BitVec 128, w = .list [adminToV (.plain (.vecConst v))] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c₁), .plain (.vecLoadLane p x arg j)]⟩
        ⟨s, f, [.plain (.vecConst v)]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c₁),
      Round6.MemSimd.instrToVM (.vecLoadLane p x arg j)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoadLane]; exact lhsIn_vloadLane _ _ _ _ _ _ _ _
  have hf' := (Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf
  rw [State.adminToV_aconst, instrToVM_vecLoadLane] at hf'
  obtain ⟨sh, ma, mi, c, rfl, hm, hl, rfl⟩ := bwd_vloadLaneVal hf'
  refine ⟨_, ?_, .memory (.vecLoadLaneVal hm hl)⟩
  rw [vecLoadLaneResult]; rfl

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
