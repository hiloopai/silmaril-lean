module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadOob
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StateF

/-!
# Round 7, memory SIMD: the out-of-bounds vector loads, backward (`Step_read` 42, 44, 46, 48, 50)

If an out-of-bounds load rule fires at the image of a vector load (encoded by `instrToVM`), the
result is `TRAP`, and Core's `vecLoadOob` (resp. `vecLoadLaneOob`) steps there. The access width
is bound by the instruction's left-hand side (`N` of `SPLAT N`, `ZERO N`, `VLOAD_LANE N`, or `K`
and `M` of `SHAPE K X M _ sx`), and the bound premise reads `$mem(z, x).BYTES`, inverted by
`memPrem_invF` (round 5's `BwdPureStep.memPrem_inv` at `stateVF`) for a `B` that does not
interpret `$mem`. Since pass 6 the leaves are stated at `stateVF F s f` (any `FUNCS` value), so
they apply at `stateV` and at `stateVD` alike.

* `bwd_vloadOob`: rules 42, 44, 46, 48 at `vecLoad op`, the rule being `oobRule op`; a rule that
  does not match `op`'s shape cannot fire, so this covers every out-of-bounds load rule.
* `bwd_vloadLaneOob`: rule 50 at `vecLoadLane`.
* `bwdB_vloadOob`, `bwdB_vloadLaneOob`: the same at round 6's backend reading.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)

variable {B : Builtins} {H : Type} {hn : H → String} {F : Value}

/-- A firing `Step_read` rule of the form `z; l ~> rh`, inverted. -/
theorem fires_cfg_read {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {z : Value} {l : List Value} {w : Value}
    (h : HasRuleAt env "Step_read" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires env "Step_read" k (.tuple [cfgV z l, w])) :
    ∃ σ, (VarEnv.empty.bindVals σ).findVal? "z" = some z ∧
      EvalExps env (VarEnv.empty.bindVals σ) es l ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env "Step_read" [] k (.tuple [cfgV z l, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, -, he, hp⟩ := State.Fires.rule_eq h hf
  obtain ⟨hz, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  exact ⟨σ, evalExp_varE_iff.1 hz, RefsGC.elems_of_list hc, RefsGC.rhs_of_concl he, hp⟩

/-- The operands of a `VLOAD` element of a left-hand side: the option, `x` and `ao`. -/
theorem vload_fvs {env : Env} {ρ : VarEnv} {eo : Exp} {o : Option Value} {n : Nat}
    {arg : MemArg}
    (h : EvalExp env ρ (.caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []), eo, .varE "x",
      .varE "ao"])) (vloadV o n arg)) :
    EvalExp env ρ eo (.opt o) ∧ ρ.findVal? "x" = some (idxV n) ∧
      ρ.findVal? "ao" = some (memargV arg) := by
  have hx := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv h))).2
  have hx₂ := RefsGC.evalExps_cons_inv hx
  have hx₃ := RefsGC.evalExps_cons_inv hx₂.2
  exact ⟨hx₂.1, evalExp_varE_iff.1 hx₃.1,
    evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hx₃.2).1⟩

/-- The operands `N`, `x`, `ao` of a `VLOAD_LANE` element of a left-hand side. -/
theorem vloadLane_fvs {env : Env} {ρ : VarEnv} {w n : Nat} {arg : MemArg} {j : Nat}
    (h : EvalExp env ρ (.caseE "VLOAD_LANE" (.tupE [.caseE "V128" (.tupE []),
      .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])) (vloadLaneV w n arg j)) :
    ρ.findVal? "N" = some (.num (.natN w)) ∧ ρ.findVal? "x" = some (idxV n) ∧
      ρ.findVal? "ao" = some (memargV arg) := by
  have hx₂ := RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2
  have hx₃ := RefsGC.evalExps_cons_inv hx₂.2
  exact ⟨evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv hx₂.1))).1, evalExp_varE_iff.1 hx₃.1,
    evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hx₃.2).1⟩

/-- `C (%(N))` (or `C %(N)` with a bare payload) inside an option binds `N`. -/
theorem optPct_N {env : Env} {ρ : VarEnv} {C : MixopS} {w : Nat}
    (h : EvalExp env ρ (.optE (some (.caseE C (.caseE "%" (.tupE [.varE "N"])))))
      (.opt (some (.case C (pctV w))))) :
    ρ.findVal? "N" = some (.num (.natN w)) := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  have hu' : u = .case C (pctV w) := by simpa using he.symm
  exact evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv
    (RefsGC.case_inv (hu' ▸ hu))))).1

/-- `ZERO (%(N))` inside an option binds `N`. -/
theorem optZero_N {env : Env} {ρ : VarEnv} {w : Nat}
    (h : EvalExp env ρ (.optE (some (.caseE "ZERO" (.tupE [.caseE "%" (.tupE [.varE "N"])]))))
      (.opt (some (.case "ZERO" (.tuple [pctV w]))))) :
    ρ.findVal? "N" = some (.num (.natN w)) := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  have hu' : u = .case "ZERO" (.tuple [pctV w]) := by simpa using he.symm
  have h₁ := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv (hu' ▸ hu)))).1
  exact evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv h₁))).1

/-- `SHAPE (%(K)) X M _ sx` inside an option binds `K` and `M`. -/
theorem optShape_KM {env : Env} {ρ : VarEnv} {k m : Nat} {sv : Value}
    (h : EvalExp env ρ (.optE (some (.caseE "SHAPE%X%_%" (.tupE [.caseE "%" (.tupE [.varE "K"]),
      .varE "M", .varE "sx"])))) (.opt (some (.case "SHAPE%X%_%" (.tuple [pctV k, pctV m, sv]))))) :
    ρ.findVal? "K" = some (.num (.natN k)) ∧ ρ.findVal? "M" = some (pctV m) := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  have hu' : u = .case "SHAPE%X%_%" (.tuple [pctV k, pctV m, sv]) := by simpa using he.symm
  have hs := RefsGC.elems_of_tup (RefsGC.case_inv (hu' ▸ hu))
  have h₁ := RefsGC.evalExps_cons_inv hs
  exact ⟨evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv h₁.1))).1, evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv h₁.2).1⟩

/-- **The common core of the out-of-bounds loads, backward**: the bound premise at a resolved
width gives the memory and Core's bound. -/
theorem oobPrem_inv (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx} {I K : Nat} {arg : MemArg}
    {ew : Exp} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (hw : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ew (.num (.natN K)))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT) (.binE .addOp
      (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ew)
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true)) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr I arg + K := by
  have hN := RefsGC.evalExp_addNat (env := simEnv B) (t := .numT .natT)
    (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao)) hw
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_invF B hb ⟨rfl, rfl, rfl⟩ fz fx hN h
  exact ⟨ma, mi, by simp [Store.mem?, hma, hmi], by simpa [effAddr] using hlt⟩

/-- The rule number of the out-of-bounds load at `op`'s shape. -/
def oobRule : VecLoadOp → Nat
  | .full => 42
  | .extend8x8 _ | .extend16x4 _ | .extend32x2 _ => 44
  | .splat _ => 46
  | .zero32 | .zero64 => 48

/-! ## The five rules, backward -/

section Rules

variable (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {s : Store H} {f : Frame}
  {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {w : Value}

/-- The `TRAP` right-hand side. -/
theorem rhs_trap {ρ : VarEnv} (h : EvalExp (simEnv B) ρ (.listE [.caseE "TRAP" (.tupE [])]) w) :
    w = .list [.case "TRAP" (.tuple [])] :=
  EvalExp.unique h (by beval)

include hb in
/-- **`Step_read/vload-num-oob`, backward.** -/
theorem bwd_vloadNumOob
    (hf : Fires (simEnv B) "Step_read" 42 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV none x.toNat arg], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr i.toNat arg + 16 := by
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg_read (State.hasReadRules_simEnv B).vloadNumOob hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  obtain ⟨-, fx, fao⟩ := vload_fvs (RefsGC.evalExps_cons_inv h₁.2).1
  exact ⟨rhs_trap hr, oobPrem_inv hb fz fx (fi_of_aconst h₁.1) fao evalExp_vsize8
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))⟩

include hb in
/-- **`Step_read/vload-pack-oob`, backward**, at `SHAPE k X m _ sx` with `k * m = 64`. -/
theorem bwd_vloadPackOob {k m : Nat} (hkm : k * m = 64) {sv : Value}
    (hf : Fires (simEnv B) "Step_read" 44 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat,
        vloadV (some (.case "SHAPE%X%_%" (.tuple [pctV k, pctV m, sv]))) x.toNat arg], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr i.toNat arg + 8 := by
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg_read (State.hasReadRules_simEnv B).vloadPackOob hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  obtain ⟨ho, fx, fao⟩ := vload_fvs (RefsGC.evalExps_cons_inv h₁.2).1
  obtain ⟨fK, fM⟩ := optShape_KM ho
  have hw : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.binE .divOp (.numT .ratT)
      (.cvtE (.binE .mulOp (.numT .natT) (.varE "K") (.projE (.uncaseE (.varE "M") "%") 0))
        .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN 8)) :=
    Memory.evalExp_div8 (w := 64) (by decide)
      (hkm ▸ RefsGC.evalExp_mulNat (evalExp_var fK) (RefsGC.evalExp_unpct (evalExp_var fM)))
  exact ⟨rhs_trap hr, oobPrem_inv hb fz fx (fi_of_aconst h₁.1) fao hw
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))⟩

include hb in
/-- **`Step_read/vload-splat-oob`, backward.** -/
theorem bwd_vloadSplatOob {p : PackSize}
    (hf : Fires (simEnv B) "Step_read" 46 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV (some (.case "SPLAT" (szV p))) x.toNat arg],
      w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr i.toNat arg + p.width / 8 := by
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg_read (State.hasReadRules_simEnv B).vloadSplatOob hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  obtain ⟨ho, fx, fao⟩ := vload_fvs (RefsGC.evalExps_cons_inv h₁.2).1
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  exact ⟨rhs_trap hr, oobPrem_inv hb fz fx (fi_of_aconst h₁.1) fao
    (Memory.evalExp_div8 hw8 (evalExp_var (optPct_N ho)))
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))⟩

include hb in
/-- **`Step_read/vload-zero-oob`, backward**, at `ZERO N` with `N ∈ {32, 64}`. -/
theorem bwd_vloadZeroOob {N : Nat} (hN : N = 32 ∨ N = 64)
    (hf : Fires (simEnv B) "Step_read" 48 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV (some (.case "ZERO" (.tuple [pctV N]))) x.toNat
        arg], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr i.toNat arg + N / 8 := by
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg_read (State.hasReadRules_simEnv B).vloadZeroOob hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  obtain ⟨ho, fx, fao⟩ := vload_fvs (RefsGC.evalExps_cons_inv h₁.2).1
  exact ⟨rhs_trap hr, oobPrem_inv hb fz fx (fi_of_aconst h₁.1) fao
    (Memory.evalExp_div8 (by omega) (evalExp_var (optZero_N ho)))
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))⟩

include hb in
/-- **`Step_read/vload_lane-oob`, backward.** -/
theorem bwd_vloadLaneOobV {p : PackSize} {l : Nat} {c : BitVec 128}
    (hf : Fires (simEnv B) "Step_read" 50 (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vconstV c, vloadLaneV p.width x.toNat arg l], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes.size < effAddr i.toNat arg + p.width / 8 := by
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg_read (State.hasReadRules_simEnv B).vloadLaneOob hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  obtain ⟨fN, fx, fao⟩ := vloadLane_fvs
    (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv h₁.2).2).1
  have hw8 : p.width = 8 ∨ p.width = 16 ∨ p.width = 32 ∨ p.width = 64 := by
    cases p <;> simp [PackSize.width]
  exact ⟨rhs_trap hr, oobPrem_inv hb fz fx (fi_of_aconst h₁.1) fao
    (Memory.evalExp_div8 hw8 (evalExp_var fN)) (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))⟩

end Rules

/-! ## In Core's terms -/

section Core

variable (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {P : Numerics.Profile}
  {host : HostSemantics H} {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
  {i : BitVec a.intType.width} {w : Value}

include hb in
/-- The rule `oobRule op`, backward, with Core's access width. -/
theorem bwd_oobRule {op : VecLoadOp}
    (hf : Fires (simEnv B) "Step_read" (oobRule op) (.tuple [cfgV (stateVF F s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV (Round6.MemSimd.vecLoadOpV op) x.toNat arg],
      w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧ ∃ ma mi, s.mem? f x = some (ma, mi) ∧
      mi.bytes.size < effAddr i.toNat arg + op.accessWidth / 8 := by
  cases op with
  | full => exact bwd_vloadNumOob hb hf
  | extend8x8 sx => simpa [VecLoadOp.accessWidth] using bwd_vloadPackOob hb (k := 8) (m := 8) rfl hf
  | extend16x4 sx =>
      simpa [VecLoadOp.accessWidth] using bwd_vloadPackOob hb (k := 16) (m := 4) rfl hf
  | extend32x2 sx =>
      simpa [VecLoadOp.accessWidth] using bwd_vloadPackOob hb (k := 32) (m := 2) rfl hf
  | splat p => exact bwd_vloadSplatOob hb hf
  | zero32 => exact bwd_vloadZeroOob hb (.inl rfl) hf
  | zero64 => exact bwd_vloadZeroOob hb (.inr rfl) hf

include hb in
/-- **The out-of-bounds vector loads, backward**: if the out-of-bounds rule at `op`'s shape
fires at the image of `v128.load…`, the result is `TRAP` and Core's `vecLoadOob` steps there. -/
theorem bwd_vloadOob {op : VecLoadOp}
    (hf : Fires (simEnv B) "Step_read" (oobRule op) (.tuple [cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, [.trap]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecLoad] at hf
  obtain ⟨hw, ma, mi, hm, hlt⟩ := bwd_oobRule hb hf
  exact ⟨hw, .memory (.vecLoadOob hm hlt)⟩

include hb in
/-- **`Step_read/vload_lane-oob`, backward, in Core's terms.** -/
theorem bwd_vloadLaneOob {sz : PackSize} {j : LaneIdx} {c : BitVec 128}
    (hf : Fires (simEnv B) "Step_read" 50 (.tuple [cfgV (stateVF F s f)
      [adminToV (aconst a i), valV (.vec c), Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)],
      w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecLoadLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecLoadLane] at hf
  obtain ⟨hw, ma, mi, hm, hlt⟩ := bwd_vloadLaneOobV hb hf
  exact ⟨hw, .memory (.vecLoadLaneOob hm hlt)⟩

end Core

/-! ## At the backend reading and the concrete primitives -/

section Backend

variable {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {x : MemIdx}
  {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {w : Value}

/-- **The out-of-bounds vector loads at round 6's backend reading, backward**, at the concrete
primitives. -/
theorem bwdB_vloadOob {op : VecLoadOp}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read"
      (oobRule op) (.tuple [cfgV (stateVF F s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecLoad op x arg)]⟩ ⟨s, f, [.trap]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f)
      [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad op x arg)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoad]; exact lhsIn_vload _ _ _ _ _ _
  exact bwd_vloadOob (call_mem_vb (P := P) (host := host))
    ((Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf)

/-- **`Step_read/vload_lane-oob` at round 6's backend reading, backward.** -/
theorem bwdB_vloadLaneOob {sz : PackSize} {j : LaneIdx} {c : BitVec 128}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step_read" 50
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)], w])) :
    w = .list [.case "TRAP" (.tuple [])] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecLoadLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩ := by
  have ha : RefsGC.LhsIn loadTags (cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
      Round6.MemSimd.instrToVM (.vecLoadLane sz x arg j)]) := by
    rw [State.adminToV_aconst, instrToVM_vecLoadLane]; exact lhsIn_vloadLane _ _ _ _ _ _ _ _
  exact bwd_vloadLaneOob (call_mem_vb (P := P) (host := host))
    ((Round6.Reading.firesB_read_iff _ loadTags_noCast ha).1 hf)

end Backend

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
