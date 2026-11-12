module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.VStoreLane
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StateF

/-!
# Round 7, memory SIMD: the out-of-bounds vector stores, backward (`Step` 22, 24)

If `Step/vstore-oob` (22) or `Step/vstore_lane-oob` (24) fires at the image of a vector store
(encoded by `instrToVM`), the result is the image of the trap configuration, and Core's
`vecStoreOob` (resp. `vecStoreLaneOob`) steps there. The bound premise reads
`$mem(z, x).BYTES`, which evaluates only when the frame's module lists `x` and the store holds the
memory (`memPrem_invF`, round 5's `BwdPureStep.memPrem_inv` at `stateVF`, for a `B` that does
not interpret `$mem`, as `Prims.builtins` does not). The access end is evaluated forward and compared by
`EvalExp.unique`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)

variable {B : Builtins} {H : Type} {hn : H → String} {F : Value}

/-- A firing rule of the form `z; l ~> rh` at an explicit configuration value, inverted. -/
theorem fires_cfg {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp} {rh : Exp}
    {prems : List Prem} {z : Value} {l : List Value} {w : Value}
    (h : HasRuleAt env "Step" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires env "Step" k (.tuple [cfgV z l, w])) :
    ∃ σ, (VarEnv.empty.bindVals σ).findVal? "z" = some z ∧
      EvalExps env (VarEnv.empty.bindVals σ) es l ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env "Step" [] k (.tuple [cfgV z l, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, -, he, hp⟩ := State.Fires.rule_eq h hf
  obtain ⟨hz, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  exact ⟨σ, evalExp_varE_iff.1 hz, RefsGC.elems_of_list hc, RefsGC.rhs_of_concl he, hp⟩

/-- The address operand `CONST at i` binds `i`. -/
theorem fi_of_aconst {env : Env} {ρ : VarEnv} {A : Value} {n : Nat}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
      (.varT "numtype" []), .varE "i"])) (aconstV A n)) :
    ρ.findVal? "i" = some (idxV n) :=
  evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2).1

/-- The operands `N`, `x`, `ao` of a `VSTORE_LANE` element of a left-hand side. -/
theorem vstoreLane_fvs {env : Env} {ρ : VarEnv} {w n j : Nat} {arg : MemArg}
    (h : EvalExp env ρ (.caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []),
      .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])) (vstoreLaneV w n arg j)) :
    ρ.findVal? "N" = some (.num (.natN w)) ∧ ρ.findVal? "x" = some (idxV n) ∧
      ρ.findVal? "ao" = some (memargV arg) := by
  have hx₂ := RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2
  have hx₃ := RefsGC.evalExps_cons_inv hx₂.2
  exact ⟨evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv hx₂.1))).1, evalExp_varE_iff.1 hx₃.1,
    evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hx₃.2).1⟩

/-- **`Step/vstore-oob`, backward**: the result is the trap image, and Core's `vecStoreOob` steps. -/
theorem bwd_vstoreOob (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {w : Value}
    (hf : Fires (simEnv B) "Step" 22 (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i),
      valV (.vec c), Round6.MemSimd.instrToVM (.vecStore x arg)], w])) :
    w = cfgV (stateVF F s f) [adminToV .trap] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s, f, [.trap]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStore] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreOob |> hasRuleAt_simEnv B) hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  have h₃ := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv h₁.2).2).1
  have fi := fi_of_aconst h₁.1
  have hx := RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv h₃))
  have fx := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hx.2).1
  have fao := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hx.2).2).1
  have hN := RefsGC.evalExp_addNat (env := simEnv B) (t := .numT .natT)
    (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao)) (evalExp_vsize8 (B := B) (σ := σ))
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_invF B hb
    ⟨rfl, rfl, rfl⟩ fz fx hN
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have hm : s.mem? f x = some (ma, mi) := by simp [Store.mem?, hma, hmi]
  refine ⟨EvalExp.unique hr (by beval), .memory (.vecStoreOob hm (by simpa [effAddr] using hlt))⟩

/-- **`Step/vstore_lane-oob`, backward.** -/
theorem bwd_vstoreLaneOob (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {sz : PackSize}
    {x : MemIdx} {arg : MemArg} {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width}
    {c : BitVec 128} {w : Value}
    (hf : Fires (simEnv B) "Step" 24 (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i),
      valV (.vec c), Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)], w])) :
    w = cfgV (stateVF F s f) [adminToV .trap] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStoreLane] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreLaneOob |> hasRuleAt_simEnv B)
    hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV i.toNat) := fi_of_aconst h₁.1
  obtain ⟨fN, fx, fao⟩ := vstoreLane_fvs
    (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv h₁.2).2).1
  have hN : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) _ (.num (.natN _)) :=
    RefsGC.evalExp_addNat (t := .numT .natT)
      (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
      (Memory.evalExp_div8 (w := sz.width) (by cases sz <;> simp [PackSize.width])
        (evalExp_var fN))
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_invF B hb ⟨rfl, rfl, rfl⟩ fz fx hN
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have hm : s.mem? f x = some (ma, mi) := by simp [Store.mem?, hma, hmi]
  refine ⟨EvalExp.unique hr (by beval),
    .memory (.vecStoreLaneOob hm (by simpa [effAddr] using hlt))⟩

/-! ## At the backend reading and the concrete primitives -/

/-- `withVBytes (Prims.builtins …)` does not interpret `$mem`. -/
theorem call_mem_vb {P : Numerics.Profile} {host : HostSemantics H} (Z X : Value) :
    (withVBytes (Prims.builtins P hn host)).call "mem" [.val Z, .val X] = none := by
  simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **`Step/vstore-oob` at round 6's backend reading, backward**, at the concrete primitives. -/
theorem bwdB_vstoreOob {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128}
    {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 22
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)], w])) :
    w = cfgV (stateVF F s f) [adminToV .trap] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s, f, [.trap]⟩ :=
  bwd_vstoreOob (call_mem_vb (P := P) (host := host))
    ((Round6.Reading.firesB_step_iff _ (.inr (by decide))).1 hf)

/-- **`Step/vstore_lane-oob` at round 6's backend reading, backward**, at the concrete
primitives. -/
theorem bwdB_vstoreLaneOob {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg} {j : LaneIdx} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {w : Value}
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 24
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)], w])) :
    w = cfgV (stateVF F s f) [adminToV .trap] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s, f, [.trap]⟩ :=
  bwd_vstoreLaneOob (call_mem_vb (P := P) (host := host))
    ((Round6.Reading.firesB_step_iff _ (.inr (by decide))).1 hf)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
