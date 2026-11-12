module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Backward
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.MemSimd.WithMem

/-!
# Round 7, memory SIMD: the in-bounds vector store, backward (`Step` 23)

`Step/vstore-val` writes `$with_mem(z, x, i + ao.OFFSET, 16, b*)` with `b* = $vbytes_(V128, c)`.
The evaluator's slice update succeeds only inside the list, so a firing rule is in bounds
(`withMem_bound'`, round 5's `BwdStep.withMem_bound` for any `B` that does not interpret
`$with_mem`). In bounds, Core's store succeeds, the written bytes are read back through
`$vbytes_` (`VBytes`), and the written state is evaluated forward and compared
(`withMem_store'`).

* `bwd_vstoreVal`: if rule 23 fires at the image of `v128.store` over a memory the frame
  resolves, the result is the image of Core's store and Core's `vecStoreVal` steps there.
* `bwdB_vstoreVal`: the same at round 6's backend reading and `withVBytes (Prims.builtins …)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)
open FwdMem (bytesV leBytesV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (memInstToValue)

variable {B : Builtins} {H : Type} {hn : H → String} {F : Value}

/-- `storeVF` after a memory update (`FwdMem.storeV_setMem` at any function list). -/
theorem storeVF_setMem (F : Value) (s : Store H) (a : Nat) (m : MemInst) :
    (storeVF F s).setField "MEMS" (.list ((s.mems.map memInstToValue).set a (memInstToValue m))) =
      some (storeVF F (s.setMem a m)) := by
  simp [storeVF, Store.setMem, List.map_set]

/-- **A firing `$with_mem(z, x, i + ao.OFFSET, k, b*)`**, with `b*` the `k`-byte encoding of
`w`, at a resolved memory: Core's store of `w` succeeds and the call is its state image (round
5's `BwdStep.withMem_store`, for any `B` that does not interpret `$with_mem`, at `stateVF`). -/
theorem withMem_store' (hwm : ∀ ws, B.call "with_mem" ws = none) {σ : List (IL.Id × Value)}
    {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {ma : Nat} {mi : MemInst} {I k : Nat}
    {w : BitVec (8 * k)} {ej eb : Exp} {W : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateVF F s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV I))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (hm : s.mem? f x = some (ma, mi))
    (hj : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ej (.num (.natN k)))
    (hb : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) eb (.list (leBytesV k w.toNat)))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)), .expA ej, .expA eb]) W) :
    ∃ b, Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr I arg) w = some b ∧
      W = stateVF F (s.setMem ma { mi with bytes := b }) f := by
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hea := Memory.evalExp_effAddr (env := simEnv B) (evalExp_var fi) (evalExp_var fao)
  have hle := withMem_bound' hwm hρ fz fx hm hea hj hb h
  obtain ⟨b, hs⟩ := Round5.BwdStep.store_of_le (w := w) (i := effAddr I arg)
    (by simpa [effAddr] using hle)
  obtain ⟨-, hbv⟩ := FwdMem.store_bytesV hs
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
  have hle' : effAddr I arg + k ≤ mi.bytes.size := by simpa [effAddr] using hle
  have hsl : Value.setSlice (.list (bytesV mi.bytes)) (effAddr I arg) k
      (.list (leBytesV k w.toNat)) = some (.list ((bytesV mi.bytes).take (effAddr I arg) ++
        leBytesV k w.toNat ++ (bytesV mi.bytes).drop (effAddr I arg + k))) := by
    simp [Value.setSlice, hle']
  have ew := FwdMem.evalExp_withMem (ez := .varE "z") (ex := .varE "x")
    (State.stateDefs_simEnv _) (FwdMem.withMemDef_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz) (evalExp_var fx) hea hj hb
    (rfl : (storeVF F s).field? "MEMS" = _) (State.frameV_MODULE f) (State.moduleV_MEMS _)
    (State.getElem?_map_natN hma) (by simp [hmi]) (FwdMem.memInstV_BYTES' mi) hsl
    (hbv ▸ FwdMem.memInstV_setBytes mi b) (storeVF_setMem F s ma _)
  exact ⟨b, hs, EvalExp.unique h ew⟩

/-- The `VCONST V128 c` operand binds `c`. -/
theorem fc_of_vconst {env : Env} {ρ : VarEnv} {c : BitVec 128}
    (h : EvalExp env ρ (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]))
      (vconstV c)) :
    ρ.findVal? "c" = some (pctV c.toNat) :=
  evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2).1

/-- The operands `x`, `ao` of a `VSTORE` element of a left-hand side. -/
theorem vstore_fvs {env : Env} {ρ : VarEnv} {n : Nat} {arg : MemArg}
    (h : EvalExp env ρ (.caseE "VSTORE" (.tupE [.caseE "V128" (.tupE []), .varE "x", .varE "ao"]))
      (vstoreV n arg)) :
    ρ.findVal? "x" = some (idxV n) ∧ ρ.findVal? "ao" = some (memargV arg) := by
  have hx := RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv h))
  exact ⟨evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hx.2).1,
    evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hx.2).2).1⟩

/-- **`Step/vstore-val`, backward**: at a memory the frame resolves, the result is the image of
Core's store, and Core's `vecStoreVal` steps there. -/
theorem bwd_vstoreVal (Vb : VBytes (simEnv B)) (hwm : ∀ ws, B.call "with_mem" ws = none)
    {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat}
    {mi : MemInst} {w : Value} (hm : s.mem? f x = some (ma, mi))
    (hf : Fires (simEnv B) "Step" 23 (.tuple [cfgV (stateV hn s f) [adminToV (aconst a i),
      valV (.vec c), Round6.MemSimd.instrToVM (.vecStore x arg)], w])) :
    ∃ s', w = cfgV (stateV hn s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s', f, []⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStore] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreVal |> hasRuleAt_simEnv B) hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  have h₂ := RefsGC.evalExps_cons_inv h₁.2
  obtain ⟨fx, fao⟩ := vstore_fvs (RefsGC.evalExps_cons_inv h₂.2).1
  have fc := fc_of_vconst h₂.1
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have eV : V = .list (leBytesV 16 c.toNat) := Applies.unique ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly ⟨rfl, rfl, rfl⟩ _) (Equiv.evalArgs_cons evalExp_v128
      (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 e₂)) (Vb c)
  subst eV
  obtain ⟨W, hW, rfl⟩ := BwdPureStep.rhs_nil hr
  obtain ⟨b, hs, rfl⟩ := withMem_store' (w := c) (k := 16) hwm fz fx (fi_of_aconst h₁.1) fao hm
    (evalExp_vsize8 (B := B)) e₁ hW
  exact ⟨_, rfl, .memory (.vecStoreVal hm hs)⟩

/-- `withVBytes (Prims.builtins …)` does not interpret `$with_mem`. -/
theorem call_withMem_vb {P : Numerics.Profile} {host : HostSemantics H} (ws : List ArgV) :
    (withVBytes (Prims.builtins P hn host)).call "with_mem" ws = none := by
  simp [withVBytes, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **`Step/vstore-val` at round 6's backend reading, backward**, at the concrete primitives. -/
theorem bwdB_vstoreVal {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128}
    {ma : Nat} {mi : MemInst} {w : Value} (hm : s.mem? f x = some (ma, mi))
    (hf : Round6.Reading.FiresB (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 23
      (.tuple [cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)], w])) :
    ∃ s', w = cfgV (stateV hn s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s', f, []⟩ :=
  bwd_vstoreVal (vBytes_withVBytes _) call_withMem_vb hm
    ((Round6.Reading.firesB_step_iff _ (.inr (by decide))).1 hf)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
