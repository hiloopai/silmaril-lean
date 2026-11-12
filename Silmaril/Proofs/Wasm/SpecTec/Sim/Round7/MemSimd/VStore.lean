module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs

/-!
# Round 7, memory SIMD: `Step/vstore-oob` (22) and `Step/vstore-val` (23), forward

The value-level rule lemmas follow the scalar `Step/store-num-oob` and `store-num-val`
(`FwdMem.sstep_storeNumOob`, `sstep_storeNumVal`). The differences are the operand
`VCONST V128 c`, typed by `Typing.hasTyp_vec`, the width `$vsize(V128)/8 = 16`, and the written
bytes `$vbytes_(V128, c)`.

* `vBytes_withVBytes`: `withVBytes B` answers `$vbytes_` (`VBytes`), for every `B`.
* `sstep_vstoreOob`, `sstep_vstoreVal`: the two rules fire, for arbitrary typed state values.
* `fwd_vecStoreOob`, `fwd_vecStoreVal`: **Core's `MemoryStep.vecStoreOob`/`vecStoreVal`
  forward**. Each is a SpecTec step from the state image and the code
  `[CONST at i, VCONST V128 c, instrToVM (vecStore x ao)]`, so the vector store is encoded against
  the IL type `instr` (`Round6.MemSimd.typedV_vecMemV`), not by the provisional `schemaInstrV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecStepRules (vstoreOobRule vstoreValRule vstoreLaneOobRule)
open Silmaril.SpecTec.Equiv.RuntimeBridge (memInstToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

/-! ## `$vbytes_` -/

set_option maxRecDepth 100000 in
theorem findDef_vbytes (B : Builtins) : ∃ ps t, (simEnv B).findDef? "vbytes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- **`withVBytes B` answers `$vbytes_`**, for every `B`. -/
theorem vBytes_withVBytes (B : Builtins) : VBytes (simEnv (withVBytes B)) := fun c =>
  Prims.applies_of_noClause (findDef_vbytes _) (by simp [simEnv, withVBytes, vbytesCall, pctV, caseNilV])

/-! ## Evaluation helpers -/

section Helpers

variable {env : Env}

/-- `V128`. -/
theorem evalExp_v128 {ρ : VarEnv} :
    EvalExp env ρ (.caseE "V128" (.tupE [])) (caseNilV "V128") :=
  evalExp_case (RefsGC.evalExp_tupE_of RefsGC.evalExps_nil')

/-- `$vsize(V128)/8`, written through `ℚ` as the rules write it. -/
theorem evalExp_vsize8 {B : Builtins} {σ : List (IL.Id × Value)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [.expA (.caseE "V128" (.tupE []))])
        .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN 16)) := by
  have h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) (.num (.natN 128)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons evalExp_v128 evalArgs_nil)
      FwdSimdAgg.applies_vsize
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) .natT .ratT) (.num (.ratN 128)) :=
    evalExp_cvtE_iff.2 ⟨_, _, h, rfl, rfl⟩
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE (.numE (.natN 8)) .natT .ratT)
      (.num (.ratN 8)) := evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have e₃ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.binE .divOp (.numT .ratT)
      (.cvtE (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN ((16 : Nat) : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show (8 : ℚ) ≠ 0 by decide, ↓reduceIte]
      norm_num⟩⟩
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, by decide +kernel, rfl⟩

end Helpers

/-! ## From one firing rule to both readings -/

/-- A rule of a parameterless relation, fired at an explicit assignment. -/
theorem fires_of_ruleAt {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} {prems : List Prem}
    (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems)) (σ : List (IL.Id × Value))
    {v : Value} (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, DPrem env (otherwise env) (otherwise env x [] k v)
      (VarEnv.empty.bindVals σ) pr) :
    Fires env x k v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact ⟨t, rules, _, hrel, hk, rfl, VarEnv.empty, σ, rfl, hq, he,
    fun pr hpr => dprem_toPremW (hp pr hpr)⟩

/-- **A firing `Step` rule `k ≥ 6` is a step in both readings**: the declarative `SStep` and
round 6's backend reading `SStepB` (`Round6.Int.backend`), whose rules `k ≥ 6` fire exactly when
the declarative ones do (`Round6.Reading.firesB_step_iff`). -/
theorem both_of_fires {B : Builtins} {k : Nat} (hk : 6 ≤ k) {v w : Value}
    (hf : Fires (simEnv B) "Step" k (.tuple [v, w])) :
    SStep (simEnv B) v w ∧ (Round6.Int.backend).step B v w := by
  obtain ⟨t, rules, hrel⟩ := Bwd.findRel_of_ruleAt (hasStepRules_simEnv B).pure
  exact ⟨(dderives_iff_fires hrel).2 ⟨k, hf⟩,
    (Round6.Reading.dderivesB_iff_firesB hrel).2
      ⟨k, (Round6.Reading.firesB_step_iff B (.inr hk)).2 hf⟩⟩

/-! ## The rules, for arbitrary state values -/

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

/-- The `VCONST V128 c` operand. -/
abbrev vconstV (c : BitVec 128) : Value := .case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat])

/-- The `VSTORE V128 x ao` instruction. -/
abbrev vstoreV (n : Nat) (arg : MemArg) : Value :=
  .case "VSTORE" (.tuple [caseNilV "V128", idxV n, memargV arg])

include St M in
/-- **`Step/vstore-oob`** (rule 22). -/
theorem fires_vstoreOob (h : HasRuleAt (simEnv B) "Step" "%~>%" 22 vstoreOobRule)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width}
    {c : BitVec 128} {n : Nat} {arg : MemArg} (hz : TypedV (simEnv B) stateT (stV S F))
    (hn : n < 2 ^ 32) (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + 16) :
    Fires (simEnv B) "Step" 22 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c, vstoreV n arg], cfgV (stV S F) [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c", pctV c.toNat), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact fires_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128)
          (QuantsOk.cons rfl (St.idx n hn _ hρ)
            (QuantsOk.cons rfl (M.memarg arg _ hρ) QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        evalExp_vsize8)
      (Memory.evalExp_memBytesLen (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl)
        hm hB) hoob)))

include St M in
/-- **`Step/vstore-val`** (rule 23): `z; (CONST at i) (VCONST V128 c) (VSTORE V128 x ao) ~>
$with_mem(z, x, i + ao.OFFSET, 16, b*); ε` with `b* = $vbytes_(V128, c)`. -/
theorem fires_vstoreVal (Vb : VBytes (simEnv B))
    (h : HasRuleAt (simEnv B) "Step" "%~>%" 23 vstoreValRule)
    {S F M' m m' S' : Value} {Ls As bs : List Value} {ma : Nat} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32)
    (hS : S.field? "MEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M')
    (hA : M'.field? "MEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN ma)))
    (hm : Ls[ma]? = some m) (hB : m.field? "BYTES" = some (.list bs))
    (hsl : SliceAt bs (i.toNat + arg.offset.val) 16)
    (hm' : m.setField "BYTES" (.list (bs.take (i.toNat + arg.offset.val) ++
      leBytesV 16 c.toNat ++ bs.drop (i.toNat + arg.offset.val + 16))) = some m')
    (hS' : S.setField "MEMS" (.list (Ls.set ma m')) = some S') :
    Fires (simEnv B) "Step" 23 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c, vstoreV n arg], cfgV (stV S' F) []]) := by
  let ws := leBytesV 16 c.toNat
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c", pctV c.toNat), ("x", idxV n), ("ao", memargV arg), ("b*", .list ws)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hbT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.iterT (.varT "byte" []) .list)
      (.list ws) := FwdMem.hasTyp_bytes hρ _
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "vbytes_" [.expA (.caseE "V128" (.tupE [])), .expA (.varE "c")]) (.list ws) :=
    FwdMem.evalExp_call_applies (evalArgs_cons evalExp_v128 (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Vb c)
  have ewm := FwdMem.evalExp_withMem (ez := .varE "z") (ex := .varE "x")
    (eb := State.iterVar "b" "b*") (State.stateDefs_simEnv B) (FwdMem.withMemDef_simEnv B)
    (Memory.findDef_bindVals_empty σ _) (evalExp_var rfl) (evalExp_var rfl)
    (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl)) evalExp_vsize8
    (Equiv.Execution.evalExp_iterPat (by decide) rfl) hS hM hA ha hm hB (hsl.2 ws) hm' hS'
  exact fires_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            (QuantsOk.cons rfl hbT QuantsOk.nil)))))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ewm
      (RefsGC.evalExp_listE_of RefsGC.evalExps_nil'))))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true
      (Equiv.Execution.evalExp_iterPat (by decide) rfl) e₁)))

set_option maxRecDepth 100000 in
theorem findTyp_N (B : Builtins) :
    (simEnv B).findTyp? "N" = some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-- The `VSTORE_LANE V128 N x ao j` instruction. -/
abbrev vstoreLaneV (w n : Nat) (arg : MemArg) (j : Nat) : Value :=
  .case "VSTORE_LANE" (.tuple [caseNilV "V128", pctV w, idxV n, memargV arg, pctV j])

include St M in
/-- **`Step/vstore_lane-oob`** (rule 24), at a pack width `w ∈ {8, 16, 32, 64}`. -/
theorem fires_vstoreLaneOob (h : HasRuleAt (simEnv B) "Step" "%~>%" 24 vstoreLaneOobRule)
    {S F m : Value} {bs : List Value} {a : AddrType} {i : BitVec a.intType.width}
    {c : BitVec 128} {w n : Nat} {arg : MemArg} {l : LaneIdx}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (hz : TypedV (simEnv B) stateT (stV S F))
    (hn : n < 2 ^ 32) (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + w / 8) :
    Fires (simEnv B) "Step" 24 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vconstV c, vstoreLaneV w n arg l.val], cfgV (stV S F) [.case "TRAP" (.tuple [])]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("c", pctV c.toNat), ("N", .num (.natN w)), ("x", idxV n),
    ("ao", memargV arg), ("j", pctV l.val)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact fires_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl)
        (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128)
          (QuantsOk.cons rfl (Typing.typedV_natAlias (findTyp_N B) w _ hρ)
            (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
              (QuantsOk.cons rfl (Round5.SimdTy.typedV_laneidx l _ hρ) QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (Memory.evalExp_div8 hw (evalExp_var rfl)))
      (Memory.evalExp_memBytesLen (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl)
        hm hB) hoob)))

/-! ## Core's vector stores, forward -/

variable {H : Type} {hn : H → String}

theorem instrToVM_vecStore (x : MemIdx) (arg : MemArg) :
    Round6.MemSimd.instrToVM (.vecStore x arg) = vstoreV x.toNat arg := rfl

include St M in
/-- **`MemoryStep.vecStoreOob`, forward**: an out-of-bounds vector store traps in SpecTec too,
from a typed state image, with the store encoded by `instrToVM`. -/
theorem fwd_vecStoreOob {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst}
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + 16) :
    SStep (simEnv B)
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)])
      (cfgV (stateV hn s f) [adminToV .trap]) ∧
    (Round6.Int.backend).step B
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)])
      (cfgV (stateV hn s f) [adminToV .trap]) := by
  rw [State.adminToV_aconst, instrToVM_vecStore]
  exact both_of_fires (by decide) <| fires_vstoreOob St M
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreOob |> hasRuleAt_simEnv B)
    hz x.value.isLt (memAt_of_mem? hn hm) (Memory.memInstV_BYTES mi)
    (by simpa [effAddr] using h)

include St M in
/-- **`MemoryStep.vecStoreVal`, forward**: an in-bounds vector store writes the same bytes in
SpecTec, once `$vbytes_` is answered (`VBytes`; `vBytes_withVBytes`). -/
theorem fwd_vecStoreVal (Vb : VBytes (simEnv B)) {s : Store H} {f : Frame} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat}
    {mi : MemInst} {b : ByteArray} (hz : TypedV (simEnv B) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi))
    (hs : Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg) (count := 16) c =
      some b) :
    SStep (simEnv B)
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)])
      (cfgV (stateV hn (s.setMem ma { mi with bytes := b }) f) []) ∧
    (Round6.Int.backend).step B
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStore x arg)])
      (cfgV (stateV hn (s.setMem ma { mi with bytes := b }) f) []) := by
  obtain ⟨hle, hb⟩ := FwdMem.store_bytesV hs
  obtain ⟨M', Ls, As, hS, hM, hA, ha, hmi, hm', hS'⟩ := FwdMem.fwd_storeAux (hn := hn) hm hb
  rw [State.adminToV_aconst, instrToVM_vecStore]
  exact both_of_fires (by decide) <| fires_vstoreVal St M Vb
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreVal |> hasRuleAt_simEnv B)
    hz x.value.isLt hS hM hA ha hmi (FwdMem.memInstV_BYTES' mi)
    (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hm' hS'

theorem instrToVM_vecStoreLane (p : PackSize) (x : MemIdx) (arg : MemArg) (l : LaneIdx) :
    Round6.MemSimd.instrToVM (.vecStoreLane p x arg l) = vstoreLaneV p.width x.toNat arg l.val :=
  rfl

include St M in
/-- **`MemoryStep.vecStoreLaneOob`, forward.** -/
theorem fwd_vecStoreLaneOob {s : Store H} {f : Frame} {sz : PackSize} {x : MemIdx}
    {arg : MemArg} {j : LaneIdx} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128}
    {ma : Nat} {mi : MemInst} (hz : TypedV (simEnv B) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
    SStep (simEnv B)
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)])
      (cfgV (stateV hn s f) [adminToV .trap]) ∧
    (Round6.Int.backend).step B
      (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)])
      (cfgV (stateV hn s f) [adminToV .trap]) := by
  rw [State.adminToV_aconst, instrToVM_vecStoreLane]
  exact both_of_fires (by decide) <| fires_vstoreLaneOob St M
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreLaneOob |> hasRuleAt_simEnv B)
    (by cases sz <;> simp [PackSize.width]) hz x.value.isLt (memAt_of_mem? hn hm)
    (Memory.memInstV_BYTES mi) (by simpa [effAddr] using h)

/-- **Both vector store steps at the concrete primitives with `$vbytes_`, at round 6's backend
reading**:
`withVBytes (Prims.builtins P hn host)` (state and memory typing are proved for every
`simEnv B`). -/
theorem fwd_vecStore_builtins {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {ma : Nat} {mi : MemInst}
    (hz : TypedV (simEnv (withVBytes (Prims.builtins P hn host))) stateT (stateV hn s f))
    (hm : s.mem? f x = some (ma, mi)) :
    (mi.bytes.size < effAddr i.toNat arg + 16 →
      (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host))
        (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
          Round6.MemSimd.instrToVM (.vecStore x arg)])
        (cfgV (stateV hn s f) [adminToV .trap])) ∧
    (∀ b, Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr i.toNat arg) (count := 16) c =
        some b →
      (Round6.Int.backend).step (withVBytes (Prims.builtins P hn host))
        (cfgV (stateV hn s f) [adminToV (aconst a i), valV (.vec c),
          Round6.MemSimd.instrToVM (.vecStore x arg)])
        (cfgV (stateV hn (s.setMem ma { mi with bytes := b }) f) [])) :=
  ⟨fun h => (fwd_vecStoreOob (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) hz hm
      h).2,
    fun _ hs => (fwd_vecStoreVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _)
      (vBytes_withVBytes _) hz hm hs).2⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
