module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadOobBwd

/-!
# Round 7, memory SIMD: `v128.load`, in bounds (`Step_read` 43), forward

`Step_read/vload-num-val`: `z; (CONST at i) (VLOAD V128 ε x ao) ~> (VCONST V128 c)` when
`$vbytes_(V128, c) = $mem(z, x).BYTES[i + ao.OFFSET : $vsize(V128)/8]`. The vector `c` is
quantified and bound only by the premise; forward it is Core's loaded vector.

* `fires_vloadNumVal`: the rule fires, for arbitrary typed state values, given `VBytes`.
* `fwd_vecLoadFull`: **Core's `vecLoadVal` at `.full`, forward**, as a `Step_read` step in both
  readings, at `withVBytes B` (which answers `$vbytes_`).

The backward direction needs the range of `c` (`c < 2 ^ 128`, from its type `vec_(V128)`),
because `$vbytes_` at `withVBytes` reads only the low 128 bits; that inversion is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateTyping)
open Memory (MemAt MemTyping memAt_of_mem?)
open FwdMem (leBytesV bytesV SliceAt)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))

include St M in
/-- **`Step_read/vload-num-val`** (rule 43). -/
theorem fires_vloadNumVal (Vb : VBytes (simEnv B)) {S F m : Value} {bs : List Value}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec 128} {n : Nat} {arg : MemArg}
    (hz : TypedV (simEnv B) stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs)) (hsl : SliceAt bs (i.toNat + arg.offset.val) 16)
    (hc : leBytesV 16 c.toNat = (bs.drop (i.toNat + arg.offset.val)).take 16) :
    Fires (simEnv B) "Step_read" 43 (.tuple [cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
      vloadV none n arg], .list [vconstV c]]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("x", idxV n), ("ao", memargV arg), ("c", pctV c.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "vbytes_" [.expA (.caseE "V128" (.tupE [])), .expA (.varE "c")])
      (.list (leBytesV 16 c.toNat)) :=
    FwdMem.evalExp_call_applies (evalArgs_cons evalExp_v128 (evalArgs_cons (evalExp_var rfl)
      evalArgs_nil)) (Vb c)
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [.expA (.caseE "V128"
          (.tupE []))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.list (leBytesV 16 c.toNat)) := hc ▸ FwdMem.evalExp_memSlice (State.stateDefs_simEnv B)
        (evalExp_var rfl) (evalExp_var rfl) hm hB
        (Memory.evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl)) evalExp_vsize8 hsl
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).vloadNumVal σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.idx n hn _ hρ)
        (QuantsOk.cons rfl (M.memarg arg _ hρ)
          (QuantsOk.cons rfl (Typing.hasTyp_vec c evalExp_v128) QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_eq_true e₁ e₂)))

variable {H : Type} {hn : H → String}

/-- `CONST at i; VLOAD …` steps to `VCONST`, which names no cast constructor either. -/
theorem fwd_vecLoadFull_fires {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * 16)}
    (hz : TypedV (simEnv (withVBytes B)) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 16 = some c) :
    Fires (simEnv (withVBytes B)) "Step_read" 43 (.tuple [cfgV (stateV hn s f)
      [aconstV (Encode.toValue a) i.toNat, vloadV none x.toNat arg],
      .list [vconstV (vecLoadResult .full c)]]) := by
  obtain ⟨hle, hb⟩ := FwdMem.load_bytesV hl
  have hc : leBytesV 16 (vecLoadResult .full c).toNat =
      ((bytesV mi.bytes).drop (effAddr i.toNat arg)).take 16 := by
    rw [← hb, vecLoadResult, FwdMem.toNat_setWidth_of_le _ (by decide)]
  exact fires_vloadNumVal (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _)
    (vBytes_withVBytes B) hz x.value.isLt (memAt_of_mem? hn hm) (FwdMem.memInstV_BYTES' mi)
    (FwdMem.sliceAt_of_or (.inl FwdMem.sliceTotal) hle) hc

/-- **`MemoryStep.vecLoadVal` at `v128.load`, forward**: from a typed state image, the in-bounds
load is a `Step_read` step to Core's loaded vector, in both readings, at `withVBytes B`. -/
theorem fwd_vecLoadFull {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * 16)}
    (hz : TypedV (simEnv (withVBytes B)) stateT (stateV hn s f)) (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) 16 = some c) :
    SRead (simEnv (withVBytes B)) (cfgV (stateV hn s f) [adminToV (aconst a i),
        Round6.MemSimd.instrToVM (.vecLoad .full x arg)])
      [adminToV (.plain (.vecConst (vecLoadResult .full c)))] ∧
      Round6.Reading.SReadB (simEnv (withVBytes B)) (cfgV (stateV hn s f)
        [adminToV (aconst a i), Round6.MemSimd.instrToVM (.vecLoad .full x arg)])
        [adminToV (.plain (.vecConst (vecLoadResult .full c)))] := by
  rw [State.adminToV_aconst, instrToVM_vecLoad]
  exact sread_of_fires loadTags_noCast (lhsIn_vload _ _ _ _ _ _) (fwd_vecLoadFull_fires hz hm hl)

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
