module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Boundary

/-!
# The trapping integer loads and stores, Core → SpecTec

`Step_read/load-num-oob` (38) and `load-pack-oob` (40) for integer loads, `Step/store-num-oob`
(18) and `store-pack-oob` (20) for integer stores, constructed for arbitrary state values and
instantiated at the Core encoding. The access width is SpecTec's `$size(nt) / 8` (or `n / 8`),
evaluated in ℚ and converted back (`evalExp_div8`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs StateTyping GrowDefs)

/-! ## Widths -/

section Width

variable {env : Env} {ρ : VarEnv}

/-- A width `w` in bits, divided by 8 in ℚ and converted back: `w / 8`, for the widths loads and
stores use. -/
theorem evalExp_div8 {e : Exp} {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (h : EvalExp env ρ e (.num (.natN w))) :
    EvalExp env ρ (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (w / 8))) := by
  have e₁ : EvalExp env ρ (.cvtE e .natT .ratT) (.num (.ratN w)) :=
    evalExp_cvtE_iff.2 ⟨_, _, h, rfl, rfl⟩
  have e₂ : EvalExp env ρ (.cvtE (.numE (.natN 8)) .natT .ratT) (.num (.ratN 8)) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have hq : ((w : ℚ) / 8) = ((w / 8 : Nat) : ℚ) := by
    rcases hw with rfl | rfl | rfl | rfl <;> decide +kernel
  have e₃ : EvalExp env ρ (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN ((w / 8 : Nat) : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show (8 : ℚ) ≠ 0 by decide, ↓reduceIte, hq]
      rfl⟩⟩
  have hc : Num.cvt .natT (.ratN ((w / 8 : Nat) : ℚ)) = some (.natN (w / 8)) := by
    rcases hw with rfl | rfl | rfl | rfl <;> decide +kernel
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, hc, rfl⟩

/-- The address type with the same encoding as an integer type. -/
def intAddr : IntType → AddrType
  | .i32 => .i32
  | .i64 => .i64

theorem toValue_int (t : IntType) :
    Encode.toValue (NumType.int t) = Encode.toValue (intAddr t) := by
  cases t <;> rfl

theorem width_toAddr (t : IntType) : (intAddr t).intType.width = t.width := by
  cases t <;> rfl

/-- `$size(nt) / 8` for an integer number type. -/
theorem evalExp_widthInt (G : GrowDefs env) {σ : List (IL.Id × Value)} (t : IntType)
    (hnt : EvalExp env (VarEnv.empty.bindVals σ) (.varE "nt") (Encode.toValue (NumType.int t))) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (t.width / 8))) := by
  have hs := State.evalExp_size G (findDef_bindVals_empty σ _) (intAddr t) (toValue_int t ▸ hnt)
  rw [width_toAddr] at hs
  exact evalExp_div8 (by cases t <;> simp [IntType.width]) hs

end Width

/-! ## The rules, for arbitrary values -/

section Rules

variable {env : Env} (D : StateDefs env) (G : GrowDefs env) (St : StateTyping env)
  (M : MemTyping env)
include D St M

/-- `Step_read/load-num-oob` for an integer load. -/
theorem sread_loadIntOob (h : HasRuleAt env "Step_read" "%~>%" 38 loadNumOobRule)
    (G : GrowDefs env) {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {t : IntType} {n : Nat} {arg : MemArg}
    (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + t.width / 8) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "LOAD" (.tuple [Encode.toValue (NumType.int t), .opt none, idxV n, memargV arg])])
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue (NumType.int t)), ("x", idxV n),
    ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
          QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (evalExp_widthInt G t (evalExp_var rfl)))
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) hm hB) hoob)))

/-- `Step_read/load-pack-oob`. -/
theorem sread_loadPackOob (h : HasRuleAt env "Step_read" "%~>%" 40 loadPackOobRule)
    {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {t : IntType} {sz : PackSize} {sx : Signedness} {n : Nat}
    {arg : MemArg} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + sz.width / 8) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "LOAD" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%_%" (.tuple [szV sz, sxV sx]))), idxV n, memargV arg])])
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("Inn", Encode.toValue (NumType.int t)), ("n", .num (.natN sz.width)),
    ("sx", sxV sx), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.inn t _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (M.sx sx _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (evalExp_div8 (by cases sz <;> simp [PackSize.width]) (evalExp_var rfl)))
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) hm hB) hoob)))

/-- `Step/store-num-oob` for an integer store. -/
theorem sstep_storeIntOob (h : HasRuleAt env "Step" "%~>%" 18
      Silmaril.SpecTec.Equiv.ExecStepRules.storeNumOobRule)
    (G : GrowDefs env) {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {t : IntType} {c : BitVec t.width} {n : Nat} {arg : MemArg}
    (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + t.width / 8) :
    SStep env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        aconstV (Encode.toValue (NumType.int t)) c.toNat,
        .case "STORE" (.tuple [Encode.toValue (NumType.int t), .opt none, idxV n, memargV arg])])
      (cfgV (stV S F) [.case "TRAP" (.tuple [])]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue (NumType.int t)), ("c", idxV c.toNat),
    ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl (M.numInt "nt" t c _ hρ rfl) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          (QuantsOk.cons rfl (M.memarg arg _ hρ) QuantsOk.nil)))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (evalExp_widthInt G t (evalExp_var rfl)))
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) hm hB) hoob)))

/-- `Step/store-pack-oob`. -/
theorem sstep_storePackOob (h : HasRuleAt env "Step" "%~>%" 20
      Silmaril.SpecTec.Equiv.ExecStepRules.storePackOobRule)
    {S F m : Value} {bs : List Value} {a : AddrType}
    {i : BitVec a.intType.width} {t : IntType} {c : BitVec t.width} {sz : PackSize} {n : Nat}
    {arg : MemArg} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + sz.width / 8) :
    SStep env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        aconstV (Encode.toValue (NumType.int t)) c.toNat,
        .case "STORE" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%" (.tuple [szV sz]))), idxV n, memargV arg])])
      (cfgV (stV S F) [.case "TRAP" (.tuple [])]) := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("Inn", Encode.toValue (NumType.int t)), ("c", idxV c.toNat),
    ("n", .num (.natN sz.width)), ("x", idxV n), ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.inn t _ hρ)
        (QuantsOk.cons rfl (M.numInn "Inn" t c _ hρ rfl) (QuantsOk.cons rfl (St.nat _ _ hρ)
          (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
            QuantsOk.nil))))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl))
        (evalExp_div8 (by cases sz <;> simp [PackSize.width]) (evalExp_var rfl)))
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) hm hB) hoob)))

end Rules

/-! ## Forward, at the Core encoding -/

section Forward

variable {H : Type} (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (M : MemTyping (simEnv B))
include T St M

omit T St M in
/-- An integer constant encodes as `CONST Inn (% c)`. -/
theorem adminToV_intConst (t : IntType) (c : BitVec t.width) :
    adminToV (.plain (.intConst t c)) = aconstV (Encode.toValue (NumType.int t)) c.toNat := rfl

/-- `MemoryStep.loadIntOob`, forward. -/
theorem fwd_loadIntOob {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_loadIntOob (State.stateDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadNumOob (State.growDefs_simEnv B) (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `MemoryStep.loadPackOob`, forward. -/
theorem fwd_loadPackOob {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_loadPackOob (t := t) (sx := sx) (State.stateDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadPackOob (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `MemoryStep.storeIntOob`, forward. -/
theorem fwd_storeIntOob {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t none x arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc _
  have hs := sstep_storeIntOob (c := c) (State.stateDefs_simEnv B) St M
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.storeNumOob |> hasRuleAt_simEnv B)
    (State.growDefs_simEnv B) (State.typedV_state T hc) x.value.isLt (memAt_of_mem? hn hm)
    (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq, State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil]
  rw [State.adminToV_aconst, adminToV_intConst]
  exact hs

/-- `MemoryStep.storePackOob`, forward. -/
theorem fwd_storePackOob {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat}
    {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a i, .plain (.intConst t c), .plain (.intStore t (some sz) x arg)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc _
  have hs := sstep_storePackOob (c := c) (State.stateDefs_simEnv B) St M
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.storePackOob |> hasRuleAt_simEnv B)
    (State.typedV_state T hc) x.value.isLt (memAt_of_mem? hn hm)
    (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq, State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil]
  rw [State.adminToV_aconst, adminToV_intConst]
  exact hs

end Forward

end Silmaril.Wasm.SpecTec.Sim.Memory
