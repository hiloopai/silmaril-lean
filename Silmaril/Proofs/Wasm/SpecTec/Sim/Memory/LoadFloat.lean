module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Loads

/-!
# Trapping float loads, Core → SpecTec

`Step_read/load-num-oob` (38) for `f32.load`/`f64.load`. The width is `$size(F32/F64) / 8`,
evaluated through `$size`'s float clauses (`SizeDefs`, by computation). Float stores and
successful float loads quantify a float constant, which is never typed (gap 1), so only this
rule is constructible for floats.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs StateTyping)

/-- `$size`'s four clauses. -/
def SizeDefs (env : Env) : Prop :=
  ∃ ps t, env.findDef? "size" = some (ps, t,
    [.defD [] [.expA (.caseE "I32" (.tupE []))] (.numE (.natN 32)) [],
     .defD [] [.expA (.caseE "I64" (.tupE []))] (.numE (.natN 64)) [],
     .defD [] [.expA (.caseE "F32" (.tupE []))] (.numE (.natN 32)) [],
     .defD [] [.expA (.caseE "F64" (.tupE []))] (.numE (.natN 64)) []])

set_option maxRecDepth 100000 in
/-- `baseEnv` has them. -/
theorem sizeDefs_baseEnv : SizeDefs baseEnv := ⟨_, _, rfl⟩

/-- So does every `simEnv B`. -/
theorem sizeDefs_simEnv (B : Builtins) : SizeDefs (simEnv B) := by
  obtain ⟨ps, t, h⟩ := sizeDefs_baseEnv
  exact ⟨ps, t, (Env.findDef?_withBuiltins baseEnv B "size").trans h⟩

/-- `$size(Fnn)`. -/
theorem evalExp_sizeFloat {env : Env} (Z : SizeDefs env) {ρ : VarEnv} {e : Exp}
    (hρ : ρ.findDef? "size" = none) (t : FloatType)
    (he : EvalExp env ρ e (Encode.toValue (NumType.float t))) :
    EvalExp env ρ (.callE "size" [.expA e]) (.num (.natN t.width)) := by
  obtain ⟨ps, ty, hs⟩ := Z
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hs (evalArgs_cons he evalArgs_nil) ?_)
  cases t with
  | f32 =>
    exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        matchArgs_nil) premsHold_nil RefsGC.evalExp_num'))
  | f64 =>
    exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        matchArgs_nil) premsHold_nil RefsGC.evalExp_num')))

/-- `Step_read/load-num-oob` for a float load. -/
theorem sread_loadFloatOob {env : Env} (D : StateDefs env) (Z : SizeDefs env)
    (St : StateTyping env) (M : MemTyping env)
    (h : HasRuleAt env "Step_read" "%~>%" 38 loadNumOobRule) {S F m : Value} {bs : List Value}
    {a : AddrType} {i : BitVec a.intType.width} {t : FloatType} {n : Nat} {arg : MemArg}
    (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs))
    (hoob : bs.length < i.toNat + arg.offset.val + t.width / 8) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat,
        .case "LOAD" (.tuple [Encode.toValue (NumType.float t), .opt none, idxV n, memargV arg])])
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("nt", Encode.toValue (NumType.float t)), ("x", idxV n),
    ("ao", memargV arg)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hw : EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (t.width / 8))) :=
    evalExp_div8 (by cases t <;> simp [FloatType.width])
      (evalExp_sizeFloat Z (findDef_bindVals_empty σ _) t (evalExp_var rfl))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (M.numtype _ _ hρ)
        (QuantsOk.cons rfl (St.idx n hn _ hρ) (QuantsOk.cons rfl (M.memarg arg _ hρ)
          QuantsOk.nil))))))
    (by mem_eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (evalExp_effAddr (evalExp_var rfl) (evalExp_var rfl)) hw)
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) hm hB) hoob)))

/-- `MemoryStep.loadFloatOob`, forward. -/
theorem fwd_loadFloatOob {H : Type} (B : Builtins) {hn : H → String}
    (T : TypingFacts (simEnv B) hn) (St : StateTyping (simEnv B)) (M : MemTyping (simEnv B))
    {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_loadFloatOob (State.stateDefs_simEnv B) (sizeDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadNumOob (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

end Silmaril.Wasm.SpecTec.Sim.Memory
