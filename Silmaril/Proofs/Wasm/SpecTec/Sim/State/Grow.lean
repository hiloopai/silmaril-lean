module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Table

/-!
# Family M: `table.grow`/`memory.grow` failing, and `data.drop`, Core → SpecTec

`Step/table.grow-fail` (16) and `Step/memory.grow-fail` (27) have no premise: SpecTec always allows
growth to fail, and so does Core under `Profile.spec`; in either profile, a Core `growFail` step is
a SpecTec step. Their result `$inv_signed_($size(at), -1)` is evaluated through `GrowDefs`
(`evalExp_growFailResult`). `Step/data.drop` (28) is `$with_data(z, x, ε)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (natV intV evalArgs_cons evalArgs_nil callDef_invSigned)
open Silmaril.SpecTec.Equiv.RuntimeBridge

/-! ## The environment facts -/

set_option maxRecDepth 100000 in
/-- `baseEnv` has the numeric definitions `GrowDefs` names. -/
theorem growDefs_baseEnv : GrowDefs baseEnv :=
  ⟨⟨_, _, _, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxRecDepth 100000 in
/-- So has every `simEnv B`. -/
theorem growDefs_simEnv (B : Builtins) : GrowDefs (simEnv B) := by
  have hsame : ∀ x, (simEnv B).findDef? x = baseEnv.findDef? x := fun x =>
    Env.findDef?_withBuiltins baseEnv B x
  obtain ⟨⟨ps, t, rest, hs⟩, hn⟩ := growDefs_baseEnv
  refine ⟨⟨ps, t, rest, (hsame _).trans hs⟩, ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅⟩ := hn
  exact ⟨(hsame _).trans h₁, (hsame _).trans h₂, (hsame _).trans h₃, (hsame _).trans h₄,
    (hsame _).trans h₅, (hsame _).trans h₆, (hsame _).trans h₇, (hsame _).trans h₈,
    (hsame _).trans h₉, (hsame _).trans h₁₀, (hsame _).trans h₁₁, (hsame _).trans h₁₂,
    (hsame _).trans h₁₃, (hsame _).trans h₁₄, (hsame _).trans h₁₅, (hsame _).trans h₁₆,
    (hsame _).trans h₁₇, (hsame _).trans h₁₈, (hsame _).trans h₁₉, (hsame _).trans h₂₀,
    (hsame _).trans h₂₁, (hsame _).trans h₂₂, (hsame _).trans h₂₃, (hsame _).trans h₂₄,
    (hsame _).trans h₂₅⟩

/-! ## `$inv_signed_($size(at), -1)` -/

/-- `$size(at)` for an address type. -/
theorem evalExp_size {env : Env} (G : GrowDefs env) {ρ : VarEnv} {e : Exp}
    (hρ : ρ.findDef? "size" = none) (a : Silmaril.Wasm.AddrType)
    (he : EvalExp env ρ e (Encode.toValue a)) :
    EvalExp env ρ (.callE "size" [.expA e]) (natV a.intType.width) := by
  obtain ⟨ps, t, rest, hs⟩ := G.size
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hs (evalArgs_cons he evalArgs_nil) ?_)
  cases a with
  | i32 =>
    exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      matchArgs_nil) premsHold_nil evalExp_num
  | i64 =>
    exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_caseE_undef (by decide))))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        matchArgs_nil) premsHold_nil evalExp_num)

/-- `$inv_signed_(N, -1) = 2^N - 1`, at the two address widths. -/
theorem invSigned_minusOne (a : Silmaril.Wasm.AddrType) :
    Silmaril.Wasm.Numerics.invSigned_ a.intType.width (-1) =
      (BitVec.allOnes a.intType.width).toNat := by
  cases a <;> decide

/-- The result of the `grow-fail` rules, `$inv_signed_($size(at), -1)`, is `-1` at the address
width. -/
theorem evalExp_growFailResult {env : Env} (G : GrowDefs env) {ρ : VarEnv}
    (a : Silmaril.Wasm.AddrType) (hd₁ : ρ.findDef? "inv_signed_" = none)
    (hd₂ : ρ.findDef? "size" = none) (fa : ρ.findVal? "at" = some (Encode.toValue a)) :
    EvalExp env ρ (.callE "inv_signed_" [.expA (.callE "size"
        [.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []))]),
      .expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))])
      (natV (BitVec.allOnes a.intType.width).toNat) := by
  have hw : 0 < a.intType.width := by cases a <;> decide
  have hpow : (1 : Int) ≤ 2 ^ (a.intType.width - 1) := by
    have h := Nat.one_le_two_pow (n := a.intType.width - 1)
    exact_mod_cast h
  have hm : EvalExp env ρ (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
      (intV (-1)) :=
    evalExp_unE_iff.2 ⟨intV 1, evalExp_cvtNum evalExp_num rfl, by simp [unValue, Num.un, intV]⟩
  rw [← invSigned_minusOne a]
  exact evalExp_callE_iff.2 (callDef_invSigned G.num hd₁
    (evalArgs_cons (evalExp_size G hd₂ a (evalExp_subE_iff.2 (evalExp_var fa)))
      (evalArgs_cons hm evalArgs_nil)) hw (by omega) (by omega))

/-! ## The rules, for arbitrary values -/

section Rules

variable {env : Env} (G : GrowDefs env) (St : StateTyping env)
include G St

omit G St in
/-- `CONST at (% n)` with `n` a variable. -/
theorem evalExp_constAtN {ρ : VarEnv} {A : Value} {k : Nat} (fa : ρ.findVal? "at" = some A)
    (fn : ρ.findVal? "n" = some (.num (.natN k))) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
      .caseE "%" (.tupE [.varE "n"])])) (aconstV A k) :=
  evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fa))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩)))

/-- `Step/table.grow-fail`: `z; ref (CONST at (% n)) (TABLE.GROW x) ~> z; CONST at (% -1)`,
unconditionally. -/
theorem sstep_tableGrowFail
    (h : HasRuleAt env "Step" "%~>%" 16 Equiv.ExecStepRules.tableGrowFailRule) {Z R : Value}
    {a : Silmaril.Wasm.AddrType} {k n : Nat} (hz : TypedV env stateT Z) (hn : n < 2 ^ 32)
    (hR : TypedV env refT R) :
    SStep env (cfgV Z [R, aconstV (Encode.toValue a) k, .case "TABLE.GROW" (idxV n)])
      (cfgV Z [aconstV (Encode.toValue a) (BitVec.allOnes a.intType.width).toNat]) := by
  let ρ := VarEnv.empty.bindVals [("z", Z), ("ref", R), ("at", Encode.toValue a),
    ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some Z := rfl
  have fr : ρ.findVal? "ref" = some R := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN k)) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fr (hR ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fn (St.nat k ρ hρ) (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_,
        evalExps_cons (evalExp_subE_iff.2 (evalExp_var fr)) (evalExps_cons
          (evalExp_constAtN fa fn) (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)),
        rfl⟩)))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
        (evalExp_subE_iff.2 (evalExp_var fa)) (evalExp_case (evalExp_tupE_iff.2 ⟨_,
          evalExps_cons (evalExp_growFailResult G a rfl rfl fa) evalExps_nil, rfl⟩))))))))
    (fun _ h => by cases h)

/-- `Step/memory.grow-fail`: `z; (CONST at (% n)) (MEMORY.GROW x) ~> z; CONST at (% -1)`,
unconditionally. -/
theorem sstep_memoryGrowFail
    (h : HasRuleAt env "Step" "%~>%" 27 Equiv.ExecStepRules.memoryGrowFailRule) {Z : Value}
    {a : Silmaril.Wasm.AddrType} {k n : Nat} (hz : TypedV env stateT Z) (hn : n < 2 ^ 32) :
    SStep env (cfgV Z [aconstV (Encode.toValue a) k, .case "MEMORY.GROW" (idxV n)])
      (cfgV Z [aconstV (Encode.toValue a) (BitVec.allOnes a.intType.width).toNat]) := by
  let ρ := VarEnv.empty.bindVals [("z", Z), ("at", Encode.toValue a),
    ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some Z := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN k)) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fn (St.nat k ρ hρ) (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_,
        evalExps_cons (evalExp_constAtN fa fn)
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil), rfl⟩)))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
        (evalExp_subE_iff.2 (evalExp_var fa)) (evalExp_case (evalExp_tupE_iff.2 ⟨_,
          evalExps_cons (evalExp_growFailResult G a rfl rfl fa) evalExps_nil, rfl⟩))))))))
    (fun _ h => by cases h)

omit G in
/-- `Step/data.drop`: `z; (DATA.DROP x) ~> $with_data(z, x, ε); ε`. -/
theorem sstep_dataDrop (D : StateDefs env)
    (h : HasRuleAt env "Step" "%~>%" 28 Equiv.ExecStepRules.dataDropRule)
    {S S' F M t t' : Value} {Ls As : List Value} {n da : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32)
    (hS : S.field? "DATAS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "DATAS" = some (.list As)) (ha : As[n]? = some (.num (.natN da)))
    (ht : Ls[da]? = some t) (ht' : t.setField "BYTES" (.list []) = some t')
    (hS' : S.setField "DATAS" (.list (Ls.set da t')) = some S') :
    SStep env (cfgV (stV S F) [.case "DATA.DROP" (idxV n)]) (cfgV (stV S' F) []) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_case (evalExp_tup2
        (evalExp_withData D rfl (evalExp_var fz) (evalExp_var fx)
          (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hS hM hA ha ht ht' hS')
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (fun _ h => by cases h)

end Rules

/-! ## Forward, at the Core encoding -/

section Forward

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- `Store.data?` unfolded. -/
theorem Store.data?_eq_some {s : Store H} {f : Frame} {x : DataIdx} {a : Nat}
    {d : DataInst} (h : s.data? f x = some (a, d)) :
    f.module.datas[x.toNat]? = some a ∧ s.datas[a]? = some d := by
  simp only [Store.data?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, d', hd, rfl, rfl⟩ := h
  exact ⟨ha, hd⟩

/-- Emptying an encoded data segment. -/
theorem dataInstV_drop (d : DataInst) :
    (dataInstToValue d).setField "BYTES" (.list []) = some (dataInstToValue ⟨ByteArray.empty⟩) := by
  simp [dataInstToValue, bytesToValue_eq]

/-- Dropping a data segment of an encoded store encodes `Store.setData`. -/
theorem storeV_setData (hn : H → String) (s : Store H) {a : Nat} {d : DataInst}
    (hd : s.datas[a]? = some d) :
    (storeV hn s).setField "DATAS" (.list ((s.datas.map dataInstToValue).set a
      (dataInstToValue ⟨ByteArray.empty⟩))) = some (storeV hn (s.setData a ByteArray.empty)) := by
  simp [storeV, Store.setData, List.modify_eq_set_of_getElem? hd, List.map_set]

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : StateTyping (simEnv B))
include T St

/-- `TableStep.growFail`, forward, in any profile. -/
theorem fwd_tableGrowFail {P : Profile} {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {n : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti : TableInst}
    (_ : s.table? f x = some (ta, ti))
    (_ : P.growMayFail .table ta ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none) :
    FwdP (simEnv B) hn ⟨s, f, [.ref r, aconst a n, .plain (.tableGrow x)]⟩
      ⟨s, f, [aconst a (BitVec.allOnes _)]⟩ := by
  intro hc _
  show SStep _ (cfgV _ [adminToV (.ref r), adminToV (aconst a n), _])
    (cfgV _ [adminToV (aconst a (BitVec.allOnes _))])
  rw [adminToV_ref, adminToV_aconst, adminToV_aconst]
  exact sstep_tableGrowFail (growDefs_simEnv B) St (hasStepRules_simEnv B).tableGrowFail
    (typedV_state T hc) x.value.isLt (typedV_ref_of_mem B T St hc (by simp))

/-- `MemoryStep.growFail`, forward, in any profile. -/
theorem fwd_memoryGrowFail {P : Profile} {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst} (_ : s.mem? f x = some (ma, mi))
    (_ : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩
      ⟨s, f, [aconst a (BitVec.allOnes _)]⟩ := by
  intro hc _
  show SStep _ (cfgV _ [adminToV (aconst a n), _]) (cfgV _ [adminToV (aconst a (BitVec.allOnes _))])
  rw [adminToV_aconst, adminToV_aconst]
  exact sstep_memoryGrowFail (growDefs_simEnv B) St (hasStepRules_simEnv B).memoryGrowFail
    (typedV_state T hc) x.value.isLt

/-- `MemoryStep.dataDrop`, forward. -/
theorem fwd_dataDrop {s : Store H} {f : Frame} {y : DataIdx} {da : Nat} {di : DataInst}
    (hd : s.data? f y = some (da, di)) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s.setData da ByteArray.empty, f, []⟩ := by
  intro hc _
  obtain ⟨hda, hdi⟩ := Store.data?_eq_some hd
  exact sstep_dataDrop St (stateDefs_simEnv B) (hasStepRules_simEnv B).dataDrop
    (typedV_state T hc) y.value.isLt (storeV_DATAS hn s) (frameV_MODULE f) (moduleV_DATAS _)
    (getElem?_map_natN hda) (by simp [hdi]) (dataInstV_drop di) (storeV_setData hn s hdi)

end Forward

end Silmaril.Wasm.SpecTec.Sim.State
