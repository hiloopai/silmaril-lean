module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggAll

/-!
# Round 5: `array.init_data-zero`, forward (`Step_read` 101)

Round 4 left `array.init_data-zero` open (`R4Fwd.InitDataZeroObl`): it is an `otherwise` rule,
so `-oob1` (99) and `-oob2` (100) must be refuted at the same left-hand side, and Core's
`arrayInitDataZero` has no `Expand` premise from which to read the element type `zt` that a
`-oob2` instance picks. At `n = 0` the element type does not matter: whatever `$zsize(zt)` is,
`n * $zsize(zt)` evaluates (if at all) to `0` (`mul_zero_inv`), so the `-oob2` bound evaluates to
`j > |data|`, which Core's premise `j ≤ |data|` refutes (`not_arrayInitDataOob₂_zero`). The rule
itself has no `Expand` premise and no type quantifier, so no typing bundle is used:
`fwd_arrayInitDataZero5` holds in every `simEnv B` with family R's discharged structures, and
`initDataZeroB_builtins` discharges `InitDataZeroB` for the concrete `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open RefsGC
open R4Fwd (binds_arrayInitData not_arrayInitDataOob₁ evalExp_divBy8)
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

/-- A product whose left factor evaluates to `0` evaluates, if at all, to `0`. -/
theorem mul_zero_inv {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp} {k : Num}
    (h : EvalExp env ρ (.binE .mulOp t e₁ e₂) (.num k))
    (h₀ : EvalExp env ρ e₁ (.num (.natN 0))) : k = .natN 0 := by
  obtain ⟨v₁, h₁, hc⟩ := evalExp_binE_iff.1 h
  have hv₁ : v₁ = .num (.natN 0) := EvalExp.unique h₁ h₀
  subst hv₁
  rcases hc with hs | ⟨-, v₂, -, hb⟩
  · simp [boolShort] at hs
  · cases v₂ with
    | num m =>
      cases m <;> simp [binValues, Num.bin, Res.ofOption] at hb
      exact hb.symm
    | _ => simp [binValues] at hb

/-- **The `-oob2` bound at `n = 0`**: `j + n * $zsize(zt)/8` evaluates, if at all, to `j`, for
any `zt`. -/
theorem bound_zero_inv {env : Env} {ρ : VarEnv} {ez : Exp} {jn : Nat} {v : Value}
    (h : EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") 0)
      (.cvtE (.binE .divOp (.numT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") ez) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) v)
    (hj : EvalExp env ρ (.varE "j") (pctV jn)) (hn : EvalExp env ρ (.varE "n") (.num (.natN 0))) :
    v = .num (.natN jn) := by
  obtain ⟨v₁, -, hc⟩ := evalExp_binE_iff.1 h
  obtain ⟨w, hw⟩ : ∃ w, EvalExp env ρ (.cvtE (.binE .divOp (.numT .ratT)
      (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") ez) .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) w := by
    rcases hc with hs | ⟨-, w, hw, -⟩
    · simp [boolShort] at hs
    · exact ⟨w, hw⟩
  obtain ⟨m, -, hm, -, -⟩ := evalExp_cvtE_iff.1 hw
  obtain ⟨u₁, hu₁, -⟩ := evalExp_binE_iff.1 hm
  obtain ⟨k, -, hk, -, -⟩ := evalExp_cvtE_iff.1 hu₁
  have hk0 : k = .natN 0 := mul_zero_inv hk hn
  rw [hk0] at hk
  have hfwd : EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") 0)
      (.cvtE (.binE .divOp (.numT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") ez) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.num (.natN (jn + 0 / 8))) :=
    evalExp_addNat (evalExp_unpct hj) (evalExp_divBy8 (dvd_zero 8) hk)
  simpa using EvalExp.unique h hfwd

/-- **`array.init_data-oob2` does not fire at `n = 0` when `j` is within the data segment**, for
any element type. -/
theorem not_arrayInitDataOob₂_zero {D : Interp} {els : Prop} {s : Store H} {f : Frame}
    {x : TypeIdx} {y : DataIdx} {i j : BitVec 32} {a da : Nat} {di : DataInst}
    (hdat : s.data? f y = some (da, di)) (h : j.toNat ≤ di.bytes.size) {c : Value} :
    ¬ RuleBody (simEnv B) D els [] [] "%~>%" arrayInitDataOob2Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
        .plain (.arrayInitData x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, hev, hp⟩
  have hρ := valsOnly_scope (σ := σ) hb
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl hev)
  obtain ⟨-, -, hj, hn', -, hy⟩ := binds_arrayInitData hl
  have hn0 : EvalExp (simEnv B) (ρ₀.bindVals σ) (.varE "n") (.num (.natN 0)) := by simpa using hn'
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hif
  have hv₁ : v₁ = .num (.natN j.toNat) := bound_zero_inv h₁ hj hn0
  have hdata : EvalExp (simEnv B) (ρ₀.bindVals σ) (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA, ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _) hz hy hS
      hM hA ha' hr
  have hlen := evalExp_len (evalExp_dot hdata (Memory.dataInstV_BYTES di))
  rw [Memory.bytesL_length] at hlen
  have hv₂ : v₂ = .num (.natN di.bytes.size) := EvalExp.unique h₂ hlen
  rw [hv₁, hv₂] at hcmp
  have hgt : di.bytes.size < j.toNat := by
    simpa [cmpValues, Num.cmp, Res.ofOption] using hcmp
  omega

/-- **`array.init_data-zero` (`Step_read` rule 101), forward.** -/
theorem sread_arrayInitDataZero5 (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j : BitVec 32} {a da : Nat}
    {ai : ArrayInst} {di : DataInst} (ha : s.arrays[a]? = some ai)
    (hdat : s.data? f y = some (da, di))
    (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitData x y)]⟩) (adminsToV []) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN (0 : BitVec 32).toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hl : LhsIn ["ARRAY.INIT_DATA", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
        .plain (.arrayInitData x y)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))))⟩
  have h₁ : i.toNat + (0 : BitVec 32).toNat ≤ ai.fields.length := by simpa using h.1
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayInitDataZero (readTable_simEnv B)
    (i := 101) (b := .list (adminsToV [])) (by decide) (exc := [99, 100]) hl (by decide) (by
      intro k' hk' _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hk' : k' = 99 ∨ k' = 100) with rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob1 hr']
        exact not_arrayInitDataOob₁ G ha h₁
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob2 hr']
        exact not_arrayInitDataOob₂_zero hdat h.2)
  have hif : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))) (.bool true) :=
    RefsGC.evalExp_eq_true (by eval_tac) RefsGC.evalExp_num'
  exact dderives_of_ruleAt (Aggregates.rd B).arrayInitDataZero σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (prems_two (.elsePr hel) (.ifPr hif))

/-- **`array.init_data-zero`, as a forward obligation**, in every `simEnv B`. -/
theorem fwd_arrayInitDataZero5 (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j : BitVec 32} {a da : Nat} {ai : ArrayInst} {di : DataInst}
    (ha : s.arrays[a]? = some ai) (hdat : s.data? f y = some (da, di))
    (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitData x y)]⟩ ⟨s, f, []⟩ :=
  RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayInitDataZero5 R G ha hdat h hz

/-- **`InitDataZeroB` holds for the concrete `B`** (it does not even need the bound). -/
theorem initDataZeroB_builtins {P : Profile} (hn : H → String) (host : HostSemantics H) :
    InitDataZeroB (BI P hn host) hn :=
  fun _ _ _ _ _ _ _ _ _ _ _ ha hdat h =>
    fwd_arrayInitDataZero5 (Typing.typingFacts_simEnv _ hn) (Typing.rTyping_simEnv _)
      (rStore_builtins hn host) ha hdat h

open Round4 (Bounded) in
/-- **The forward conjunct on valid, bounded sources** (the `fwd` field of `Round4Int.Parts`),
from `TypesB`, `RefOkB`, a finite host respecting the encoding, the non-bitwise SIMD operators and
`array.new_data-num` (`NewDataNumB`). -/
theorem forward_valid_final {P : Profile} {host : HostSemantics H}
    (TB : TypesB (simEnv (BI P hn host))) (KB : RefOkB (simEnv (BI P hn host)))
    (hf : HostFinite host) (hr : Prims.HostRespects hn host)
    (vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
      (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Bounded ⟨s, f, is⟩ →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩)
    (hND : NewDataNumB (BI P hn host) hn) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  forward_valid_agg TB KB hf hr vector hND (initDataZeroB_builtins hn host)

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
