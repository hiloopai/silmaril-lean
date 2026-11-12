module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureVals

/-!
# `Step_pure/br-succ` of 1.0, backwards

`br-succ` (9) is byte-identical in 1.0 and 2.0 (`hasRuleAt10_brSucc`, kernel `rfl`), and 2.0's
evaluation of its conclusion, `Sim20.Pure.eval_brSucc`, is stated for any environment. What it
needs is the label quantifier `l` read back as a numeral `%(k)`: an inversion of the 1.0 typing
of `labelidx`. 1.0 declares `labelidx = idx`, `idx = u32`, `u32 = uN(32)` and `uN(N)` with one
case `%(i)`, as 2.0 does; the closed-alias unfolding `Sim20.Pure.hasTyp_closedAlias` is
environment-generic, and the four `findTyp?` facts are kernel `rfl` at `simEnv10 B`
(`labelidx10_inv`).

Backwards, `br-succ` is V1's `labelBranchOuter`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin PureStep value values lowerLabel)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk quant_list ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT eval_brSucc fires_inv
  hasTyp_closedAlias labelidxT)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## The 1.0 typing of `labelidx` -/

theorem findTyp_labelidx10 : (simEnv10 B).findTyp? "labelidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

theorem findTyp_idx10 : (simEnv10 B).findTyp? "idx" =
    some ([], [.instD [] [] (.aliasT (.varT "u32" []))]) := rfl

theorem findTyp_u32_10 : (simEnv10 B).findTyp? "u32" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 32))]))]) := rfl

theorem findTyp_uN10 : ∃ ps qs p, (simEnv10 B).findTyp? "uN" =
    some (ps, [.instD qs [.expA (.varE "N")]
      (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] p])]) := ⟨_, _, _, rfl⟩

/-- A payload of a one-case `%(i : nat)` variant is a numeral `%(k)`. -/
theorem pctCase_inv {env : Env} {σ : VarEnv} {p : List Prem} {op : MixopS} {w : Value}
    (hc : HasTypCase env σ [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] p] op w) :
    ∃ k, Value.case op w = pctV k := by
  obtain ⟨t, qs', prems, hm, ht, -⟩ := hasTypCase_mem hc
  obtain ⟨rfl, rfl, -, -⟩ := TypCase.mk.inj (List.mem_singleton.1 hm)
  obtain ⟨vs, rfl, ht'⟩ := hasTyp_tupT_iff.1 ht
  obtain ⟨x, vs₁, rfl, hx, ht₁⟩ := hasTypTup_cons_iff.1 ht'
  have hv₁ : vs₁ = [] := hasTypTup_nil_iff.1 ht₁
  obtain ⟨m, rfl, hm''⟩ := hasTyp_numT_iff.1 hx
  cases m with
  | natN k => exact ⟨k, by rw [hv₁]; rfl⟩
  | _ => simp [Num.toTyp, Num.subTyp] at hm''

/-- A value of 1.0's `uN(32)` is a numeral `%(k)`. -/
theorem uN32_inv10 {ρ : VarEnv} {v : Value}
    (h : HasTyp (simEnv10 B) ρ (.varT "uN" [.expA (.numE (.natN 32))]) v) : ∃ k, v = pctV k := by
  obtain ⟨ps, qs, p, htd⟩ := findTyp_uN10 (B := B)
  have hl : localTyp? ρ "uN" [.expA (.numE (.natN 32))] = none := by simp [localTyp?]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  obtain rfl := (Option.some.inj (htd.symm.trans htd')).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact pctCase_inv hc
  · exact absurd hrest not_hasTypInsts_nil

/-- **A typed wasm-1.0 `labelidx` is a numeral `%(k)`.** -/
theorem labelidx10_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv10 B) ρ labelidxT v) : ∃ k, v = pctV k :=
  uN32_inv10 (hasTyp_closedAlias ⟨rfl, rfl, rfl⟩ findTyp_u32_10
    (hasTyp_closedAlias ⟨rfl, rfl, rfl⟩ findTyp_idx10
      (hasTyp_closedAlias hρ findTyp_labelidx10 h)))

/-! ## `br-succ` -/

/-- **`Step_pure/br-succ` backwards**: V1's `labelBranchOuter`. -/
theorem bwd10_brSucc {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 9 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_brSucc B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨lv, fl, hlt⟩ := hq "l" labelidxT (by simp)
  obtain ⟨k, rfl⟩ := labelidx10_inv (Sim.valsOnly_bindVals σ) hlt
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_brSucc fn fc fv fl fi))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, -⟩ := split_marked10 (by simpa using hb)
  obtain ⟨l, rfl⟩ := head10_br (adminToV_case10 hm)
  have hk : l.toNat = k + 1 := Sim20.Pure.pctV_inj (Value.case.inj hm).2
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV (values us ++ [.source (.br (lowerLabel l))])) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, h₁]
    show Value.list (ws ++ [.case "BR" (pctV k)]) = .list (ws ++ [.case "BR" (pctV (l.toNat - 1))])
    rw [hk, Nat.add_sub_cancel]
  exact pureBwd10_of hw' (.labelBranchOuter n cont us l₃ l (by omega))

end Silmaril.Wasm.SpecTec.Sim10.Whole
