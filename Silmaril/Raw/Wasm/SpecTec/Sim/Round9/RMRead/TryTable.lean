module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.Catch

/-!
# Round 9, rm: `try_table` at `configVD` (unrefined)

Round 6's `Exn.bwd_read_tryTable` (`Step_read` 22), re-run at `configVD` at the concrete
primitives: the premise reads `$blocktype_(z, bt)` (`blocktypeD_inv`), the body is carried into
the new label as `instrsToVD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD stateVD adminsToVD adminToVD instrsToVD adminsToVD_eq_single
  adminsToVD_append adminsToVD_vals adminsToVD_expression)
open RMPure (valsD_of adminsToVD_eq_split)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- `TRY_TABLE` at `adminToVD`. -/
theorem tryTableD_of {a : Admin} {u : Value} (h : adminToVD a = .case "TRY_TABLE" u) :
    ∃ bt cs body, a = .plain (.tryTable bt cs body) ∧
      u = .tuple [Encode.toValue bt, .case "%" (.tuple [.list (cs.map Encode.toValue)]),
        .list (instrsToVD body)] := by
  have hh := Round7.MemSimd.adminToVD_case h
  cases a with
  | plain i =>
    cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
    rename_i bt cs body
    simp only [adminToVD, Round7.MemSimd.instrToVD, Value.case.injEq, true_and] at h
    exact ⟨bt, cs, body, rfl, h.symm⟩
  | ref r => cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | _ => simp [Typing.adminHead] at hh

/-- `val^m ++ [C e]` at `adminsToVD`. -/
theorem valsNLastD_decode {B : Builtins} {ρ : VarEnv} {m : IL.Id} {op : MixopS} {e : Exp}
    {code : List Admin}
    (h : EvalExp (simEnv B) ρ (.catE (valsNPat "val" "val*" m) (.listE [.caseE op e]))
      (.list (adminsToVD code))) :
    ∃ l₁ a u vs, code = l₁ ++ [a] ∧ adminToVD a = .case op u ∧ EvalExp (simEnv B) ρ e u ∧
      ρ.findVal? "val*" = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      adminsToVD l₁ = vs := by
  obtain ⟨a, b, ha, hb, hab⟩ := Exn.evalExp_cat_inv h
  obtain ⟨vs, fv, fm, hvs⟩ := Exn.evalExp_valsNPat_inv (by decide) ha
  obtain ⟨x, rfl, hx⟩ := Exn.evalExp_list1_inv' hb
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hx
  obtain ⟨l₁, a₀, l₂, rfl, h₁, ha₀, h₂⟩ := adminsToVD_eq_split (C := [])
    (by rw [hab, List.append_nil])
  have hl₂ : l₂ = [] := by
    rw [Round7.MemSimd.adminsToVD_eq_map] at h₂; exact List.map_eq_nil_iff.1 h₂
  subst hl₂
  exact ⟨l₁, a₀, u, vs, by simp, ha₀, hu, fv, fm, by rw [h₁]; exact Value.list.inj hvs⟩

theorem bwdRD_tryTable : LeafRD (Prims.builtins P hn host) hn P host 22 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv (Prims.builtins P hn host)).tryTable hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨l₁, a, u, vs, rfl, ha, hu, fv, fm, hl₁⟩ := valsNLastD_decode hce
  obtain ⟨bt, cs, body, rfl, rfl⟩ := tryTableD_of ha
  obtain ⟨hbt, hcsE, hbody⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨t₁, t₂, hbtt, fm', fn⟩ : ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧
      (VarEnv.empty.bindVals σ).findVal? "m" = some (.num (.natN t₁.length)) ∧
      (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN t₂.length)) := by
    cases hp _ (List.mem_singleton_self _) with
    | ifPr h =>
      obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 h
      have heq : u₁ = u₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
      obtain ⟨v₁, v₂, rfl, fm₁, fn₁⟩ := Exn.instrType_inv hu₂
      have happ : Applies (simEnv (Prims.builtins P hn host)) "blocktype_"
          [.val (stateVD hn s f), .val (Encode.toValue bt)] (Exn.instrTypeV v₁ v₂) :=
        heq ▸ (Equiv.ExecNumeric.applies_iff_callDef rfl (Equiv.evalArgs_cons
          (evalExp_var (evalExp_varE_iff.1 hz))
          (Equiv.evalArgs_cons hbt Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 hu₁)
      obtain ⟨t₁, t₂, hb', h₁, h₂⟩ := blocktypeD_inv s f bt v₁ v₂ happ
      exact ⟨t₁, t₂, hb', h₁ ▸ fm₁, h₂ ▸ fn₁⟩
  obtain ⟨vs', rfl, hv', hlen'⟩ := valsD_of hl₁ (Exn.vals_typed hq (by simp) fv)
  have hlen : vs'.length = t₁.length := by
    have e : vs.length = t₁.length := by simpa [fm] using fm'
    rw [← e, hlen']
  have hv : EvalExp (simEnv (Prims.builtins P hn host)) (VarEnv.empty.bindVals σ)
      (valsNPat "val" "val*" "m") (.list (adminsToVD (vals vs'))) :=
    hl₁ ▸ Exn.evalExp_valsNPat (by decide) fv fm
  have hw := EvalExp.unique hre (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (Exn.tryCatches_inv hcsE)
    (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) Exn.evalExp_nil
      (evalExp_cat hv hbody)))))))
  refine ⟨[.handler t₂.length cs [.label t₂.length [] (vals vs' ++ expression body)]], ?_,
    .tryTable hbtt hlen⟩
  rw [hw, ← adminsToVD_expression, ← adminsToVD_append]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
