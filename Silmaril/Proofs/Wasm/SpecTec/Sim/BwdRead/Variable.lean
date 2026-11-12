module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Inv

/-!
# Track bwd-read: `Step_read/local.get` (23) and `Step_read/global.get` (24), backward

Whatever rule 23 (24) derives from the image of a Core configuration is the image of Core's
`local.get` (`global.get`) step. The conclusion is read back by evaluating it forwards at the
rule's quantifiers and comparing (`EvalExp.unique`); the instruction is decoded by its tag
(`Typing.adminToV_case`); the premise `$local(z, x) = ?(val)` (`$global(z, x).VALUE = val`) is
read back through the inverted accessor (`evalExp_local_inv`, `evalExp_storeAcc_inv`). The only
fact about `B` used is that it does not interpret the accessor (`NoAcc`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_localGet {a : Admin} (h : Typing.adminHead a = "LOCAL.GET") :
    ∃ x, a = .plain (.localGet x) := by
  revert h
  admin_head_inv

theorem head_globalGet {a : Admin} (h : Typing.adminHead a = "GLOBAL.GET") :
    ∃ x, a = .plain (.globalGet x) := by
  revert h
  admin_head_inv

/-- The only image tagged `LOCAL.GET` is `local.get`'s. -/
theorem decode_localGet {a : Admin} {X : Value} (h : adminToV a = .case "LOCAL.GET" X) :
    ∃ x : LocalIdx, a = .plain (.localGet x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_localGet (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- The only image tagged `GLOBAL.GET` is `global.get`'s. -/
theorem decode_globalGet {a : Admin} {X : Value} (h : adminToV a = .case "GLOBAL.GET" X) :
    ∃ x : GlobalIdx, a = .plain (.globalGet x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_globalGet (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- The configuration of a one-instruction `Step_read` rule `z; (OP x)`, read back. -/
theorem cfg_single_inv {s : Store H} {f : Frame} {is : List Admin} {Z : Value} {op : MixopS}
    {X : Value} (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case op X]])) :
    Z = stV (storeV hn s) (frameV f) ∧ ∃ a, is = [a] ∧ adminToV a = .case op X := by
  have h' : stV (storeV hn s) (frameV f) = Z ∧ adminsToV is = [.case op X] := by
    simpa [configV, stateV] using h
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single h'.2
  exact ⟨h'.1.symm, a, rfl, ha⟩

/-- A local, read back from its encoding. -/
theorem local_of_idx {f : Frame} {n : Nat} {V : Value}
    (h : (Value.list (f.locals.map fun o => .opt (o.map valV))).idx? n = some (.opt (some V))) :
    ∃ v, f.locals[n]? = some (some v) ∧ V = valV v := by
  have e : (f.locals[n]?).map (fun o => Value.opt (o.map valV)) = some (.opt (some V)) := by
    simpa [Value.idx?] using h
  obtain ⟨o, ho, eo⟩ := Option.map_eq_some_iff.1 e
  have eo' : o.map valV = some V := by simpa using eo
  obtain ⟨v, rfl, rfl⟩ := Option.map_eq_some_iff.1 eo'
  exact ⟨v, ho, rfl⟩

variable (B : Builtins) (NA : NoAcc B)
include NA

/-- **`Backward.read 23`** (`local.get`). -/
theorem bwd_localGet : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 23 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).localGet hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨V, fv, -⟩ := hq "val" State.valT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "LOCAL.GET" X]]) ∧
      w = .list [V] := by
    concl_inv he
  obtain ⟨hZ, a, rfl, ha⟩ := cfg_single_inv hc.1
  obtain ⟨x, rfl, rfl⟩ := decode_localGet ha
  have hpr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.callE "local" [.expA (.varE "z"), .expA (.varE "x")]) (.optE (some (.varE "val"))))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  have e₂ : v₂ = .opt (some V) := EvalExp.unique h₂ (evalExp_optE_some_iff.2 ⟨V, evalExp_var fv, rfl⟩)
  have e₁ : v₁ = .opt (some V) := (cmpValues_eq_true_iff.1 hcmp).trans e₂
  obtain ⟨L, hL, hr⟩ := evalExp_local_inv (State.stateDefs_simEnv B) rfl (NA.local_ _)
    (evalExp_var (hZ ▸ fz)) (evalExp_var fx) h₁
  have hL' : L = .list (f.locals.map fun o => .opt (o.map valV)) := by
    simpa using hL.symm
  obtain ⟨v, hv, rfl⟩ := local_of_idx (hL' ▸ e₁ ▸ hr)
  exact ⟨[v.toAdmin], by simp [hc.2, adminsToV, State.adminToV_toAdmin], .variable (.localGet hv)⟩

/-- **`Backward.read 24`** (`global.get`). -/
theorem bwd_globalGet : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 24 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).globalGet hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨V, fv, -⟩ := hq "val" State.valT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "GLOBAL.GET" X]]) ∧
      w = .list [V] := by
    concl_inv he
  obtain ⟨hZ, a, rfl, ha⟩ := cfg_single_inv hc.1
  obtain ⟨x, rfl, rfl⟩ := decode_globalGet ha
  have hpr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.dotE (.callE "global" [.expA (.varE "z"), .expA (.varE "x")]) "VALUE") (.varE "val"))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  have e₁ : v₁ = V := (cmpValues_eq_true_iff.1 hcmp).trans (EvalExp.unique h₂ (evalExp_var fv))
  obtain ⟨G, hG, hGV⟩ := evalExp_dotE_iff.1 h₁
  obtain ⟨Ls, M, As, ga, hLs, hM, hAs, hga, hg⟩ := evalExp_storeAcc_inv (State.stateDefs_simEnv B)
    (State.stateDefs_simEnv B).global rfl (NA.global _) (evalExp_var (hZ ▸ fz)) (evalExp_var fx) hG
  have hLs' : Ls = .list (s.globals.map globalInstV) := by simpa using hLs.symm
  have hM' : M = moduleInstToValue CT f.module := by simpa using hM.symm
  have hAs' : As = .list (f.module.globals.map fun a => .num (.natN a)) := by
    simpa [hM'] using hAs.symm
  obtain ⟨g, h₁', h₂', rfl⟩ := idx_idx_map_inv (hAs' ▸ hga) (hLs' ▸ hg)
  have hgl : s.global? f x = some (ga, g) := by simp [Store.global?, h₁', h₂']
  have hV : V = valV g.value := by simpa [← e₁] using hGV.symm
  exact ⟨[g.value.toAdmin], by simp [hc.2, hV, adminsToV, State.adminToV_toAdmin],
    .variable (.globalGet hgl)⟩

end Silmaril.Wasm.SpecTec.Sim.BwdRead
