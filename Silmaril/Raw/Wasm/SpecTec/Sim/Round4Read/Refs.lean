module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.Agg

/-!
# Track r4-read: `Step_read/ref.null` (63), `ref.func` (64), backward

Neither needs validity: `ref.null ht` has no premise, and `ref.func x` reads
`$moduleinst(z).FUNCS[x]`, which evaluates only when the frame's module has the function, which
is all Core's `refFunc` asks.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_refNullI {a : Admin} (h : Typing.adminHead a = "REF.NULL") :
    ∃ ht, a = .plain (.refNull ht) := by
  revert h
  admin_head_inv

theorem head_refFuncI {a : Admin} (h : Typing.adminHead a = "REF.FUNC") :
    ∃ x, a = .plain (.refFunc x) := by
  revert h
  admin_head_inv

variable (B : Builtins)

/-- **`Step_read` 63 (`ref.null`), backward.** -/
theorem bwdV_refNull : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 63 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).refNull hf)
  have hc : ∃ Z HT, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.NULL" HT]])
      ∧ w = .list [.case "REF.NULL_ADDR" (.tuple [])] := by
    concl_inv he
  obtain ⟨Z, HT, hcfg, hw⟩ := hc
  obtain ⟨-, hcode⟩ := cfg_inv hcfg
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single hcode
  obtain ⟨ht, rfl⟩ := head_refNullI (Typing.adminToV_case ha).symm
  exact ⟨[.ref .null], by rw [hw]; rfl, .reference (.refNull ht)⟩

/-- **`Step_read` 64 (`ref.func`), backward.** -/
theorem bwdV_refFunc : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 64 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).refFunc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.FUNC" X]]) ∧
      ∃ R, EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.idxE (.dotE (.callE "moduleinst" [.expA (.varE "z")]) "FUNCS")
          (.projE (.uncaseE (.varE "x") "%") 0)) R ∧
        w = .list [.case "REF.FUNC_ADDR" R] := by
    concl_inv he
  obtain ⟨⟨hZ, hcode⟩, R, hR, hw⟩ := hc.imp_left cfg_inv
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single hcode
  obtain ⟨x, rfl⟩ := head_refFuncI (Typing.adminToV_case ha).symm
  have hX : X = idxV x.toNat := by
    injection ha with _ h₂
    exact h₂.symm
  subst hZ hX
  obtain ⟨Fs, k, hFs, hk, hidx⟩ := evalExp_idxE_iff.1 hR
  have eFs : Fs = .list (f.module.funcs.map fun a => .num (.natN a)) := by
    obtain ⟨M, hM, hMF⟩ := evalExp_dotE_iff.1 hFs
    have := EvalExp.unique hM (Aggregates.evalExp_moduleinst (Aggregates.aggDefs_simEnv B) rfl
      (evalExp_var fz))
    subst this
    have hF : (RefsGC.moduleInstToValue' f.module).field? "FUNCS" =
        some (.list (f.module.funcs.map fun a => .num (.natN a))) := rfl
    rw [hF] at hMF
    exact (Option.some.inj hMF).symm
  have ek : k = x.toNat := by
    have := EvalExp.unique hk (RefsGC.evalExp_unpct (evalExp_var fx))
    simpa using this
  subst eFs ek
  have hmap : (f.module.funcs[x.toNat]?).map (fun a => Value.num (.natN a)) = some R := by
    simpa [Value.idx?] using hidx
  obtain ⟨fa, hfa, rfl⟩ := Option.map_eq_some_iff.1 hmap
  exact ⟨[.ref (.func fa)], by rw [hw]; rfl, .reference (.refFunc hfa)⟩

end Silmaril.Wasm.SpecTec.Sim.Round4Read
