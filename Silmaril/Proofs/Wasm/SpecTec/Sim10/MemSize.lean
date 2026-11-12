module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ConstBound

/-!
# `Step_read/memory.size` of 1.0, backwards

1.0's `Step_read/memory.size` (rule 12) is 2.0's rule 36 verbatim (`Sim20.Whole.memorySizeRule`,
kernel `rfl` at the 1.0 index): `z; MEMORY.SIZE ~> CONST I32 (% n)` under
`n * 64 * $Ki = |$mem(z, 0).BYTES|`. The premise is read back with 2.0's environment-generic
`Sim20.Whole.memSize_inv`, at the 1.0 `$mem` (`evalExp_memLen10`) and `$Ki`.

V1's `Step.memorySize` answers `i32.const (BitVec.ofNat 32 (Memory.size m.data))`, where
`Memory.size` divides by the page size `65536`. The premise makes the size a whole number `n` of
pages, and `n < 2 ^ 32` because the result `admininstr*` is IL-typed (`lt_of_typed_constI32_10`).
The memory exists by `ResOkL10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 HasClause1)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memorySizeRule memSize_inv evalExp_constN)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

variable (B) in
theorem hasRuleAt10_memorySize : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 12 memorySizeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasClause_ki10 : HasClause1 (simEnv10 B) "Ki" [] (.numE (.natN 1024)) := ⟨_, _, _, rfl⟩

/-- `$Ki = 1024` in 1.0. -/
theorem evalExp_ki10 {ρ : VarEnv} (hρ : ρ.findDef? "Ki" = none) :
    EvalExp (simEnv10 B) ρ (.callE "Ki" []) (.num (.natN 1024)) :=
  evalExp_call1 (ρ₀ := VarEnv.empty) hasClause_ki10 hρ evalArgs_nil matchArgs_nil
    (evalExp_numE_iff.2 rfl)

theorem head10_memorySize {a : Admin} (h : adminHead10 a = "MEMORY.SIZE") :
    a = .source .memorySize := by
  revert h; admin_head_inv10

/-- The image of V1's `memory.size` result, at a whole number `k < 2 ^ 32` of pages. -/
theorem adminsToV_memorySize {m : MemInst} {k : Nat} (hk : k * 64 * 1024 = m.data.size)
    (hlt : k < 2 ^ 32) :
    adminsToV [value ⟨.int .i32, BitVec.ofNat 32 (Execution.Memory.size m.data)⟩] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV k])] := by
  have hs : Execution.Memory.size m.data = k := by
    simp only [Execution.Memory.size, Execution.Memory.pageSize, ← hk]
    omega
  have hb : (BitVec.ofNat 32 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hs]
  show [Value.case "CONST" (.tuple [caseNilV "I32", pctV (BitVec.ofNat 32 k).toNat])] = _
  rw [hb]

/-- **`Step_read/memory.size` backwards**, at a `GoodV1` configuration with a typed result. -/
theorem bwd10_memorySize {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hw : TypedSome (simEnv10 B) adminsT (.list w))
    (hf : Fires (simEnv10 B) "Step_read" 12 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_memorySize B) hf
  obtain ⟨a₁, rfl, h₁⟩ := codes10_one hes
  obtain rfl := head10_memorySize (head10_of_caseE h₁)
  obtain ⟨⟨a, m⟩, hm⟩ := Option.isSome_iff_exists.1 (show (frameMemory s f).isSome from hg.1.1)
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ :=
    evalExp_cmpE_iff.1 (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have ev : v₁ = .num (.natN m.data.size) :=
    (cmpValues_eq_true_iff.1 hcmp).trans (EvalExp.unique e₂ (evalExp_memLen10 rfl fz hm))
  obtain ⟨k, fn, hk⟩ := memSize_inv (evalExp_ki10 rfl) (ev ▸ e₁)
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV k])] :=
    Value.list.inj (EvalExp.unique hrh (evalExp_list1 (evalExp_constN fn)))
  have hlt : k < 2 ^ 32 := lt_of_typed_constI32_10 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memorySize hk hlt).symm, .memorySize s f a m hm⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
