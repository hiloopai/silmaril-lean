module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestTable

/-!
# `memory.grow-fail` of 1.0, backwards

1.0's `Step/memory.grow-fail` (rule 12) is 2.0's rule 20 verbatim (`Sim20.Whole.memGrowFailRule20`,
kernel `rfl` at the 1.0 index). Its result is `CONST I32 $inv_signed_(32, -1)`.

`Equiv.NumEnvCore` does not hold for `simEnv10` (1.0 has no saturating or SIMD integer
definitions), but `Equiv.NumEnvCore.callDef_invSigned` reads only its `invSignedD` field, which
holds for `simEnv10` by kernel `rfl` (`invSignedD10`). `callDef_invSigned10` is that lemma's proof,
restated over that one field, for the negative arguments the rule needs.

Backwards, at a configuration whose frame names a memory (`ResOkL10`), the rule is V1's
`Step.memoryGrow` with `Memory.Grow.failure`, which leaves the store as it is.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv

set_option maxRecDepth 100000

/-- 1.0's `$inv_signed_` is the shared definition. -/
theorem invSignedD10 (B : Builtins) :
    (simEnv10 B).findDef? "inv_signed_" = some invSignedDef := rfl

/-- **`$inv_signed_`** agrees with `Numerics.invSigned_` on negative arguments in its domain, from
the one definition (the negative branch of `Equiv.NumEnvCore.callDef_invSigned`, over
`invSignedD` alone). -/
theorem callDef_invSigned10 {env : Env} {ρ : VarEnv}
    (h : env.findDef? "inv_signed_" = some invSignedDef)
    (hρ : ρ.findDef? "inv_signed_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) (hN : 0 < N)
    (h₁ : -2 ^ (N - 1) ≤ j) (hneg : j < 0) :
    CallDef env ρ "inv_signed_" args (natV (Silmaril.Wasm.Numerics.invSigned_ N j)) := by
  refine callDef_of_tryClauses hρ h ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hpow : EvalExp env σ _ (intV ((2 ^ (N - 1) : Nat) : Int)) :=
    evalExp_toInt (evalExp_twoPowPred hN hNv)
  have hcast : (((2 ^ (N - 1) : Nat)) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  rw [hcast] at hpow
  refine tryClauses_skip_prem hmatch (premsUndef_ifPr ?_) ?_
  · exact evalExp_and (b₁ := false) (b₂ := true)
      (evalExp_cmpNum (op := .leOp) (t := .numT .intT) evalExp_zeroInt
        (evalExp_var hiv) (by simp [Num.cmp]; omega))
      (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) hpow
        (by simp [Num.cmp]; omega))
  refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
  · exact evalExp_and (b₁ := true) (b₂ := true)
      (evalExp_cmpNum (op := .leOp) (t := .numT .intT) (evalExp_unNum hpow rfl) (evalExp_var hiv)
        (by simp [Num.cmp]; omega))
      (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) evalExp_zeroInt
        (by simp [Num.cmp]; omega))
  have hsum := evalExp_binNum (env := env) (op := .addOp) (t := .numT .intT)
    (evalExp_var hiv) (evalExp_toInt (evalExp_twoPow hNv)) rfl
  have hnn : (0 : Int) ≤ j + ((2 ^ N : Nat) : Int) := by
    have : (2 : Int) ^ (N - 1) ≤ 2 ^ N := by
      have : (2 : Nat) ^ (N - 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this
    push_cast; omega
  have := evalExp_toNat (env := env) hnn hsum
  rw [Silmaril.Wasm.Numerics.invSigned_of_neg (by omega) (by omega)]
  convert this using 3
  push_cast
  rfl

/-! ## The rule backwards -/

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memGrowFailRule20 minusOneE growFailRhs)

theorem hasRuleAt10_memGrowFail (B : Builtins) :
    HasRuleAt (simEnv10 B) "Step" "%~>%" 12 memGrowFailRule20 := ⟨_, _, _, rfl, rfl, rfl⟩

variable {B : Builtins} {H : Type} {hn : H → String}

/-- `$inv_signed_(32, -1)` is `2^32 - 1` in the 1.0 script. -/
theorem evalExp_minusOne10 {ρ : VarEnv} (hρ : ρ.findDef? "inv_signed_" = none) :
    EvalExp (simEnv10 B) ρ minusOneE (.num (.natN (BitVec.allOnes 32).toNat)) := by
  have hm : EvalExp (simEnv10 B) ρ (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT
      .intT)) (.num (.intN (-1))) :=
    evalExp_unE_iff.2 ⟨.num (.intN 1), evalExp_cvtNum evalExp_num rfl, by simp [unValue, Num.un]⟩
  have e : Silmaril.Wasm.Numerics.invSigned_ 32 (-1) = (BitVec.allOnes 32).toNat := by decide
  rw [← e]
  exact evalExp_callE_iff.2 (callDef_invSigned10 (invSignedD10 B) hρ
    (evalArgs_cons evalExp_num (evalArgs_cons hm evalArgs_nil)) (by decide) (by decide)
    (by decide))

/-- Writing back a memory unchanged leaves the store as it is. -/
theorem setMemory_self {s : Store H} {a : Execution.Runtime.MemAddr} {m : MemInst}
    (h : s.memories[a.value]? = some m) : setMemory s a { m with data := m.data } = s := by
  obtain ⟨hlt, hm⟩ := List.getElem?_eq_some_iff.1 h
  have hs : s.memories.set a.value m = s.memories := by
    rw [← hm]
    exact List.set_getElem_self hlt
  simp only [setMemory, hs]

/-- The memory a `GoodV1` `memory.grow` configuration names. -/
theorem memory_of_good {s : Store H} {f : Frame} {v : Execution.Runtime.Value}
    (hg : GoodV1 (⟨s, f, [value v, .source .memoryGrow]⟩ : Config H)) :
    ∃ a m, frameMemory s f = some (a, m) ∧ s.memories[a.value]? = some m := by
  have hr : (frameMemory s f).isSome := by
    have h := hg.1
    simp only [ResOkL10] at h
    exact h.2.1
  obtain ⟨⟨a, m⟩, hfm⟩ := Option.isSome_iff_exists.1 hr
  refine ⟨a, m, hfm, ?_⟩
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hfm
  obtain ⟨a', -, m', hm', rfl, rfl⟩ := hfm
  exact hm'

/-- V1's failing `memory.grow` leaves the store as it is. -/
theorem step_memGrowFail {host : HostSemantics H} {s : Store H} {f : Frame} {n : BitVec 32}
    {a : Execution.Runtime.MemAddr} {m : MemInst} (hfm : frameMemory s f = some (a, m))
    (hsm : s.memories[a.value]? = some m) :
    Step host ⟨s, f, [value ⟨.int .i32, n⟩, .source .memoryGrow]⟩
      ⟨s, f, [value ⟨.int .i32, -1⟩]⟩ := by
  have h := Step.memoryGrow (host := host) s f a m n (-1) m.data hfm .failure
  rwa [setMemory_self hsm] at h

/-- **`Step/memory.grow-fail` backwards**, at a `GoodV1` configuration: V1's `memoryGrow` with
`Memory.Grow.failure`. -/
theorem bwd10_memGrowFail {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step" 12 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_memGrowFail B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨n, rfl, -⟩ := constI32_of_lhs10 h₁
  obtain rfl := head10_memoryGrow (head10_of_caseE h₂)
  obtain ⟨a, m, hfm, hsm⟩ := memory_of_good hg
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) growFailRhs
      (configV hn ⟨s, f, [value ⟨.int .i32, -1⟩]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_minusOne10 rfl) evalExps_nil,
        rfl⟩))))))
  exact ⟨_, EvalExp.unique hrh he, step_memGrowFail hfm hsm⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
