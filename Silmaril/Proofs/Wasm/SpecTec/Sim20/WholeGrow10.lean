module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestGrow

/-!
# The 1.0 route, first step: `memory.grow-succeed` in the wasm-1.0 script

The 1.0 script has no `table.grow`. Its `Step/memory.grow-succeed` is rule 11 of `Step`, which is
2.0's rule 19 byte for byte (`census_step_10_20`). Its only premise is
`if $growmemory($mem(z, 0), n) = mi`.

1.0's `$growmemory` has one clause. Its first premise is `if mi = {TYPE [i .. j?], BYTES b*}`:
1.0 memory types have no `PAGE` marker, but the unbound `i` is there as in 2.0. So the clause
fails definitely and the call is the builtins' answer (`growmemory10_builtin`). At `floatIntB`
there is no answer, so the rule never fires (`not_fires_memGrowSucceed10`). Backwards this rule is
discharged at the spec's builtins, before any 1.0 configuration encoding exists. Forwards it is
the same gap as in 2.0: at the spec's builtins the 1.0 script never grows a memory.

`simEnv10 B` is the fixed 1.0 script with the builtins `B`, the 1.0 counterpart of `simEnv20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.Wasm.SpecTec.Sim (Fires)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- The fixed wasm-1.0 script with the primitives `B` installed. -/
noncomputable def simEnv10 (B : Builtins) : Env :=
  (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed).withBuiltins B

/-- The first premise of 1.0's `$growmemory`: `if mi = {TYPE [i .. j?], …}`. -/
def growMemPrem10 (tl : List Exp) (fs : List ExpField) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.varE "mi") (.strE (.mk "TYPE" (limPat tl) :: fs)))

/-- 1.0's `$growmemory`, up to the parts the proofs do not read. -/
theorem growmemory10_def : ∃ ps t q body tl fs rest, (simEnv10 B).findDef? "growmemory" =
    some (ps, t, [.defD q [.expA (.varE "mi"), .expA (.varE "n")] body
      (growMemPrem10 tl fs :: rest)]) :=
  ⟨_, _, _, _, _, _, _, rfl⟩

/-- 1.0's `$growmemory` clause definitely fails on every argument pair. -/
theorem growmemory10_undef (M N : Value) :
    ∃ ps t cs, (simEnv10 B).findDef? "growmemory" = some (ps, t, cs) ∧
      TryClausesUndef (simEnv10 B) cs [.val M, .val N] := by
  obtain ⟨ps, t, q, body, tl, fs, rest, hd⟩ := growmemory10_def (B := B)
  refine ⟨ps, t, _, hd, Sim.IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) ?_ Sim.IntNumeric.tryClausesUndef_nil⟩
  exact Sim.Prims.premsUndef_if (Sim.Prims.evalExpUndef_cmpR (evalExp_var rfl)
    (evalExpUndef_strHead20 (limPat_undef rfl)))

/-- **1.0's `$growmemory` is whatever the builtins answer.** -/
theorem growmemory10_builtin {M N v : Value}
    (h : Applies (simEnv10 B) "growmemory" [.val M, .val N] v) :
    B.call "growmemory" [.val M, .val N] = some v := by
  obtain ⟨ps, t, cs, hd, hu⟩ := growmemory10_undef (B := B) M N
  obtain ⟨ps', t', cs', hd', hc⟩ := h
  rw [hd] at hd'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
  · rwa [simEnv10, Env.builtins_withBuiltins] at hb

/-- `Step/memory.grow-succeed`, rule 11 of 1.0's `Step`: its premise, verbatim. -/
theorem hasRuleAt_memGrowSucceed10 : ∃ qs e, HasRuleAt (simEnv10 B) "Step" "%~>%" 11
    (.ruleD "memory.grow-succeed" qs "%~>%" e
      [.ifPr (.cmpE .eqOp .boolT growMemCallE (.varE "mi"))]) :=
  ⟨_, _, _, _, _, rfl, rfl, rfl⟩

/-- **When `B` does not answer `$growmemory`, 1.0's `Step/memory.grow-succeed` never fires.** -/
theorem not_fires_memGrowSucceed10 (hB : ∀ ws, B.call "growmemory" ws = none) (v : Value) :
    ¬ Fires (simEnv10 B) "Step" 11 v := by
  intro hf
  obtain ⟨qs, e, hr⟩ := hasRuleAt_memGrowSucceed10 (B := B)
  obtain ⟨σ, -, -, hp⟩ := Sim.State.Fires.rule_eq hr hf
  obtain ⟨u₁, u₂, e₁, -, -⟩ :=
    evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨M, N, -, -, ha⟩ := applies_of_call2' rfl e₁
  have hb := growmemory10_builtin ha
  rw [hB] at hb
  cases hb

/-- **At the spec's builtins the 1.0 script never grows a memory.** -/
theorem not_fires_memGrowSucceed10_floatIntB (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step" 11 v :=
  not_fires_memGrowSucceed10 (floatIntB_growmemory P) v

end Silmaril.Wasm.SpecTec.Sim20.Whole
