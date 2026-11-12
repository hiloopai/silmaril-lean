module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestStoreTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Undef
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.DivRem
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead

/-!
# The two `grow-succeed` rules of the 2.0 script, and `Task.wholeStepBwdW`

`Step` 8 (`table.grow-succeed`) and 19 (`memory.grow-succeed`) of the wasm-2.0 script each have
one premise, `if $growtable($table(z, x), n, ref) = ti` (resp. `$growmemory($mem(z, 0), n) = mi`).

`$growtable` and `$growmemory` have one clause each. Its first premise is
`if ti = {TYPE ([i .. j?] rt), REFS r'*}` (resp. `{TYPE ([i .. j?] PAGE), BYTES b*}`), which
mentions `i`, `j?`, `rt` and `r'*`, and nothing binds them: the clause's patterns bind only
`ti, n, r` (resp. `mi, n`). Under the evaluator that premise fails definitely
(`growtable20_undef`, `growmemory20_undef`), so `callDef` falls back to the builtins `B`
(`growtable20_builtin`, `growmemory20_builtin`). This is the 2.0 instance of round 3's gap G3
(`RefOk.growtable_undef` for the 3.0 script).

The spec builtins `floatIntB P` answer neither name (`floatIntB_growtable`,
`floatIntB_growmemory`). **So at the spec builtins neither `grow-succeed` rule fires**
(`not_fires_tableGrowSucceed`, `not_fires_memGrowSucceed`), which discharges `BwdRestW10`
there, and with it **`Task.wholeStepBwdW`** (`wholeStepBwdW`).

The discharge is vacuous for these two rules. At `floatIntB` the 2.0 script cannot grow a table or
a memory at all, and V2's `tableGrowSucceed`/`memoryGrowSucceed` have no SpecTec counterpart. This
is a forward gap, not a backward one. `WholeGrowAnswer` handles builtins that do answer.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim.Prims (EvalExpUndef)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The clauses of `$growtable` and `$growmemory` -/

/-- A record whose first field definitely fails definitely fails. -/
theorem evalExpUndef_strHead20 {env : Env} {ρ : VarEnv} {a : AtomS} {e : Exp}
    {fs : List ExpField} (h : EvalExpUndef env ρ e) :
    EvalExpUndef env ρ (.strE (.mk a e :: fs)) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 2, by simp [evalExp, evalExpFields, h, Bind.bind, Except.bind]⟩

/-- `[i .. j?]` with `i` unbound. -/
abbrev limPat (tl : List Exp) : Exp := .caseE "[%..%]" (.tupE (.varE "i" :: tl))

/-- The first premise of `$growtable`: `if ti = {TYPE ([i .. j?] rt), …}`. -/
def growTablePrem (tl tl' : List Exp) (fs : List ExpField) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.varE "ti")
    (.strE (.mk "TYPE" (.caseE "%%" (.tupE (limPat tl :: tl'))) :: fs)))

/-- The first premise of `$growmemory`: `if mi = {TYPE ([i .. j?] PAGE), …}`. -/
def growMemPrem (tl : List Exp) (fs : List ExpField) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.varE "mi") (.strE (.mk "TYPE" (.caseE "%PAGE" (limPat tl)) :: fs)))

/-- The two definitions in the 2.0 script, up to the parts the proofs do not read. -/
structure GrowDefs20 (env : Env) : Prop where
  growtable : ∃ ps t q body tl tl' fs rest, env.findDef? "growtable" = some (ps, t,
    [.defD q [.expA (.varE "ti"), .expA (.varE "n"), .expA (.varE "r")] body
      (growTablePrem tl tl' fs :: rest)])
  growmemory : ∃ ps t q body tl fs rest, env.findDef? "growmemory" = some (ps, t,
    [.defD q [.expA (.varE "mi"), .expA (.varE "n")] body (growMemPrem tl fs :: rest)])

/-- `simEnv20 B` has them. -/
theorem growDefs_simEnv20 (B : Builtins) : GrowDefs20 (simEnv20 B) :=
  ⟨⟨_, _, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, rfl⟩⟩

/-- `[i .. j?]` definitely fails in a scope not binding `i`. -/
theorem limPat_undef {env : Env} {ρ : VarEnv} {tl : List Exp} (hi : ρ.findVal? "i" = none) :
    EvalExpUndef env ρ (limPat tl) :=
  Sim.Prims.evalExpUndef_case (Sim.Prims.evalExpUndef_tup (pre := []) evalExps_nil
    (Sim.Prims.evalExpUndef_var hi))

/-- `$growtable`'s clause definitely fails on every argument triple. -/
theorem growtable20_undef {env : Env} (D : GrowDefs20 env) (T N R : Value) :
    ∃ ps t cs, env.findDef? "growtable" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val T, .val N, .val R] := by
  obtain ⟨ps, t, q, body, tl, tl', fs, rest, hd⟩ := D.growtable
  refine ⟨ps, t, _, hd, Sim.IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        matchArgs_nil))) ?_ Sim.IntNumeric.tryClausesUndef_nil⟩
  exact Sim.Prims.premsUndef_if (Sim.Prims.evalExpUndef_cmpR (evalExp_var rfl)
    (evalExpUndef_strHead20 (Sim.Prims.evalExpUndef_case (Sim.Prims.evalExpUndef_tup (pre := [])
      evalExps_nil (limPat_undef rfl)))))

/-- `$growmemory`'s clause definitely fails on every argument pair. -/
theorem growmemory20_undef {env : Env} (D : GrowDefs20 env) (M N : Value) :
    ∃ ps t cs, env.findDef? "growmemory" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val M, .val N] := by
  obtain ⟨ps, t, q, body, tl, fs, rest, hd⟩ := D.growmemory
  refine ⟨ps, t, _, hd, Sim.IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) ?_ Sim.IntNumeric.tryClausesUndef_nil⟩
  exact Sim.Prims.premsUndef_if (Sim.Prims.evalExpUndef_cmpR (evalExp_var rfl)
    (evalExpUndef_strHead20 (Sim.Prims.evalExpUndef_case (limPat_undef rfl))))

/-- **`$growtable` is whatever the builtins answer.** -/
theorem growtable20_builtin {T N R v : Value}
    (h : Applies (simEnv20 B) "growtable" [.val T, .val N, .val R] v) :
    B.call "growtable" [.val T, .val N, .val R] = some v := by
  obtain ⟨ps, t, cs, hd, hu⟩ := growtable20_undef (growDefs_simEnv20 B) T N R
  obtain ⟨ps', t', cs', hd', hc⟩ := h
  rw [hd] at hd'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
  · rwa [simEnv20, Env.builtins_withBuiltins] at hb

/-- **`$growmemory` is whatever the builtins answer.** -/
theorem growmemory20_builtin {M N v : Value}
    (h : Applies (simEnv20 B) "growmemory" [.val M, .val N] v) :
    B.call "growmemory" [.val M, .val N] = some v := by
  obtain ⟨ps, t, cs, hd, hu⟩ := growmemory20_undef (growDefs_simEnv20 B) M N
  obtain ⟨ps', t', cs', hd', hc⟩ := h
  rw [hd] at hd'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
  · rwa [simEnv20, Env.builtins_withBuiltins] at hb

/-! ## The spec builtins answer neither -/

theorem floatIntB_growtable (P : Profile) (ws : List ArgV) :
    (Sim.Floats.floatIntB P).call "growtable" ws = none := by
  simp [Sim.Floats.floatIntB, Sim.Floats.floatNames, Sim.IntNumeric.intCall]

theorem floatIntB_growmemory (P : Profile) (ws : List ArgV) :
    (Sim.Floats.floatIntB P).call "growmemory" ws = none := by
  simp [Sim.Floats.floatIntB, Sim.Floats.floatNames, Sim.IntNumeric.intCall]

/-! ## Calls, read back at their arguments -/

/-- A call of a definition with three expression arguments, in a scope not shadowing it. -/
theorem applies_of_call3 {env : Env} {ρ : VarEnv} {x : IL.Id} (hρ : ρ.findDef? x = none)
    {e₁ e₂ e₃ : Exp} {v : Value} (h : EvalExp env ρ (.callE x [.expA e₁, .expA e₂, .expA e₃]) v) :
    ∃ v₁ v₂ v₃, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ ∧
      Applies env x [.val v₁, .val v₂, .val v₃] v := by
  obtain ⟨ws, -, -, -, hw, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  obtain ⟨v₁, ws₁, rfl, h₁, hw₁⟩ := Equiv.ExecRead.evalArgs_expA_cons_iff.1 hw
  obtain ⟨v₂, ws₂, rfl, h₂, hw₂⟩ := Equiv.ExecRead.evalArgs_expA_cons_iff.1 hw₁
  obtain ⟨v₃, ws₃, rfl, h₃, hw₃⟩ := Equiv.ExecRead.evalArgs_expA_cons_iff.1 hw₂
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hw₃
  exact ⟨v₁, v₂, v₃, h₁, h₂, h₃, (applies_iff_callDef hρ hw).2 (evalExp_callE_iff.1 h)⟩

/-- A call of a definition with two expression arguments, in a scope not shadowing it. -/
theorem applies_of_call2' {env : Env} {ρ : VarEnv} {x : IL.Id} (hρ : ρ.findDef? x = none)
    {e₁ e₂ : Exp} {v : Value} (h : EvalExp env ρ (.callE x [.expA e₁, .expA e₂]) v) :
    ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧
      Applies env x [.val v₁, .val v₂] v := by
  obtain ⟨ws, -, -, -, hw, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  obtain ⟨v₁, ws₁, rfl, h₁, hw₁⟩ := Equiv.ExecRead.evalArgs_expA_cons_iff.1 hw
  obtain ⟨v₂, ws₂, rfl, h₂, hw₂⟩ := Equiv.ExecRead.evalArgs_expA_cons_iff.1 hw₁
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hw₂
  exact ⟨v₁, v₂, h₁, h₂, (applies_iff_callDef hρ hw).2 (evalExp_callE_iff.1 h)⟩

/-! ## The two rules, up to their conclusions -/

/-- `$growtable($table(z, x), n, ref)`. -/
abbrev growTableCallE : Exp :=
  .callE "growtable" [.expA tableE, .expA (.varE "n"), .expA (.varE "ref")]

/-- `$growmemory($mem(z, 0), n)`. -/
abbrev growMemCallE : Exp := .callE "growmemory" [.expA mem0E, .expA (.varE "n")]

/-- `Step/table.grow-succeed`, rule 8 of `Step`: its premise, verbatim. -/
theorem hasRuleAt_tableGrowSucceed : ∃ qs e, HasRuleAt (simEnv20 B) "Step" "%~>%" 8
    (.ruleD "table.grow-succeed" qs "%~>%" e
      [.ifPr (.cmpE .eqOp .boolT growTableCallE (.varE "ti"))]) :=
  ⟨_, _, _, _, _, rfl, rfl, rfl⟩

/-- `Step/memory.grow-succeed`, rule 19 of `Step`: its premise, verbatim. -/
theorem hasRuleAt_memGrowSucceed : ∃ qs e, HasRuleAt (simEnv20 B) "Step" "%~>%" 19
    (.ruleD "memory.grow-succeed" qs "%~>%" e
      [.ifPr (.cmpE .eqOp .boolT growMemCallE (.varE "mi"))]) :=
  ⟨_, _, _, _, _, rfl, rfl, rfl⟩

/-- **When `B` does not answer `$growtable`, `Step/table.grow-succeed` never fires.** -/
theorem not_fires_tableGrowSucceed (hB : ∀ ws, B.call "growtable" ws = none) (v : Value) :
    ¬ Fires (simEnv20 B) "Step" 8 v := by
  intro hf
  obtain ⟨qs, e, hr⟩ := hasRuleAt_tableGrowSucceed (B := B)
  obtain ⟨σ, -, -, hp⟩ := Sim.State.Fires.rule_eq hr hf
  obtain ⟨u₁, u₂, e₁, -, -⟩ :=
    evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨T, N, R, -, -, -, ha⟩ := applies_of_call3 rfl e₁
  have hb := growtable20_builtin ha
  rw [hB] at hb
  cases hb

/-- **When `B` does not answer `$growmemory`, `Step/memory.grow-succeed` never fires.** -/
theorem not_fires_memGrowSucceed (hB : ∀ ws, B.call "growmemory" ws = none) (v : Value) :
    ¬ Fires (simEnv20 B) "Step" 19 v := by
  intro hf
  obtain ⟨qs, e, hr⟩ := hasRuleAt_memGrowSucceed (B := B)
  obtain ⟨σ, -, -, hp⟩ := Sim.State.Fires.rule_eq hr hf
  obtain ⟨u₁, u₂, e₁, -, -⟩ :=
    evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨M, N, -, -, ha⟩ := applies_of_call2' rfl e₁
  have hb := growmemory20_builtin ha
  rw [hB] at hb
  cases hb

/-! ## `Task.wholeStepBwdW` -/

/-- `BwdRestW10`, at builtins answering neither growth primitive. -/
theorem bwdRestW10_of_noGrow {P : Profile} {host : HostSemantics H}
    (ht : ∀ ws, B.call "growtable" ws = none) (hm : ∀ ws, B.call "growmemory" ws = none) :
    BwdRestW10 B hn P host where
  step i hi c w _ hf := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact absurd hf (not_fires_tableGrowSucceed ht _)
    · exact absurd hf (not_fires_memGrowSucceed hm _)

/-- **`Task.wholeStepBwdW`.** At the spec's builtins, every step of the wasm-2.0 script from a
`GoodW` configuration (the invariant of the task) is a V2 step. Rules 8 and 19 are discharged
vacuously: at `floatIntB` they never fire. -/
theorem wholeStepBwdW : Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest10 fun _ _ _ _ _ _ =>
    bwdRestW10_of_noGrow (floatIntB_growtable _) (floatIntB_growmemory _)

end Silmaril.Wasm.SpecTec.Sim20.Whole
