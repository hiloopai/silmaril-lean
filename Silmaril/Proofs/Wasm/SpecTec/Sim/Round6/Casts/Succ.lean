module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Forward

/-!
# Round 6: successors of typed witnesses are typed, under the new reading

`Round5.Multi.succCallsTyped` and `succTyped` (`Round5/Multi/SuccCalls.lean`) for
`SStepB`. A step of the new reading is a rule body at an alternative of the rule's conclusion; no
rule of `Step` has an empty-domain option in its conclusion (`stepRules_noOpt`, checked over the
script), so the alternative is the conclusion itself and round 5's check applies unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round5.Multi (CodeCallsTyped)
open Reading (SStepB)

variable {H : Type}

set_option maxRecDepth 100000 in
/-- **No rule of `Step` has an empty-domain option in its conclusion**, in every `simEnv B`. -/
theorem stepRules_noOpt (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
      rules.all (fun r => !Reading.hasOptNil (Reading.ruleConcl r)) = true :=
  ⟨_, _, rfl, rfl⟩

/-- The rule list of `Step`, read off two lookups. -/
theorem step_rules_eq {B : Builtins} {ps : List Param} {op : MixopS} {t t' : Typ}
    {rules rules' : List Rule}
    (h₁ : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (h₂ : (simEnv B).findRel? "Step" = some ([], "%~>%", t', rules')) :
    ps = [] ∧ op = "%~>%" ∧ rules = rules' := by
  have h := h₁.symm.trans h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- **The `CALL_REF`s of the new reading's successors of typed witnesses are typed**
(`Round5.Multi.succCallsTyped` for `SStepB`). -/
theorem succCallsTypedB (B : Builtins) (hn : H → String) (d d' : Config H)
    (hd : Typed (simEnv B) hn d) (hs : SStepB (simEnv B) (configV hn d) (configV hn d')) :
    CodeCallsTyped (simEnv B) d'.code := by
  cases hs with
  | rule hrel hrule halt hps hq he _ =>
    obtain ⟨t₁, rules₁, hrel₁, hall⟩ := Round5.Multi.stepRules_checked B
    obtain ⟨t₂, rules₂, hrel₂, hno⟩ := stepRules_noOpt B
    obtain ⟨rfl, -, rfl⟩ := step_rules_eq hrel hrel₁
    obtain ⟨-, -, rfl⟩ := step_rules_eq hrel₁ hrel₂
    obtain rfl : _ = VarEnv.empty := (Option.some.inj hps).symm
    have hmem := List.mem_of_getElem? hrule
    obtain ⟨_, _, _, S, lc, S', rc, _, hr, hg⟩ :=
      Round5.Multi.succRule_inv (List.all_eq_true.1 hall _ hmem)
    cases hr
    have hn₀ : Reading.hasOptNil
        (.tupE [.caseE "%;%" (.tupE [S, lc]), .caseE "%;%" (.tupE [S', rc])]) = false := by
      simpa [Reading.ruleConcl] using List.all_eq_true.1 hno _ hmem
    rw [Reading.conclAlts_of_not hn₀, List.mem_singleton] at halt
    subst halt
    exact Round5.Multi.calls_of_rule hd hq he hg

/-- **The new reading's successors of typed witnesses are typed** when they agree with a typed
configuration up to `ConfigEq` (`Round5.Multi.succTyped` for `SStepB`). -/
theorem succTypedB (B : Builtins) (hn : H → String) (d d' c' : Config H)
    (htd : Typed (simEnv B) hn d) (hs : SStepB (simEnv B) (configV hn d) (configV hn d'))
    (he : Bwd.ConfigEq c' d') (htc' : Typed (simEnv B) hn c') : Typed (simEnv B) hn d' :=
  Round5.Multi.typed_of_configEq (Typing.typingFacts_simEnv B hn) he htc'
    (succCallsTypedB B hn d d' htd hs)

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
