module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Pure
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Rules

/-!
# What the census buys: wasm-3.0 per-rule lemmas, applied to the wasm-2.0 script

`Sim20.Census` finds 19 of the 56 wasm-2.0 `Step_pure` rules byte-identical to wasm-3.0 rules.
`sameRules_20_30` says so for the 16 of them that the earlier rounds transcribed as named
constants (`Equiv.Execution`, `Equiv.ExecNumeric`, `Equiv.ExecDefault`). The round 3 lemmas are
stated for an arbitrary environment with a `HasRuleAt` hypothesis at the wasm-3.0 index, so a
lemma transfers verbatim to `simEnv20 B` exactly when the rule is shared **and** keeps its index:
`unreachable` (0), `nop` (1), `if-true` (5) and `if-false` (6) (`spure20_*`). The others are
shared at a different index (`br_if-true` is rule 10 in wasm-2.0 and 11 in wasm-3.0), and the
lemmas would need their index generalised.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (SPure TypedV)

/-- **The rules the census finds shared, as terms**: the wasm-2.0 rules are the wasm-3.0
transcriptions of the earlier rounds. -/
theorem sameRules_20_30 :
    unreachableRule = Equiv.Execution.unreachableRule ∧ nopRule = Equiv.Execution.nopRule ∧
      ifTrueRule = Equiv.Execution.ifTrueRule ∧ ifFalseRule = Equiv.Execution.ifFalseRule ∧
      brIfTrueRule = Equiv.Execution.brIfTrueRule ∧
      brIfFalseRule = Equiv.Execution.brIfFalseRule ∧
      brTableLtRule = Equiv.ExecDefault.brTableLtRule ∧
      brTableGeRule = Equiv.ExecDefault.brTableGeRule ∧
      trapLabelRule = Equiv.Execution.trapLabelRule ∧
      trapFrameRule = Equiv.Execution.trapFrameRule ∧
      unopValRule = Equiv.ExecNumeric.unopValRule ∧ unopTrapRule = Equiv.ExecNumeric.unopTrapRule ∧
      binopValRule = Equiv.ExecNumeric.binopValRule ∧
      binopTrapRule = Equiv.ExecNumeric.binopTrapRule ∧
      testopRule = Equiv.ExecNumeric.testopRule ∧ relopRule = Equiv.ExecNumeric.relopRule :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (B : Builtins)

/-- Round 3's `unreachable` lemma, on the wasm-2.0 script. -/
theorem spure20_unreachable :
    SPure (simEnv20 B) [.case "UNREACHABLE" (.tuple [])] [.case "TRAP" (.tuple [])] :=
  Silmaril.Wasm.SpecTec.Sim.IntNumeric.spure_unreachable (hasRuleAt_unreachable B)

/-- Round 3's `nop` lemma, on the wasm-2.0 script. -/
theorem spure20_nop : SPure (simEnv20 B) [.case "NOP" (.tuple [])] [] :=
  Silmaril.Wasm.SpecTec.Sim.IntNumeric.spure_nopRule (hasRuleAt_nop B)

/-- Round 3's `if-true` lemma, on the wasm-2.0 script. -/
theorem spure20_ifTrue {k : Nat} (hk : k ≠ 0) {bt : Value} {b₁ b₂ : List Value}
    (hc : TypedV (simEnv20 B) i32T (pctV k)) (hbt : TypedV (simEnv20 B) blocktypeT bt)
    (h₁ : TypedV (simEnv20 B) instrsT (.list b₁)) (h₂ : TypedV (simEnv20 B) instrsT (.list b₂)) :
    SPure (simEnv20 B) [.case "CONST" (.tuple [caseNilV "I32", pctV k]),
        .case "IF%%ELSE%" (.tuple [bt, .list b₁, .list b₂])]
      [.case "BLOCK" (.tuple [bt, .list b₁])] :=
  Silmaril.Wasm.SpecTec.Sim.spure_ifTrue (hasRuleAt_ifTrue B) hk hc hbt h₁ h₂

/-- Round 3's `if-false` lemma, on the wasm-2.0 script. -/
theorem spure20_ifFalse {bt : Value} {b₁ b₂ : List Value}
    (hc : TypedV (simEnv20 B) i32T (pctV 0)) (hbt : TypedV (simEnv20 B) blocktypeT bt)
    (h₁ : TypedV (simEnv20 B) instrsT (.list b₁)) (h₂ : TypedV (simEnv20 B) instrsT (.list b₂)) :
    SPure (simEnv20 B) [.case "CONST" (.tuple [caseNilV "I32", pctV 0]),
        .case "IF%%ELSE%" (.tuple [bt, .list b₁, .list b₂])]
      [.case "BLOCK" (.tuple [bt, .list b₂])] :=
  Silmaril.Wasm.SpecTec.Sim.spure_ifFalse (hasRuleAt_ifFalse B) hc hbt h₁ h₂

end Silmaril.Wasm.SpecTec.Sim20.Pure
