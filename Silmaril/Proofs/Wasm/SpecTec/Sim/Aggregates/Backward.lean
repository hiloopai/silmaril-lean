module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Forward

/-!
# Aggregates: backward lemmas for the null traps

`Backward.read` at the rules `struct.get-null` (70), `array.get-null` (77) and `array.len-null`
(80): a SpecTec step by one of these rules from the image of a Core configuration lands on the
image of a Core step (`AggregateStep.structGetNull`, `.arrayGetNull`, `.arrayLenNull`). The proofs
read the conclusion back by evaluation (`concl_inv`) and decode the code with family C's
`CtrlDecode` (`REF.NULL_ADDR`) and `AggDecode` (the aggregate opcodes, `CONST I32`); both decoder
structures are assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- The image of a three-instruction sequence. -/
theorem adminsToV_eq_triple {is : List Admin} {v₁ v₂ v₃ : Value}
    (h : adminsToV is = [v₁, v₂, v₃]) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ ∧ adminToV a₃ = v₃ := by
  match is, h with
  | [a₁, a₂, a₃], h =>
      simp only [adminsToV, List.cons.injEq] at h
      exact ⟨a₁, a₂, a₃, rfl, h.1, h.2.1, h.2.2.1⟩
  | [], h => simp [adminsToV] at h
  | [_], h => simp [adminsToV] at h
  | [_, _], h => simp [adminsToV] at h
  | _ :: _ :: _ :: _ :: _, h => simp [adminsToV] at h

variable (B : Builtins) (CD : CtrlDecode (simEnv B)) (AD : AggDecode)
include CD AD

/-- **`Backward.read 80`** (`array.len-null`). -/
theorem bwd_arrayLenNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 80 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  intro c w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (rd B).arrayLenNull hf)
  have hc : ∃ z, configV hn c = .case "%;%" (.tuple [z, .list [caseNilV "REF.NULL_ADDR",
      .case "ARRAY.LEN" (.tuple [])]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨z, hcfg, rfl⟩ := hc
  obtain ⟨s, f, is⟩ := c
  have hz : stateV hn s f = z ∧ adminsToV is = [caseNilV "REF.NULL_ADDR", .case "ARRAY.LEN" (.tuple [])] := by
    simpa [configV] using hcfg
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hz.2
  obtain rfl := CD.refNull a₁ h₁
  obtain rfl := AD.arrayLen a₂ _ h₂
  exact ⟨[.trap], rfl, .aggregate .arrayLenNull⟩

/-- **`Backward.read 70`** (`struct.get-null`). -/
theorem bwd_structGetNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 70 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  intro c w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (rd B).structGetNull hf)
  have hc : ∃ z g, configV hn c = .case "%;%" (.tuple [z, .list [caseNilV "REF.NULL_ADDR",
      .case "STRUCT.GET" g]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨z, g, hcfg, rfl⟩ := hc
  obtain ⟨s, f, is⟩ := c
  have hz : stateV hn s f = z ∧ adminsToV is = [caseNilV "REF.NULL_ADDR", .case "STRUCT.GET" g] := by
    simpa [configV] using hcfg
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hz.2
  obtain rfl := CD.refNull a₁ h₁
  obtain ⟨sx, x, i, rfl⟩ := AD.structGet a₂ _ h₂
  exact ⟨[.trap], rfl, .aggregate .structGetNull⟩

/-- **`Backward.read 77`** (`array.get-null`). -/
theorem bwd_arrayGetNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 77 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  intro c w _ hf
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (rd B).arrayGetNull hf)
  have hc : ∃ z k g, configV hn c = .case "%;%" (.tuple [z, .list [caseNilV "REF.NULL_ADDR",
      .case "CONST" (.tuple [caseNilV "I32", k]), .case "ARRAY.GET" g]]) ∧
      w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨z, k, g, hcfg, rfl⟩ := hc
  obtain ⟨s, f, is⟩ := c
  have hz : stateV hn s f = z ∧ adminsToV is = [caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", k]),
      .case "ARRAY.GET" g] := by
    simpa [configV] using hcfg
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := adminsToV_eq_triple hz.2
  obtain rfl := CD.refNull a₁ h₁
  obtain ⟨b, rfl⟩ := AD.constI32 a₂ _ h₂
  obtain ⟨sx, x, rfl⟩ := AD.arrayGet a₃ _ h₃
  exact ⟨[.trap], rfl, .aggregate .arrayGetNull⟩

end Silmaril.Wasm.SpecTec.Sim.Aggregates
