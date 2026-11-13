module

public import Silmaril.Wasm.Component.Reference.Example.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Basic
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The Core 3.0 adder in the reference semantics: proofs
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Core3Adder

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Core3Adder
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

theorem isAdder3Type_eq {r : Except Validation.ValidationError ComponentType}
    (h : isAdder3Type r = true) : r = .ok adder3Type := by
  unfold isAdder3Type at h
  split at h
  next n ft =>
    have h' : n = "add" ∧ ft = Validation.DefsTests.adderFunc := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  · cases h

theorem adder3_check : check? Features.p2 adder3 = .ok adder3Type :=
  isAdder3Type_eq (by decide +kernel)

/-- The adder is a valid Core 3.0 component of type `adder3Type`. -/
theorem adder3_valid : Valid Features.p2 adder3 adder3Type :=
  check?_sound adder3_check

theorem runSummary_eq :
    runSummary = some (.resolved, some (some [Value.Val.u32 7])) := by
  decide +kernel

/-- **Calling the adder's export** `"add"` on `[u32 3, u32 4]` after instantiating it from the
empty store returns `[u32 7]`, in the reference machine over the Core 3.0 engine. -/
theorem adder3_returns :
    Outcome.returns (some [Value.Val.u32 7]) ∈
      exportBehaviours first.prof (Host.ofEmbedder emb) () adder3 [] "add"
        [Value.Val.u32 3, Value.Val.u32 4] := by
  have h := runSummary_eq
  unfold runSummary at h
  obtain ⟨⟨r₁, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f, hf, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨r, hc, h₃⟩ := Option.map_eq_some_iff.mp h₂
  have ho : callOutcome? ⟨0⟩ r = some (.resolved (some [Value.Val.u32 7])) := by
    have hr : r.outcome = .resolved ∧ r.config.result? ⟨0⟩ = some (some [Value.Val.u32 7]) := by
      simpa only [Prod.mk.injEq] using h₃
    simp only [callOutcome?, hr.1, hr.2, Option.map_some]
  exact exportBehaviours_of_run emb first () hi hf hc ho

end Silmaril.Proofs.Wasm.Component.Reference.Core3Adder
