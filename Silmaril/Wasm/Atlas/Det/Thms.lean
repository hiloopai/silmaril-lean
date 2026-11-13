module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Det.Defs
public import Silmaril.Wasm.Det.Core.Thms

/-!
# The determinism chart: results

* `Det.toCore P F`: the inclusion into the Core chart (`s ↦ (s, oracleHost F)`), equal on every
  sentence.
* `Det.unique`: on the domain, two terminating non-trapping observations of a typed call are
  equal (from `Det.Core.DetFn.oracle`).
* `Det.always_of_may`: hence a single witness decides the call: if some observation is a
  terminating non-trapping one satisfying `φ`, every observation is a trap, a divergence, or
  satisfies `φ`; by `Det.toCore` this holds in Core.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Det

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core (DetFn oracleHost)

/-- **The determinism chart is a restriction of Core**: equal on every sentence. -/
def toCore (P : Profile) (F : Nat → List Val → Result) : Transition (chart P F) (Core.chart P Nat) :=
  BTrans.ofEq (fun s => (s, oracleHost F)) id (fun _ _ => trivial) (fun _ _ _ => rfl)

theorem toCore_dir (P : Profile) (F : Nat → List Val → Result) : (toCore P F).dir = .equal := rfl

/-- **Determinism**: two terminating, non-trapping observations of a typed call are equal. -/
theorem unique {P : Profile} {F : Nat → List Val → Result} {s : Store Nat} (hs : Dom P s)
    {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) {b₁ b₂ : Behaviour Val}
    (h₁ : b₁ ∈ behaviours P (oracleHost F) s a vs) (h₂ : b₂ ∈ behaviours P (oracleHost F) s a vs)
    (t₁ : b₁ ≠ .traps) (t₂ : b₂ ≠ .traps) (d₁ : b₁ ≠ .diverges) (d₂ : b₂ ≠ .diverges) :
    b₁ = b₂ := by
  rcases h₁ with ⟨c₁, r₁, s₁, f₁, rfl⟩ | ⟨rfl, -⟩
  · rcases h₂ with ⟨c₂, r₂, s₂, f₂, rfl⟩ | ⟨rfl, -⟩
    · have n₁ : r₁ ≠ .trap := by rintro rfl; exact t₁ rfl
      have n₂ : r₂ ≠ .trap := by rintro rfl; exact t₂ rfl
      rw [((hs a).oracle hok s₁ s₂ n₁ n₂ f₁ f₂).1]
    · exact absurd rfl d₂
  · exact absurd rfl d₁

/-- **One test run decides the call** (on the determinism domain, for a typed call). -/
theorem always_of_may {P : Profile} {F : Nat → List Val → Result} {s : Store Nat}
    (hs : Dom P s) {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) {φ : Behaviour Val → Prop}
    (h : (chart P F).Sat s (.may (a, vs) (fun b => b ≠ .traps ∧ b ≠ .diverges ∧ φ b))) :
    (chart P F).Sat s (.always (a, vs) (fun b => b = .traps ∨ b = .diverges ∨ φ b)) := by
  obtain ⟨b₀, hb₀, t₀, d₀, hφ⟩ := h
  intro b hb
  by_cases t : b = .traps
  · exact Or.inl t
  by_cases d : b = .diverges
  · exact Or.inr (Or.inl d)
  exact Or.inr (Or.inr (unique hs hok hb₀ hb t₀ t d₀ d ▸ hφ))

/-- `always_of_may`, read in the Core chart. -/
theorem core_always_of_may {P : Profile} {F : Nat → List Val → Result} {s : Store Nat}
    (hs : Dom P s) {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) {φ : Behaviour Val → Prop}
    (h : (Core.chart P Nat).Sat (s, oracleHost F)
      (.may (a, vs) (fun b => b ≠ .traps ∧ b ≠ .diverges ∧ φ b))) :
    (Core.chart P Nat).Sat (s, oracleHost F)
      (.always (a, vs) (fun b => b = .traps ∨ b = .diverges ∨ φ b)) :=
  always_of_may (F := F) hs hok h

end Silmaril.Wasm.Atlas.Det
