module

public import Silmaril.Wasm.SingleThreaded.Determinism.FamDet

@[expose] public section

/-! # Determinism of the `MemoryStep` family in the deterministic profile -/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

variable {H : Type}

theorem MemoryStep.det {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {l₁ l₂ : List Admin} {c₁ c₂ : Config H} {p : List Val}
    (h₁ : MemoryStep (Profile.deterministic o) ⟨s, f, l₁⟩ c₁)
    (h₂ : MemoryStep (Profile.deterministic o) ⟨s, f, l₂⟩ c₂) (hl : l₁ = vals p ++ l₂) :
    p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> (fam_pre <;> first
    | fam_post
    | (have := Memory.load_bound ‹_›; (try simp_all); (try casesm* _ ∧ _); (try subst_vars);
       (try omega))
    | (have := Memory.store_bound ‹_›; (try simp_all); (try casesm* _ ∧ _); (try subst_vars);
       (try omega)))

end Silmaril.Wasm.SingleThreaded.Det
