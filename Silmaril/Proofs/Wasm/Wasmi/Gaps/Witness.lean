module

public import Silmaril.Wasm.Wasmi.Gaps.Defs
public import Silmaril.Wasm.Wasmi.Thms
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The version-gap witnesses (proofs)

`witness_checks`: for every gap class `k`, `witness k` validates with no imports and allocates
with no start function (kernel evaluations of silmaril-lean's validator and `prepare?`), has the
gap `k` and no other (`hasGap`); the control module validates, allocates and has no gap. So
Core 3.0 instantiates each witness at every profile and host (`core_instantiates`, through
`Silmaril.Proofs.Wasm.Wasmi.instantiate_of` from the header `Silmaril.Wasm.Wasmi.Thms`), and the model
of wasmi 2.0.0 refuses it (`wasmi_refuses`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Gaps

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Wasmi.Gaps

/-- Core 3.0 accepts the module: it validates with no imports and allocates with no start. -/
def coreOk (m : Module) : Bool :=
  ((Validation.validate? m).map fun mt => mt.imports.isEmpty) == some true &&
    ((prepare? evalConst? ({} : Store Empty) m []).map fun p => p.2.isNone) == some true

theorem witness_checks :
    (∀ k ∈ allGaps, coreOk (witness k) = true) ∧
      (∀ k ∈ allGaps, ∀ k' ∈ allGaps, hasGap k' (witness k) = decide (k' = k)) ∧
      coreOk controlMod = true ∧ refuses controlMod = false := by
  decide +kernel

theorem core_instantiates {k : Gap} (hk : k ∈ allGaps) (P : Profile)
    (host : HostSemantics Empty) :
    ∃ c : Config Empty, Instantiate P host ({} : Store Empty) (witness k) [] c := by
  have hok : coreOk (witness k) = true := witness_checks.1 k hk
  simp only [coreOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hv, hp⟩ := hok
  rcases h : prepare? evalConst? ({} : Store Empty) (witness k) [] with _ | p
  · simp [h] at hp
  · have hst : p.2 = none := by simpa [h] using hp
    exact ⟨p.1, Silmaril.Proofs.Wasm.Wasmi.instantiate_of hv h hst P host⟩

theorem isolated {k k' : Gap} (hk : k ∈ allGaps) (hk' : k' ∈ allGaps) :
    hasGap k' (witness k) = true ↔ k' = k := by
  rw [witness_checks.2.1 k hk k' hk']
  simp

theorem wasmi_refuses {k : Gap} (hk : k ∈ allGaps) :
    instantiate200? ({} : Store Empty) (witness k) = none := by
  have hr : refuses (witness k) = true :=
    List.any_eq_true.2 ⟨k, hk, (isolated hk hk).2 rfl⟩
  simp [instantiate200?, hr]

theorem instantiate_sound {s : Store Empty} {m : Module} {p : Config Empty × Option FuncIdx}
    (h : instantiate200? s m = some p) : prepare? evalConst? s m [] = some p := by
  unfold instantiate200? Silmaril.Wasm.Wasmi.Observed.instantiate? at h
  split at h
  · cases h
  · split at h
    · exact h
    · cases h

theorem control :
    refuses controlMod = false ∧
      instantiate200? ({} : Store Empty) controlMod = prepare? evalConst? {} controlMod [] := by
  have hr : refuses controlMod = false := witness_checks.2.2.2
  have hc : Silmaril.Wasm.Wasmi.Observed.ConstOk controlMod = true := by decide +kernel
  exact ⟨hr, by simp [instantiate200?, Silmaril.Wasm.Wasmi.Observed.instantiate?, hr, hc]⟩

end Silmaril.Proofs.Wasm.Wasmi.Gaps
