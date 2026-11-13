module

public import Silmaril.Wasm.Models.FXVRuns.Thms

/-!
# Core `local.set` with no operand does not step

The Core half of `Silmaril.Proofs.Wasm.Models.FXL.Refute` (split off to keep modules small), with
no host calls:

* `not_parametric_localSet`, `not_variable_localSet`, `not_head_localSet`: no head rule applies
  to `local.set` alone (the families other than `variable` are told apart by `famOf`);
* **`not_step_localSet_head`**: Core code starting with `local.set` does not step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXL

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## Core: `local.set` with no operand -/

theorem not_parametric_localSet {x : LocalIdx} {is' : List Admin} :
    ¬ ParametricStep [.plain (.localSet x)] is' := by
  intro h
  generalize hl : [Admin.plain (.localSet x)] = l at h
  cases h <;> simp_all

theorem not_variable_localSet {s : Store H} {f : Frame} {x : LocalIdx} {c : Config H} :
    ¬ VariableStep ⟨s, f, [.plain (.localSet x)]⟩ c := by
  intro h
  generalize hl : (⟨s, f, [.plain (.localSet x)]⟩ : Config H) = d at h
  cases h <;> simp_all

/-- `local.set` is in the `variable` family. -/
theorem not_fam {x : LocalIdx} {k : Fam} (hk : k ≠ .variable)
    (h : famOf (.plain (.localSet x)) = k) : False :=
  hk (h.symm.trans rfl)

theorem not_head_localSet {s : Store H} {f : Frame} {x : LocalIdx} {c : Config H} :
    ¬ Head P s f [] (.plain (.localSet x)) c := by
  intro h
  cases h with
  | parametric h => exact not_parametric_localSet h
  | numeric h => exact not_fam (by decide) (famOf_of_shape (NumericStep.shape h)).2
  | vector h => exact not_fam (by decide) (famOf_of_shape (VectorStep.shape h)).2
  | «variable» h => exact not_variable_localSet h
  | table h => exact not_fam (by decide) (famOf_of_shape (TableStep.shape h)).2
  | memory h => exact not_fam (by decide) (famOf_of_shape (MemoryStep.shape h)).2
  | reference h => exact not_fam (by decide) (famOf_of_shape (RefStep.shape h)).2
  | aggregate h => exact not_fam (by decide) (famOf_of_shape (AggregateStep.shape h)).2
  | callRefFunc _ hc => exact hc.elim

/-- **Core `local.set` with no operand does not step.** -/
theorem not_step_localSet_head {s : Store H} {f : Frame} {x : LocalIdx} {rest : List Admin}
    {c : Config H} : ¬ Step P noHost ⟨s, f, .plain (.localSet x) :: rest⟩ c := by
  intro h
  have hf0 : fnv (Admin.plain (.localSet x) :: rest) = ([], .plain (.localSet x) :: rest) :=
    fnv_cons_of_none rfl rest
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest', c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only at hf
    rw [hf0] at hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨h1, rfl, -⟩ := hf
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h1.symm
    exact not_head_localSet hh
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb <;> simp only at hf <;>
      rw [hf0] at hf <;> simp at hf

end Silmaril.Proofs.Wasm.Models.FXL
