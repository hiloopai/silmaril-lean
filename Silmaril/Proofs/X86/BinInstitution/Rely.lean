module

public import Silmaril.X86.BinInstitution.Defs
public import Silmaril.X86.RelIsa.Thms

/-!
# Proofs: the imports' contracts linked into a model

The header is `Silmaril/X86/BinInstitution/Thms.lean`.

* `le_withImports`: linking the contracts in is monotone in the model;
* `must_live`: a `Must` run from a live state ends live;
* `must_of_withImports`: if the model meets every bound import's contract, a `Must` property
  (with the trivial run predicate) of the linked model holds of the model itself.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BinInstitution

open Silmaril.X86 (RelIsa Word)
open Silmaril.X86.RelIsa (Le Must)
open Silmaril.X86.BinInstitution

variable {σ : Type}

/-- **Linking the imports in is monotone.** -/
theorem le_withImports {C₀ C : RelIsa σ} (h : Le C₀ C) (r : DynLoad) (Γ : Imports σ) :
    Le (withImports C₀ r Γ) (withImports C r Γ) := by
  obtain ⟨hv, hs⟩ := h
  obtain ⟨V₀, st₀, ls₀⟩ := C₀
  obtain ⟨V, st, ls⟩ := C
  simp only at hv
  subst hv
  refine ⟨rfl, fun {s o} hl ho => ⟨?_, ho.2⟩⟩
  have h1 := ho.1
  simp only at h1 ⊢
  split at h1
  · exact h1
  · exact hs hl h1

/-- A `Must` run from a live state reaches its goal in a live state. -/
theorem must_live {A : RelIsa σ} {R Q : σ → Prop} {s : σ} (h : Must A R Q s) (hl : A.live s) :
    Must A R (fun t => Q t ∧ A.live t) s := by
  induction h with
  | done hq => exact .done ⟨hq, hl⟩
  | step hR hns _ ih => exact .step hR hns fun t ht => ih t ht (A.live_step hl ht)

/-- The assumed contract at an address is one of the imports' at it. -/
theorem importAt_mem {r : DynLoad} {Γ : Imports σ} {a : Word} {X : XSpec σ}
    (h : importAt r Γ a = some X) : ∃ im ∈ Γ, r.resolve im.1 = some a ∧ X = im.2 a := by
  obtain ⟨im, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨im, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩

/-- **The rely discharged**: if `C` meets the contract of every bound import, a `Must`
property of the linked model holds of `C`. -/
theorem must_of_withImports {C : RelIsa σ} {r : DynLoad} {Γ : Imports σ}
    (hΓ : ∀ im ∈ Γ, ∀ a, r.resolve im.1 = some a → (im.2 a).MustTotal C) {Q : σ → Prop}
    {s : σ} (h : Must (withImports C r Γ) (fun _ => True) Q s) (hl : C.live s) :
    Must C (fun _ => True) Q s := by
  induction h with
  | done hq => exact .done hq
  | @step s _ hns hsucc ih =>
    show Must C (fun _ => True) Q s
    cases hX : importAt r Γ (C.core s).rip with
    | none =>
      show Must C (fun _ => True) Q s
      refine .step trivial (fun hst => hns ⟨?_, fun _ h => by cases h⟩) fun t ht => ?_
      · show (match importAt r Γ (C.core s).rip with
          | some X => _ | none => C.step s .stop)
        rw [hX]; exact hst
      · refine ih t ⟨?_, fun _ h => by cases h; exact C.live_step hl ht⟩ (C.live_step hl ht)
        show (match importAt r Γ (C.core s).rip with
          | some X => _ | none => C.step s (.ok t))
        rw [hX]; exact ht
    | some X =>
      show Must C (fun _ => True) Q s
      obtain ⟨im, him, hres, rfl⟩ := importAt_mem hX
      by_cases hpre : Silmaril.X86.FnContract.AbiEntry (C.core s) (C.mem s) ∧ (im.2 (C.core s).rip).entry s
      · have hm : Must C _ (fun t => _ ∧ C.live t) s := must_live (hΓ im him _ hres s hl hpre.1 hpre.2) hl
        refine Must.bind hm fun t ⟨hres', hlt⟩ => ih t ⟨?_, fun _ h => by cases h; exact hlt⟩ hlt
        show (match importAt r Γ (C.core s).rip with
          | some X => _ | none => C.step s (.ok t))
        rw [hX]; exact fun _ _ _ => ⟨t, rfl, hres'⟩
      · exfalso
        refine hns ⟨?_, fun _ h => by cases h⟩
        show (match importAt r Γ (C.core s).rip with
          | some X => _ | none => C.step s .stop)
        rw [hX]; exact fun _ ha he => absurd ⟨ha, he⟩ hpre

end Silmaril.Proofs.X86.BinInstitution
