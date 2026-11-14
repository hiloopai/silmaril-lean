module

public import Silmaril.Servers.Tensor.Defs
import Silmaril.Proofs.Servers.Tensor.Basic

/-!
# Independent endpoints: theorems

* **Refinement is monotone** in each factor of the tensor (`Model.tensor_mono`) and of the
  routed server (`Model.routed_mono`): refining one endpoint refines the composite.
* **Symmetric monoidal laws, up to the canonical maps of traces**: the tensor commutes
  (`Model.tensor_swap_iff`), associates (`Model.tensor_assoc_iff`) and has the unit
  `Model.unit` (`Model.tensor_unit_iff`).
* **Each factor is observed alone**: a sentence of the left endpoint holds of the tensor when
  it holds of the endpoint (`Model.tensor_sat_left`), and when the right endpoint can do nothing
  (`N.Tr []`), the left-only traces of the tensor are those of the left endpoint
  (`Model.tensor_inl_iff`).
* **Routes are disjoint** (`RoutedBy.isLeft_iff`): in a routed trace a request is on the left
  exactly when the router says so.
* **State isolation**: the histories of `Machine.tensor M₁ M₂` are the interleavings of
  histories of `M₁` and `M₂` (`Machine.tensor_hist_iff`).
* **Shared state is not independent** (`Tensor.shared_not_tensor`): two endpoints sharing a
  counter have, from count `0`, histories that two isolated counters have from no initial
  counts.
-/

@[expose] public section

namespace Silmaril.Servers

open Silmaril.Servers.Tensor

variable {A B C : Sig}

/-- **Refinement is monotone in each factor.** -/
theorem Model.tensor_mono {M M' : Model A} {N N' : Model B} (hM : M ≤ M') (hN : N ≤ N') :
    M.tensor N ≤ M'.tensor N' := fun _ ⟨h1, h2⟩ => ⟨hM _ h1, hN _ h2⟩

theorem Model.tensor_swap_iff (M : Model A) (N : Model B) (t : Trace (A.tensor B)) :
    (N.tensor M).Tr (t.map Event.swap) ↔ (M.tensor N).Tr t := by
  simp only [Model.tensor, Proofs.Servers.Tensor.left_swap, Proofs.Servers.Tensor.right_swap]
  exact And.comm

theorem Model.tensor_assoc_iff (M : Model A) (N : Model B) (P : Model C)
    (t : Trace ((A.tensor B).tensor C)) :
    (M.tensor (N.tensor P)).Tr (t.map Event.assoc) ↔ ((M.tensor N).tensor P).Tr t := by
  simp only [Model.tensor, Proofs.Servers.Tensor.left_assoc, Proofs.Servers.Tensor.left_right_assoc,
    Proofs.Servers.Tensor.right_right_assoc, and_assoc]

theorem Model.tensor_unit_iff (M : Model A) (t : Trace (A.tensor Sig.unit)) :
    (M.tensor Model.unit).Tr t ↔ M.Tr (Trace.left t) :=
  ⟨And.left, fun h => ⟨h, Proofs.Servers.Tensor.unit_nil _⟩⟩

theorem Model.tensor_inl_iff (M : Model A) {N : Model B} (hN : N.Tr []) (t : Trace A) :
    (M.tensor N).Tr (t.map Event.inl) ↔ M.Tr t := by
  simp only [Model.tensor, Proofs.Servers.Tensor.left_map_inl, Proofs.Servers.Tensor.right_map_inl]
  exact ⟨And.left, fun h => ⟨h, hN⟩⟩

theorem Model.tensor_sat_left {M : Model A} (N : Model B) {φ : Sen A} (h : M.Sat φ) :
    (M.tensor N).Sat fun t => φ (Trace.left t) := fun _ ht => h _ ht.1

theorem Model.tensor_sat_right (M : Model A) {N : Model B} {φ : Sen B} (h : N.Sat φ) :
    (M.tensor N).Sat fun t => φ (Trace.right t) := fun _ ht => h _ ht.2

theorem Model.routed_mono (ρ : Router A) {M M' N N' : Model A} (hM : M ≤ M') (hN : N ≤ N') :
    Model.routed ρ M N ≤ Model.routed ρ M' N' :=
  fun _ ⟨t', ht', hr, he⟩ => ⟨t', Model.tensor_mono hM hN _ ht', hr, he⟩

theorem RoutedBy.isLeft_iff {ρ : Router A} {t : Trace (A.tensor A)} (h : RoutedBy ρ t) {i : ReqId}
    {r : A.Req ⊕ A.Req} (hr : Event.recv i r ∈ t) : r.isLeft = true ↔ ρ (Sum.elim id id r) = true := by
  rw [h i r hr]

/-- **State isolation**: the histories of machines with isolated state are interleavings. -/
theorem Machine.tensor_hist_iff {σ τ : Type} (M₁ : Machine A σ) (M₂ : Machine B τ) (q₁ : σ)
    (q₂ : τ) (h : History (A.tensor B)) :
    (Machine.tensor M₁ M₂).Hist (q₁, q₂) h ↔
      History.Routed h ∧ M₁.Hist q₁ (History.left h) ∧ M₂.Hist q₂ (History.right h) :=
  Proofs.Servers.Tensor.tensor_hist_iff M₁ M₂ h q₁ q₂

/-- **Two endpoints sharing a counter are not two isolated counters**, from any counts. -/
theorem Tensor.shared_not_tensor (q₁ q₂ : Nat) :
    sharedCounter.Hist 0 ≠ (Machine.tensor counter counter).Hist (q₁, q₂) :=
  Proofs.Servers.Tensor.shared_not_tensor q₁ q₂

end Silmaril.Servers
