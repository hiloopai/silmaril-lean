module

public import Silmaril.Servers.Transport.Defs
import Silmaril.Proofs.Servers.Transport.Basic

/-!
# Transports: theorems

* **Refinement is a preorder** on transport models (`TModel.Refines.refl`, `.trans`).
* **Partial observation maps**: the satisfaction law for universal sentences
  (`PMap.sat_pull_iff`); the image is monotone (`PMap.image_mono`), so refinement of transport
  models gives refinement of their readings; composition (`PMap.image_comp`). Existential
  properties are not reflected through an undefined reading (`PMap.not_may_reflect`), and are
  when the model is total for the reading (`PMap.may_reflect_of_total`).
* **Stream readings forget chunking**: `streamIn` of a trace whose received chunks were split
  differently is the same (`streamIn_append_recv`).
-/

@[expose] public section

namespace Silmaril.Servers.Transport

variable {Addr α β γ : Type}

theorem TModel.Refines.refl (M : TModel Addr) : M.Refines M := subset_rfl

theorem TModel.Refines.trans {I M S : TModel Addr} (h₁ : I.Refines M) (h₂ : M.Refines S) :
    I.Refines S := subset_trans h₁ h₂

namespace PMap

/-- **The satisfaction law**: a model satisfies the pulled-back sentence iff its image
satisfies the sentence. -/
theorem sat_pull_iff (f : PMap α β) (M : Set α) (φ : β → Prop) :
    (∀ a ∈ M, f.pull φ a) ↔ ∀ b ∈ f.image M, φ b :=
  ⟨fun h _ ⟨a, ha, he⟩ => h a ha _ he, fun h a ha b he => h b ⟨a, ha, he⟩⟩

theorem image_mono (f : PMap α β) {M N : Set α} (h : M ⊆ N) : f.image M ⊆ f.image N :=
  fun _ ⟨a, ha, he⟩ => ⟨a, h ha, he⟩

theorem image_comp (g : PMap β γ) (f : PMap α β) (M : Set α) :
    (g.comp f).image M = g.image (f.image M) :=
  Proofs.Servers.Transport.image_comp g f M

/-- Existential properties are not reflected by a partial reading. -/
theorem not_may_reflect :
    ∃ (f : PMap Bool Unit) (M : Set Bool), (∃ a ∈ M, True) ∧ ¬ ∃ b ∈ f.image M, True :=
  ⟨fun _ => none, {true}, ⟨true, rfl, trivial⟩, fun ⟨_, ⟨_, _, h⟩, _⟩ => by cases h⟩

theorem may_reflect_of_total {f : PMap α β} {M : Set α} (ht : f.Total M) {P : α → Prop}
    (h : ∃ a ∈ M, P a) : ∃ b ∈ f.image M, ∃ a ∈ M, P a ∧ f a = some b :=
  Proofs.Servers.Transport.may_reflect_of_total ht h

end PMap

theorem streamIn_append_recv (c : Conn) (t : TTrace Addr) (xs ys : List UInt8) :
    streamIn c (.recv c xs :: .recv c ys :: t) = streamIn c (.recv c (xs ++ ys) :: t) := by
  simp [streamIn, unitsIn]

end Silmaril.Servers.Transport
