module

public import Silmaril.Servers.Context.Defs
public import Silmaril.Servers.Hosts.Thms
import Silmaril.Proofs.Servers.Context.Basic

/-!
# Contextual equivalence and HTTP observations: theorems

* **The lift** (`Reading.equivAt_of_ctxEquivOn`): components contextually equivalent over the
  contexts a reading uses have equal HTTP behaviours in every environment. With a monotone
  reading, contextual refinement gives HTTP refinement in every environment
  (`Reading.refinesAt_of_ctxRefinesOn`); image readings are monotone (`Reading.image_mono`).
  Contextual equivalence over all contexts is a special case (`Reading.equivAt_of_ctxEquiv`).
* **Reflection under full abstraction** (`Reading.ctxEquivOn_of_equivAt`): when every context
  of a class observes a function of the HTTP behaviour, HTTP equivalence gives contextual
  equivalence over that class. This is an assumption, not a fact about a language.
* **What does not follow**: an arbitrary projection (`ctxEquiv_not_preserves_projection`), a
  reading through a context outside the class (`ctxEquivOn_not_preserves_outside`), and
  reflection without full abstraction (`reading_not_reflects`).
-/

@[expose] public section

namespace Silmaril.Servers.Context

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts

variable {L : Lang} {X : Type} {A : Sig}

/-- **Contextual equivalence over the reading's contexts gives HTTP observational equivalence
in every environment.** -/
theorem Reading.equivAt_of_ctxEquivOn (ρ : Reading L X A) {c₁ c₂ : L.Comp}
    (h : CtxEquivOn ρ.ctxs c₁ c₂) : EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) :=
  fun x _ => congrArg ρ.read (h (ρ.ctx x) ⟨x, rfl⟩)

theorem Reading.equivAt_of_ctxEquiv (ρ : Reading L X A) {c₁ c₂ : L.Comp} (h : CtxEquiv c₁ c₂) :
    EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) :=
  ρ.equivAt_of_ctxEquivOn fun K _ => h K trivial

/-- **With a monotone reading, contextual refinement gives HTTP refinement in every
environment.** -/
theorem Reading.refinesAt_of_ctxRefinesOn (ρ : Reading L X A) (hm : Monotone ρ.read)
    {c₁ c₂ : L.Comp} (h : CtxRefinesOn ρ.ctxs c₁ c₂) : RefinesAt Set.univ (ρ.beh c₁) (ρ.beh c₂) :=
  fun x _ => hm (h (ρ.ctx x) ⟨x, rfl⟩)

theorem Reading.image_mono (ctx : X → L.Ctx) (f : L.Obs → Obs A) :
    Monotone (Reading.image ctx f).read := fun _ _ h => Set.image_mono h

/-- **Reflection under full abstraction**: if every context of `Ks` observes a function of the
HTTP behaviour, HTTP equivalence gives contextual equivalence over `Ks`. -/
theorem Reading.ctxEquivOn_of_equivAt (ρ : Reading L X A) {Ks : Set L.Ctx}
    (hfa : ∀ K ∈ Ks, ∃ G : Open X A → Set L.Obs, ∀ c, L.run K c = G (ρ.beh c))
    {c₁ c₂ : L.Comp} (h : EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂)) : CtxEquivOn Ks c₁ c₂ :=
  fun K hK => let ⟨G, hG⟩ := hfa K hK
    by rw [hG, hG]; exact congrArg G (funext fun x => h x trivial)

/-- **An arbitrary projection is not preserved**: contextually equivalent components whose
projections differ. -/
theorem ctxEquiv_not_preserves_projection (A : Sig) :
    ∃ (L : Lang) (c₁ c₂ : L.Comp) (π : L.Comp → Beh A), CtxEquiv c₁ c₂ ∧ π c₁ ≠ π c₂ :=
  Proofs.Servers.Context.not_projection A

/-- **A reading through a context outside the class is not preserved.** -/
theorem ctxEquivOn_not_preserves_outside (A : Sig) :
    ∃ (L : Lang) (Ks : Set L.Ctx) (ρ : Reading L Unit A) (c₁ c₂ : L.Comp),
      CtxEquivOn Ks c₁ c₂ ∧ ¬ EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) :=
  Proofs.Servers.Context.not_outside A

/-- **HTTP equivalence does not reflect** to contextual equivalence in general. -/
theorem reading_not_reflects (A : Sig) :
    ∃ (L : Lang) (ρ : Reading L Unit A) (c₁ c₂ : L.Comp),
      EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) ∧ ¬ CtxEquiv c₁ c₂ :=
  Proofs.Servers.Context.not_reflects A

end Silmaril.Servers.Context
