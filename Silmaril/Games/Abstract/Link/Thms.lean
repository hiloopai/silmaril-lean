module

public import Silmaril.Games.Abstract.Link.Defs
public import Silmaril.Games.Abstract.Machine.Thms
public import Silmaril.Games.Abstract.Hiding.Thms
import Silmaril.Proofs.Games.Abstract.Link.Basic

/-!
# Linking with hiding: theorems

* `mem_inf_pull`: the synchronised joint plays are the legal joint plays whose
  views are plays of the components.
* `link_mono`: linking of trace models is monotone in both components, so
  refinement is a congruence for linking.
* `traces_link`: the traces of the linked machine are the external images of
  the legal joint plays whose views are traces of the components. This is the
  operational content of synchronisation and hiding.
* `denote_link_le`: erasing the states of the linked machine never gives more
  than linking the erased components.
* **`denote_link`**: for components whose traces are closed (receptive
  machines), state erasure commutes with linking:
  `(Machine.link Λ M₁ M₂).denote = TraceModel.link Λ M₁.denote M₂.denote`.

As in `Silmaril.Games.Composition`, hiding makes internal divergence invisible:
an infinite internal exchange shows up as the play reached before it began.
-/

public section

namespace Silmaril.Games.Abstract

universe u

variable {G₁ G₂ G : Game.{u}} {Λ : LinkSpec G₁ G₂ G}

namespace TraceModel

/-- The synchronised joint plays. -/
theorem mem_inf_pull {T₁ : TraceModel G₁} {T₂ : TraceModel G₂} {u : List Λ.L.Move} :
    u ∈ pull Λ.π₁ T₁ ⊓ pull Λ.π₂ T₂ ↔
      u ∈ Λ.L.Legal ∧ u.filterMap Λ.π₁.map ∈ T₁ ∧ u.filterMap Λ.π₂.map ∈ T₂ :=
  Silmaril.Proofs.Games.Abstract.Link.mem_inf_pull

/-- Linking is monotone in both components. -/
theorem link_mono {T₁ T₁' : TraceModel G₁} {T₂ T₂' : TraceModel G₂} (h₁ : T₁ ≤ T₁')
    (h₂ : T₂ ≤ T₂') : link Λ T₁ T₂ ≤ link Λ T₁' T₂' :=
  hide_mono _ (inf_le_inf (pull_mono _ h₁) (pull_mono _ h₂))

end TraceModel

namespace Machine

variable {M₁ : Machine G₁} {M₂ : Machine G₂}

/-- The traces of a linked machine. -/
theorem traces_link :
    (link Λ M₁ M₂).traces = (List.filterMap Λ.ext.map) ''
      {u | u ∈ Λ.L.Legal ∧ u.filterMap Λ.π₁.map ∈ M₁.traces ∧
        u.filterMap Λ.π₂.map ∈ M₂.traces} :=
  Silmaril.Proofs.Games.Abstract.Link.traces_link

/-- Erasing the linked machine gives at most the link of the erasures. -/
theorem denote_link_le : (link Λ M₁ M₂).denote ≤ TraceModel.link Λ M₁.denote M₂.denote :=
  Silmaril.Proofs.Games.Abstract.Link.denote_link_le

/-- For receptive components, state erasure commutes with linking. -/
theorem denote_link (h₁ : G₁.Closed M₁.traces) (h₂ : G₂.Closed M₂.traces) :
    (link Λ M₁ M₂).denote = TraceModel.link Λ M₁.denote M₂.denote :=
  Silmaril.Proofs.Games.Abstract.Link.denote_link h₁ h₂

end Machine

end Silmaril.Games.Abstract
