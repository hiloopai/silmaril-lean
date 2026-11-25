module

public import Silmaril.Parse.DecodeGraph.Defs

public section

namespace Silmaril.Parse.DecodeGraph.Proofs

open scoped SetRel

variable {Context Buffer Source Middle Target : Type*}

theorem onSpan_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    onSpan (first ○ second) = onSpan first ○ onSpan second := by
  ext ⟨⟨source, width⟩, ⟨target, count⟩⟩
  change ((∃ middle, source ~[first] middle ∧ middle ~[second] target) ∧ width = count) ↔
    ∃ middle : Middle × Nat,
      (source ~[first] middle.1 ∧ width = middle.2) ∧ (middle.1 ~[second] target ∧ middle.2 = count)
  constructor
  · rintro ⟨⟨middle, left, right⟩, rfl⟩
    exact ⟨(middle, width), ⟨left, rfl⟩, ⟨right, rfl⟩⟩
  · rintro ⟨⟨middle, _⟩, ⟨left, firstSpan⟩, ⟨right, secondSpan⟩⟩
    exact ⟨⟨middle, left, right⟩, firstSpan.trans secondSpan⟩

theorem transport_mono {first first' : SetRel Source Target} {graph graph' : Graph Context Buffer Source}
    (hrel : first ⊆ first') (hgraph : graph ⊆ graph') :
    transport first graph ⊆ transport first' graph' := by
  apply SetRel.comp_subset_comp hgraph
  rintro ⟨_, _⟩ ⟨related, span⟩
  exact ⟨hrel related, span⟩

theorem pointwise_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    pointwise (first ○ second) = pointwise first ○ pointwise second := by
  ext ⟨source, target⟩
  change List.Forall₂ (fun left right => left ~[first ○ second] right) source target ↔
    ∃ middle, List.Forall₂ (fun left right => left ~[first] right) source middle ∧
      List.Forall₂ (fun left right => left ~[second] right) middle target
  constructor
  · intro aligned
    induction aligned with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons head _ ih =>
      obtain ⟨mid, left, right⟩ := SetRel.mem_comp.mp head
      obtain ⟨middle, lefts, rights⟩ := ih
      exact ⟨mid :: middle, .cons left lefts, .cons right rights⟩
  · rintro ⟨middle, lefts, rights⟩
    induction lefts generalizing target with
    | nil => cases rights; exact .nil
    | cons head _ ih =>
      cases rights with
      | cons otherHead rest => exact .cons ⟨_, head, otherHead⟩ (ih _ rest)

end Silmaril.Parse.DecodeGraph.Proofs
