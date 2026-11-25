module

public import Silmaril.Parse.DecodeGraph.Defs
import Silmaril.Proofs.Parse.DecodeGraph.Laws

public section

namespace Silmaril.Parse.DecodeGraph

open scoped SetRel

variable {Context Buffer Source Middle Target : Type*}

theorem completeFor_unique {view : ByteView Buffer} {graph : Graph Context Buffer Source} {reference}
    (complete : CompleteFor view graph reference) (unique : Deterministic graph)
    {input left right} (valid : ValidWindow view input) (hl : (input, left) ∈ overView view reference)
    (hr : (input, right) ∈ overView view reference) : left = right :=
  unique (complete valid hl) (complete valid hr)

theorem overView_mono (view : ByteView Buffer) {first second : Reference Context Source} (included : first ⊆ second) :
    overView view first ⊆ overView view second := fun _ ⟨valid, success⟩ => ⟨valid, included success⟩

theorem ignoreContext_mono {first second : Graph Unit Buffer Source} (included : first ⊆ second) :
    ignoreContext (Context := Context) first ⊆ ignoreContext second := fun _ success => included success

theorem ignoreContext_subset_iff (ctx : Context) {first second : Graph Unit Buffer Source} :
    ignoreContext (Context := Context) first ⊆ ignoreContext second ↔ first ⊆ second :=
  ⟨fun included ⟨⟨⟨⟩, bytes, stop, pos⟩, result⟩ success =>
      included (a := (⟨ctx, bytes, stop, pos⟩, result)) success,
    ignoreContext_mono⟩

/-- Inclusion does not resolve a conflict: the join retains both successes. -/
theorem not_deterministic_sup {first second : Graph Context Buffer Source} {input left right}
    (hleft : (input, left) ∈ first) (hright : (input, right) ∈ second) (different : left ≠ right) :
    ¬ Deterministic (first ⊔ second) :=
  fun unique => different (unique (Or.inl hleft) (Or.inr hright))

@[simp] theorem onSpan_id : onSpan (SetRel.id : SetRel Source Source) = SetRel.id := by
  ext ⟨⟨left, width⟩, ⟨right, count⟩⟩
  simp [onSpan, SetRel.id]

theorem onSpan_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    onSpan (first ○ second) = onSpan first ○ onSpan second :=
  Proofs.onSpan_comp first second

@[simp] theorem transport_id (graph : Graph Context Buffer Source) : transport SetRel.id graph = graph := by
  simp [transport]

theorem transport_comp (first : SetRel Source Middle) (second : SetRel Middle Target)
    (graph : Graph Context Buffer Source) :
    transport (first ○ second) graph = transport second (transport first graph) := by
  simp only [transport, onSpan_comp, SetRel.comp_assoc]

theorem transport_mono {first first' : SetRel Source Target} {graph graph' : Graph Context Buffer Source}
    (hrel : first ⊆ first') (hgraph : graph ⊆ graph') :
    transport first graph ⊆ transport first' graph' :=
  Proofs.transport_mono hrel hgraph

@[simp] theorem map_id (graph : Graph Context Buffer Source) : map id graph = graph :=
  transport_id graph

theorem map_comp (first : Source → Middle) (second : Middle → Target) (graph : Graph Context Buffer Source) :
    map (second ∘ first) graph = map second (map first graph) := by
  simp only [map, Function.graph_comp, transport_comp]

@[simp] theorem pointwise_id : pointwise (SetRel.id : SetRel Source Source) = SetRel.id := by
  ext ⟨left, right⟩
  simp [pointwise]

theorem pointwise_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    pointwise (first ○ second) = pointwise first ○ pointwise second :=
  Proofs.pointwise_comp first second

theorem pointwise_mono {first second : SetRel Source Target} (h : first ⊆ second) :
    pointwise first ⊆ pointwise second := fun _ aligned => List.Forall₂.imp (fun _ _ hab => h hab) aligned

theorem pointwise_append {rel : SetRel Source Target} {left right left' right'}
    (first : (left, right) ∈ pointwise rel) (second : (left', right') ∈ pointwise rel) :
    (left ++ left', right ++ right') ∈ pointwise rel := List.rel_append first second

end Silmaril.Parse.DecodeGraph
