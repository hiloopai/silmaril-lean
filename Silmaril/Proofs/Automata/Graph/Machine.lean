module

public import Silmaril.Automata.Graph.Defs
public import Silmaril.Automata.Machine.Thms

/-!
# State machines as rooted graphs: proofs
-/

@[expose] public section

namespace Silmaril.Proofs.Automata.Graph

open Silmaril.Machine.Graph Silmaril.Automata Silmaril.Automata.Graph

variable {S L : Type} [FinNamed S] [FinNamed L] [DecidableEq S]

theorem stateIndex_lt (s : S) : stateIndex s < (FinNamed.elems (α := S)).length :=
  List.idxOf_lt_length_of_mem (FinNamed.complete s)

theorem getElem?_stateIndex (s : S) : (FinNamed.elems (α := S))[stateIndex s]? = some s := by
  rw [List.getElem?_eq_getElem (stateIndex_lt s)]
  exact congrArg some (List.getElem_idxOf (stateIndex_lt s))

theorem stateIndex_inj {s t : S} (h : stateIndex s = stateIndex t) : s = t := by
  have := getElem?_stateIndex s
  rw [h, getElem?_stateIndex t] at this
  exact (Option.some.inj this).symm

theorem edge_iff (M : NMachine S L) (init s : S) (j : Nat) :
    (M.toDigraph init).Edge (stateIndex s) j ↔ ∃ t, j = stateIndex t ∧ ∃ l, t ∈ M.step s l := by
  simp only [Digraph.Edge, Digraph.step, NMachine.toDigraph, getElem?_stateIndex, List.mem_filter,
    List.mem_map, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨t, ⟨-, l, -, hl⟩, rfl⟩, -⟩; exact ⟨t, rfl, l, hl⟩
  · rintro ⟨t, rfl, l, hl⟩
    exact ⟨⟨t, ⟨FinNamed.complete t, l, FinNamed.complete l, hl⟩, rfl⟩, decide_eq_true (stateIndex_lt t)⟩

theorem walk_sound (M : NMachine S L) (init : S) {j : Nat}
    (h : (M.toDigraph init).Walk (fun _ => true) j) :
    ∃ t, j = stateIndex t ∧ ReachVia M.toLTS (fun _ => True) init t := by
  induction h with
  | entry _ => exact ⟨init, rfl, Relation.ReflTransGen.refl⟩
  | step _ he _ ih =>
    obtain ⟨s, rfl, hs⟩ := ih
    obtain ⟨t, rfl, l, hl⟩ := (edge_iff M init s _).mp he
    exact ⟨t, rfl, Relation.ReflTransGen.tail hs ⟨l, trivial, hl⟩⟩

theorem walk_complete (M : NMachine S L) (init : S) {t : S}
    (h : ReachVia M.toLTS (fun _ => True) init t) :
    (M.toDigraph init).Walk (fun _ => true) (stateIndex t) := by
  induction h with
  | refl => exact .entry rfl
  | tail _ hst ih =>
    obtain ⟨l, -, hl⟩ := hst
    exact .step ih ((edge_iff M init _ _).mpr ⟨_, rfl, l, hl⟩) rfl

theorem machine_reachable_iff (M : NMachine S L) (init t : S) :
    (M.toDigraph init).Reachable (stateIndex t) ↔ ReachVia M.toLTS (fun _ => True) init t := by
  rw [Digraph.reachable_iff_walk]
  constructor
  · intro h
    obtain ⟨t', ht, hr⟩ := walk_sound M init h
    rw [stateIndex_inj ht]; exact hr
  · exact walk_complete M init

theorem dmachine_reachable_iff (M : DMachine S L) (init t : S) :
    (M.toDigraph init).Reachable (stateIndex t) ↔ ReachVia M.toLTS (fun _ => True) init t := by
  rw [← M.toN_toLTS]; exact machine_reachable_iff M.toN init t

end Silmaril.Proofs.Automata.Graph
