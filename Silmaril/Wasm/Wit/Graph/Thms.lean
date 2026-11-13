module

public import Silmaril.Wasm.Wit.Graph.Defs

/-!
# Acyclicity of finite dependency graphs: Kahn's algorithm is sound and complete

* `kahn_sound`: when `kahn` succeeds, `krank` ranks the graph and is below the number
  of nodes;
* `kahn_complete`: any ranking makes `kahn` succeed (the pending node of least rank is
  always ready);
* `kahn_iff`: `kahn deps nodes = true ↔ Acyclic deps nodes`;
* `acyclic_iff_edges`: the same acyclicity stated for an edge relation `E` whose edges
  are exactly the `deps` edges between nodes.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Graph

variable {α : Type} [DecidableEq α] (deps : α → List α)

theorem kahn_of_any {rest : List α} (h : rest.any (ready deps rest) = true) :
    kahn deps rest = kahn deps (nextRound deps rest) := by
  rw [kahn]; simp only [h, ↓reduceDIte]

theorem kahn_of_not_any {rest : List α} (h : ¬ rest.any (ready deps rest) = true) :
    kahn deps rest = rest.isEmpty := by
  rw [kahn, dite_eq_right_of_eq_false (eq_false h)]

theorem krank_of_any {rest : List α} (h : rest.any (ready deps rest) = true) (a : α) :
    krank deps rest a =
      if ready deps rest a then 0 else krank deps (nextRound deps rest) a + 1 := by
  rw [krank]; simp only [h, ↓reduceDIte]

theorem not_mem_of_ready {rest : List α} {a b : α} (hr : ready deps rest a = true)
    (hb : b ∈ deps a) : b ∉ rest := by
  have h : (!rest.contains b) = true := List.all_eq_true.mp hr b hb
  simpa using h

theorem mem_nextRound {rest : List α} {a : α} :
    a ∈ nextRound deps rest ↔ a ∈ rest ∧ ready deps rest a = false := by
  simp [nextRound]

theorem nextRound_subset {rest : List α} {a : α} (h : a ∈ nextRound deps rest) :
    a ∈ rest :=
  ((mem_nextRound deps).mp h).1

/-- One round preserves rankedness backwards: if the pending nodes are ranked by
`krank`, so are the nodes before the round. -/
theorem ranked_step {rest : List α} (h : rest.any (ready deps rest) = true)
    (ih : Ranked deps (nextRound deps rest) (krank deps (nextRound deps rest))) :
    Ranked deps rest (krank deps rest) := by
  intro a ha b hb hbr
  have hk : ∀ x, krank deps rest x = _ := krank_of_any deps h
  cases hra : ready deps rest a with
  | true => exact absurd hbr (not_mem_of_ready deps hra hb)
  | false =>
    have ha' : a ∈ nextRound deps rest := (mem_nextRound deps).mpr ⟨ha, hra⟩
    cases hrb : ready deps rest b with
    | true => simp [hk, hra, hrb]
    | false =>
      have hb' : b ∈ nextRound deps rest := (mem_nextRound deps).mpr ⟨hbr, hrb⟩
      have hlt := ih a ha' b hb hb'
      simp [hk, hra, hrb, hlt]

/-- One round preserves the bound `krank < length` backwards. -/
theorem bound_step {rest : List α} (h : rest.any (ready deps rest) = true)
    (ih : ∀ a ∈ nextRound deps rest, krank deps (nextRound deps rest) a <
      (nextRound deps rest).length) :
    ∀ a ∈ rest, krank deps rest a < rest.length := by
  intro a ha
  have hlen : (nextRound deps rest).length < rest.length := nextRound_lt deps h
  rw [krank_of_any deps h]
  cases hra : ready deps rest a with
  | true => exact List.length_pos_of_mem ha
  | false =>
    have ha' : a ∈ nextRound deps rest := (mem_nextRound deps).mpr ⟨ha, hra⟩
    have := ih a ha'
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

/-- When `kahn` succeeds, `krank` ranks the graph and stays below the number of
nodes. -/
theorem kahn_sound (rest : List α) (hk : kahn deps rest = true) :
    Ranked deps rest (krank deps rest) ∧ ∀ a ∈ rest, krank deps rest a < rest.length := by
  induction rest using kahn.induct deps with
  | case1 rest h ih =>
    have hk' : kahn deps (nextRound deps rest) = true := by rwa [kahn_of_any deps h] at hk
    have ih' := ih hk'
    exact ⟨ranked_step deps h ih'.1, bound_step deps h ih'.2⟩
  | case2 rest h =>
    have hnil : rest = [] := by simpa [kahn_of_not_any deps h] using hk
    subst hnil
    exact ⟨fun _ ha => absurd ha List.not_mem_nil, fun _ ha => absurd ha List.not_mem_nil⟩

omit [DecidableEq α] in
theorem exists_min (r : α → Nat) : ∀ (l : List α), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, r m ≤ r x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min r (b :: l) (by simp)
    by_cases hle : r a ≤ r m
    · exact ⟨a, by simp, by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans hle (hmin x hx)⟩
    · exact ⟨m, List.mem_cons_of_mem _ hm, by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hmin x hx⟩

omit [DecidableEq α] in
theorem ranked_mono {nodes nodes' : List α} {r : α → Nat} (hR : Ranked deps nodes r)
    (hsub : ∀ a ∈ nodes', a ∈ nodes) : Ranked deps nodes' r :=
  fun a ha b hb hb' => hR a (hsub a ha) b hb (hsub b hb')

theorem ready_of_min {rest : List α} {r : α → Nat} (hR : Ranked deps rest r) {m : α}
    (hm : m ∈ rest) (hmin : ∀ x ∈ rest, r m ≤ r x) : ready deps rest m = true := by
  refine List.all_eq_true.mpr fun b hb => ?_
  have hnot : b ∉ rest := fun hbr => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hR m hm b hb hbr)
    (hmin b hbr))
  simpa using hnot

/-- Any ranking makes `kahn` succeed. -/
theorem kahn_complete (rest : List α) {r : α → Nat} (hR : Ranked deps rest r) :
    kahn deps rest = true := by
  induction rest using kahn.induct deps with
  | case1 rest h ih =>
    rw [kahn_of_any deps h]
    exact ih (ranked_mono deps hR fun a ha => nextRound_subset deps ha)
  | case2 rest h =>
    rw [kahn_of_not_any deps h]
    cases rest with
    | nil => rfl
    | cons a l =>
      obtain ⟨m, hm, hmin⟩ := exists_min r (a :: l) (by simp)
      exact absurd (List.any_eq_true.mpr ⟨m, hm, ready_of_min deps hR hm hmin⟩) h

theorem kahn_iff (nodes : List α) : kahn deps nodes = true ↔ Acyclic deps nodes :=
  ⟨fun h => ⟨_, (kahn_sound deps nodes h).1⟩, fun ⟨_, hR⟩ => kahn_complete deps nodes hR⟩

omit [DecidableEq α] in
/-- Acyclicity for an edge relation that has exactly the `deps` edges between nodes. -/
theorem acyclic_iff_edges {nodes : List α} {E : α → α → Prop}
    (hE : ∀ a b, E a b ↔ a ∈ nodes ∧ b ∈ deps a ∧ b ∈ nodes) :
    Acyclic deps nodes ↔ ∃ r : α → Nat, ∀ a b, E a b → r b < r a := by
  constructor
  · rintro ⟨r, hR⟩
    exact ⟨r, fun a b he => have h := (hE a b).mp he; hR a h.1 b h.2.1 h.2.2⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, fun a ha b hb hb' => hr a b ((hE a b).mpr ⟨ha, hb, hb'⟩)⟩

/-- A successful `kahn` gives a ranking of the edge relation bounded by the number of
nodes. -/
theorem kahn_bounded_edges {nodes : List α} {E : α → α → Prop}
    (hE : ∀ a b, E a b ↔ a ∈ nodes ∧ b ∈ deps a ∧ b ∈ nodes) (hk : kahn deps nodes = true) :
    ∃ r : α → Nat, (∀ a b, E a b → r b < r a) ∧ ∀ a ∈ nodes, r a < nodes.length := by
  have h := kahn_sound deps nodes hk
  exact ⟨krank deps nodes, fun a b he => have h' := (hE a b).mp he;
    h.1 a h'.1 b h'.2.1 h'.2.2, h.2⟩

end Silmaril.Wasm.Wit.Graph
