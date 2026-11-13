module

public import Silmaril.Machine.CBackend.Graph.Loops.Defs
/-!
# Reducibility, and the nesting of natural loops

`Graph/Loops.lean` defines `BackEdge` and `naturalLoop` and proves nothing about
them. This file proves what a region-recovery pass needs before it can turn a
control-flow graph into nested single-entry regions, and the first thing to say
is which hypothesis buys what, because it is not what one expects.

**Proper nesting needs reachability, not reducibility.** Two natural loops with
distinct headers are disjoint or nested in *any* digraph; what the proof needs
is that the nodes involved are reachable, because `Dominates` is vacuously true
at an unreachable node and so an edge into dead code is a back edge by default
and the "loops" it closes nest with nothing. `Pruned` is that hypothesis.
**Reducibility earns a different theorem**: `Reducible.exists_backEdge`, every
cycle contains a back edge — no cycle escapes the loop analysis — which is what
the next rung actually needs and what an irreducible graph denies. The two are
independent and each statement below says which one it rests on.

In detail:

* `BackEdge.dominates_naturalLoop` — the header of a natural loop dominates
  every node of that loop, so the loop is a single-entry region. **This needs no
  reducibility**: it is a consequence of the definition of `naturalLoop` and of
  the back edge's dominance condition alone.
* `naturalLoop_nested` — two natural loops with distinct headers are disjoint or
  one contains the other. This is the fact that makes a loop *forest*, and hence
  a nest of λSSA `cfg`s, possible. It needs no reducibility either; what it does
  need is that the nodes involved are reachable, because dominance is vacuously
  true at an unreachable node and so a back edge into unreachable code carries no
  information. `Pruned` is that condition, and it is decidable.

Loops with the *same* header are deliberately not covered: two back edges to one
header can have incomparable natural loops — the two arms of a `continue` in an
`if` — and the standard remedy is to take their union, which is what
`naturalLoops` does.

## What reducibility is for

`Reducible` is defined as **deleting the back edges leaves an acyclic graph**.
This is one of the standard equivalent definitions of a reducible flow graph,
and it is the one that says what a structuring pass wants to hear: every cycle
of the graph contains a back edge, so every cycle is accounted for by some
natural loop and no cycle is left over to defeat structuring.
`Reducible.exists_backEdge` is that statement. Irreducible graphs — a loop with
two entries, as a goto into the middle of a loop produces — have cycles
containing no back edge, and no amount of natural-loop analysis will structure
them.

Reducibility is checked, not assumed, and it is not used to prove nesting; the
two are independent and the file says which theorem rests on what.

Not provided: T1-T2 reduction, the loop nesting forest as a data structure,
Lengauer-Tarjan, or irreducible-loop transformations (node splitting).
-/

@[expose] public section

namespace Silmaril.Machine.Graph

namespace Digraph

variable {g : Digraph} {a b c x y src dst : Nat}

/-! ## Reachability between arbitrary nodes

`Reachable` is reachability from the entry. Acyclicity needs reachability from
an arbitrary node, which is the same fixpoint with the entry moved. -/

/-- `b` is reachable from `a`, which is `Reachable` in the graph re-rooted at
`a`. -/
def Reaches (g : Digraph) (a b : Nat) : Prop := ({ g with entry := a } : Digraph).Reachable b

instance : Decidable (g.Reaches a b) := inferInstanceAs (Decidable (Reachable _ _))

/-- Re-rooting changes no edge, so `Reaches` is exactly "some path leads from
`a` to `b`". -/
theorem reaches_iff_path : g.Reaches a b ↔ ∃ ls, g.Path a b ls := Iff.rfl

/-- Every node reaches itself, by the one-node path. -/
theorem Reaches.refl (g : Digraph) (a : Nat) : g.Reaches a a :=
  reaches_iff_path.mpr ⟨[a], path_singleton g a⟩

/-- A path witnesses reachability. -/
theorem Reaches.of_path {ls : List Nat} (h : g.Path a b ls) : g.Reaches a b :=
  reaches_iff_path.mpr ⟨ls, h⟩

/-- Reachability is transitive, by concatenating the two paths. -/
theorem Reaches.trans (hab : g.Reaches a b) (hbc : g.Reaches b c) : g.Reaches a c := by
  obtain ⟨p, hp⟩ := reaches_iff_path.mp hab
  obtain ⟨q, hq⟩ := reaches_iff_path.mp hbc
  exact .of_path (hp.append hq)

/-- An edge followed by a reachable run is a reachable run. -/
theorem Reaches.head (he : g.Edge a b) (h : g.Reaches b c) : g.Reaches a c :=
  (Reaches.of_path ((path_singleton g a).snoc he)).trans h

/-! ## Acyclicity -/

/-- No node of the graph lies on a cycle. The quantifier ranges over the nodes
of the graph only, which loses nothing: every edge target is a node, so every
node on a cycle is one. -/
def Acyclic (g : Digraph) : Prop :=
  ∀ a ∈ List.range g.size, ∀ b ∈ g.step a, ¬ g.Reaches b a

instance : Decidable g.Acyclic := inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/-- The far end of a path is a node of the graph, unless the path never left
its starting node. -/
theorem eq_or_lt_size_of_path : ∀ {ls : List Nat} {a b : Nat}, g.Path a b ls → b = a ∨ b < g.size
  | [], _, _, h => absurd rfl h.ne_nil
  | [x], a, b, h => by
    have hx : x = a := by simpa using h.1
    have hb : x = b := by simpa using h.2.1
    exact .inl (hb ▸ hx)
  | x :: c :: t, a, b, h => by
    have hx : x = a := by simpa using h.1
    have hch := List.isChain_cons_cons.mp h.2.2
    have hp : g.Path c b (c :: t) :=
      ⟨rfl, by rw [← List.getLast?_cons_cons]; exact h.2.1, hch.2⟩
    rcases eq_or_lt_size_of_path hp with rfl | hb
    · exact .inr (lt_size_of_edge hch.1)
    · exact .inr hb

/-- Every node of a path is a node of the graph, once its first node is. -/
theorem mem_lt_size_of_path {ls : List Nat} (h : g.Path a b ls) (ha : a < g.size) :
    ∀ x ∈ ls, x < g.size := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rcases eq_or_lt_size_of_path (h.take hi) with heq | hlt
  · exact heq ▸ ha
  · exact hlt

/-- An acyclic graph has no cycle through any node at all, in range or not. -/
theorem Acyclic.not_reaches (h : g.Acyclic) (he : g.Edge a b) : ¬ g.Reaches b a := by
  intro hr
  obtain ⟨ls, hp⟩ := reaches_iff_path.mp hr
  have ha : a < g.size := by
    rcases eq_or_lt_size_of_path hp with heq | hlt
    · rw [heq]; exact lt_size_of_edge he
    · exact hlt
  exact h a (List.mem_range.mpr ha) b he hr

/-! ## Reducibility -/

/-- The graph with every back edge deleted. -/
def dropBackEdges (g : Digraph) : Digraph :=
  { g with succ := fun a => (g.succ a).filter fun b => !decide (g.BackEdge a b) }

/-- Deleting edges changes no node. -/
@[simp] theorem dropBackEdges_size (g : Digraph) : g.dropBackEdges.size = g.size := rfl

/-- Deleting edges changes no entry. -/
@[simp] theorem dropBackEdges_entry (g : Digraph) : g.dropBackEdges.entry = g.entry := rfl

/-- An edge survives deletion exactly when it is not a back edge. -/
theorem edge_dropBackEdges : g.dropBackEdges.Edge a b ↔ (g.Edge a b ∧ ¬ g.BackEdge a b) := by
  simp only [Edge, step, dropBackEdges]
  constructor
  · intro h
    obtain ⟨hm, hlt⟩ := List.mem_filter.mp h
    obtain ⟨hm', hnb⟩ := List.mem_filter.mp hm
    exact ⟨List.mem_filter.mpr ⟨hm', hlt⟩, by simpa using hnb⟩
  · rintro ⟨h, hnb⟩
    obtain ⟨hm, hlt⟩ := List.mem_filter.mp h
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm, by simpa using hnb⟩, hlt⟩

/-- **A digraph is reducible when deleting its back edges leaves an acyclic
graph**, equivalently when every cycle contains an edge whose target dominates
its source. An irreducible graph has a cycle with two entries, which no natural
loop covers. -/
def Reducible (g : Digraph) : Prop := g.dropBackEdges.Acyclic

instance : Decidable g.Reducible := inferInstanceAs (Decidable (Acyclic _))

/-- A chain whose consecutive pairs all satisfy a second relation is a chain for
that relation. The hypothesis is stated over all members, which is all the
callers below need and all that is convenient to supply. -/
theorem isChain_of_mem {R S : Nat → Nat → Prop} :
    ∀ {ls : List Nat}, List.IsChain R ls → (∀ x ∈ ls, ∀ y ∈ ls, R x y → S x y) →
      List.IsChain S ls
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | x :: c :: t, h, hmono => by
    have hch := List.isChain_cons_cons.mp h
    refine List.isChain_cons_cons.mpr ⟨hmono x (by simp) c (by simp) hch.1, ?_⟩
    exact isChain_of_mem hch.2 fun u hu v hv => hmono u (by simp [hu]) v (by simp [hv])

/-- **Every cycle of a reducible graph contains a back edge.** This is what
makes natural loops exhaustive: no cycle escapes the loop analysis. -/
theorem Reducible.exists_backEdge (h : g.Reducible) {ls : List Nat} (hp : g.Path a a ls)
    (hlen : 2 ≤ ls.length) : ∃ x y, x ∈ ls ∧ y ∈ ls ∧ g.BackEdge x y := by
  by_contra hcon
  push Not at hcon
  have hchain : List.IsChain g.dropBackEdges.Edge ls :=
    isChain_of_mem hp.2.2 fun u hu v hv huv =>
      edge_dropBackEdges.mpr ⟨huv, fun hb => (hcon u v hu hv) hb⟩
  have hp' : g.dropBackEdges.Path a a ls := ⟨hp.1, hp.2.1, hchain⟩
  match ls, hlen, hp' with
  | x :: c :: t, _, hp' =>
    have hx : x = a := by simpa using hp'.1
    have hch := List.isChain_cons_cons.mp hp'.2.2
    have hsuf : g.dropBackEdges.Path c a (c :: t) :=
      ⟨rfl, by rw [← List.getLast?_cons_cons]; exact hp'.2.1, hch.2⟩
    exact h.not_reaches (hx ▸ hch.1) (Reaches.of_path hsuf)

/-! ## Membership in a natural loop

`naturalLoop` is computed as a fixpoint on the reversed graph. These lemmas turn
that computation into the path statement every proof below uses: a node is in
the natural loop of `src → dst` exactly when it is `dst` or it reaches `src`
along a path avoiding `dst`.

The two directions are not symmetric in their hypotheses. Reading a reversed
path forwards needs nothing; reading a forward path backwards needs its nodes to
be nodes of the graph, because `Digraph.edge_reverse` carries that side
condition. So `mem_naturalLoop_of_path` asks for `x < g.size` and
`path_of_mem_naturalLoop` asks for nothing. -/

/-- A path of the reversed graph, read backwards, is a path of the graph. -/
theorem path_of_reverse {root : Nat} {ls : List Nat}
    (h : (g.reverse root).Path a b ls) : g.Path b a ls.reverse := by
  refine ⟨by rw [List.head?_reverse]; exact h.2.1, by rw [List.getLast?_reverse]; exact h.1, ?_⟩
  exact List.isChain_reverse.mpr
    (isChain_of_mem h.2.2 fun _ _ _ _ huv => ((edge_reverse g root).mp huv).1)

/-- A path of the graph, read backwards, is a path of the reversed graph, as
long as its first node is a node of the graph. -/
theorem reverse_path {root : Nat} {ls : List Nat} (h : g.Path a b ls) (ha : a < g.size) :
    (g.reverse root).Path b a ls.reverse := by
  have hall := mem_lt_size_of_path h ha
  refine ⟨by rw [List.head?_reverse]; exact h.2.1, by rw [List.getLast?_reverse]; exact h.1, ?_⟩
  exact List.isChain_reverse.mpr
    (isChain_of_mem h.2.2 fun u hu v hv huv =>
      (edge_reverse g root).mpr ⟨huv, hall u hu, hall v hv⟩)

/-- A node of a natural loop other than its header reaches the back edge's tail
along a path that avoids the header. -/
theorem path_of_mem_naturalLoop (h : g.InNaturalLoop src dst x) (hne : x ≠ dst) :
    ∃ ls, g.Path x src ls ∧ ∀ y ∈ ls, y ≠ dst := by
  have hx : x ∈ (g.reverse src).closure fun y => y != dst := by
    simpa [InNaturalLoop, naturalLoop, hne] using h
  obtain ⟨ls, hp, hk⟩ := walk_iff_path.mp (mem_closure_iff.mp hx)
  refine ⟨ls.reverse, path_of_reverse hp, fun y hy => ?_⟩
  simpa using hk y (List.mem_reverse.mp hy)

/-- A node of the graph reaching the back edge's tail along a path avoiding the
header is in the natural loop. -/
theorem mem_naturalLoop_of_path {ls : List Nat} (hp : g.Path x src ls)
    (havoid : ∀ y ∈ ls, y ≠ dst) (hx : x < g.size) : g.InNaturalLoop src dst x := by
  have hrev : (g.reverse src).Path src x ls.reverse := reverse_path hp hx
  have hw : (g.reverse src).Walk (fun y => y != dst) x :=
    walk_iff_path.mpr ⟨ls.reverse, hrev, fun y hy => by
      simpa using havoid y (List.mem_reverse.mp hy)⟩
  simp only [InNaturalLoop, naturalLoop, List.mem_cons]
  exact .inr (mem_closure_iff.mpr hw)

/-- **Membership in a natural loop, as a path statement.** -/
theorem mem_naturalLoop_iff (hx : x < g.size) :
    g.InNaturalLoop src dst x ↔
      (x = dst ∨ ∃ ls, g.Path x src ls ∧ ∀ y ∈ ls, y ≠ dst) := by
  constructor
  · intro h
    by_cases hne : x = dst
    · exact .inl hne
    · exact .inr (path_of_mem_naturalLoop h hne)
  · rintro (rfl | ⟨ls, hp, hav⟩)
    · exact inNaturalLoop_header _ _ _
    · exact mem_naturalLoop_of_path hp hav hx

/-- Every node of a path witnessing loop membership is itself in the loop. -/
theorem mem_naturalLoop_of_mem_path {ls : List Nat} (hp : g.Path x src ls)
    (havoid : ∀ y ∈ ls, y ≠ dst) (hx : x < g.size) (hy : y ∈ ls) :
    g.InNaturalLoop src dst y := by
  have hylt : y < g.size := mem_lt_size_of_path hp hx y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact mem_naturalLoop_of_path (hp.drop hi)
    (fun z hz => havoid z (List.drop_subset _ _ hz)) hylt

/-- Every node of a natural loop is a node of the graph, once the back edge's
two ends are. -/
theorem lt_size_of_mem_naturalLoop (h : g.InNaturalLoop src dst x) (hsrc : src < g.size)
    (hdst : dst < g.size) : x < g.size := by
  by_cases hne : x = dst
  · exact hne ▸ hdst
  · have hx : x ∈ (g.reverse src).closure fun y => y != dst := by
      simpa [InNaturalLoop, naturalLoop, hne] using h
    have hmem := mem_nodes_of_walk (mem_closure_iff.mp hx)
    simp only [mem_nodes_iff, reverse_size] at hmem
    rcases hmem with rfl | h'
    · exact hsrc
    · exact h'

/-! ## The header dominates its loop -/

/-- **The header of a natural loop dominates every node of it**, so a natural
loop is a single-entry region: control enters it only at the header. No
reducibility is needed; the back edge's own dominance condition is what does the
work. -/
theorem BackEdge.dominates_naturalLoop (h : g.BackEdge src dst)
    (hx : g.InNaturalLoop src dst x) : g.Dominates dst x := by
  by_cases hne : x = dst
  · exact hne ▸ Dominates.refl g dst
  obtain ⟨ls, hp, hav⟩ := path_of_mem_naturalLoop hx hne
  rw [dominates_iff_not_walk]
  intro hw
  obtain ⟨q, hq, hqk⟩ := walk_iff_path.mp hw
  refine (dominates_iff_not_walk.mp h.2) (walk_iff_path.mpr ⟨q ++ ls.tail, hq.append hp, ?_⟩)
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hqk y hy
  · simpa using hav y (List.mem_of_mem_tail hy)

/-! ## Pruned graphs

Dominance is vacuously true at an unreachable node, so a back edge whose target
is unreachable says nothing and two such "loops" need not nest. A recovered
control-flow graph with its dead code pruned has no such nodes, and that is the
hypothesis the nesting theorem takes. -/

/-- The entry is a node of the graph and every node is reachable from it. -/
structure Pruned (g : Digraph) : Prop where
  /-- The entry is a node of the graph. -/
  entry_lt : g.entry < g.size
  /-- Every node is reachable from the entry. -/
  reachable : ∀ n ∈ List.range g.size, g.Reachable n

instance : Decidable g.Pruned :=
  decidable_of_iff (g.entry < g.size ∧ ∀ n ∈ List.range g.size, g.Reachable n)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.entry_lt, h.reachable⟩⟩

/-- In a pruned graph every reachable node is a node of the graph. -/
theorem Pruned.lt_size (h : g.Pruned) (hb : g.Reachable b) : b < g.size := by
  have hmem := mem_nodes_of_reachable hb
  simp only [mem_nodes_iff] at hmem
  rcases hmem with rfl | h'
  · exact h.entry_lt
  · exact h'

/-! ## Proper nesting

The theorem the next rung rests on: the natural loops of back edges with
distinct headers form a forest under inclusion, so each is a region that can be
lifted to one nested `cfg`. Reducibility is *not* used; `Pruned` is, through the
reachability of the node at which the two loops meet.

The proof is the classical one. If the loops meet at `x` then both headers
dominate `x`, so by `Dominates.total` one dominates the other; say `d₁`
dominates `d₂`. Cutting a path from the entry to `x` at the **last** occurrence
of `d₂` gives a path `d₂ ⇝ x` on which `d₁` cannot appear — if it did, the
suffix from it would reach `x` without meeting `d₂` at all, and prefixing a path
to `d₁` that avoids `d₂` (one exists, because `d₂` does not dominate `d₁`) would
contradict `d₂`'s dominance of `x`. Appending the witness that `x` is in the
first loop then puts `d₂` in the first loop, and from there every node of the
second loop follows. -/

/-- The last index at which a node occurs on a list. `Graph/Dominance.lean` has
the same lemma as a private `exists_max_index`; the pair belongs in a shared
list utility the next time either file moves. -/
private theorem exists_last_index {ls : List Nat} {a : Nat} (hx : a ∈ ls) :
    ∃ i : Nat, ls[i]? = some a ∧ ∀ j : Nat, ls[j]? = some a → j ≤ i := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hx
  have hmlt : m < ls.length := (List.getElem?_eq_some_iff.mp hm).1
  refine ⟨Nat.findGreatest (fun i => ls[i]? = some a) ls.length, ?_, fun j hj => ?_⟩
  · exact Nat.findGreatest_spec (P := fun i => ls[i]? = some a) (le_of_lt hmlt) hm
  · exact Nat.le_findGreatest (P := fun i => ls[i]? = some a)
      (le_of_lt (List.getElem?_eq_some_iff.mp hj).1) hj

/-- **The outer header lies in the outer loop.** When two natural loops with
distinct headers meet and the first header dominates the second, the second
header is a node of the first loop. This is the step that needs the last
occurrence of `d₂` on a path to the meeting point. Nothing is assumed about
`s₁ → d₁` being a back edge: the witness that `x` is in the first loop is all
the first loop contributes. -/
theorem mem_naturalLoop_header_of_dominates {s₁ d₁ s₂ d₂ : Nat}
    (h₂ : g.BackEdge s₂ d₂) (hne : d₁ ≠ d₂)
    (hdom : g.Dominates d₁ d₂) (hx₁ : g.InNaturalLoop s₁ d₁ x)
    (hx₂ : g.InNaturalLoop s₂ d₂ x) (hxr : g.Reachable x) :
    g.InNaturalLoop s₁ d₁ d₂ := by
  have hd₂lt : d₂ < g.size := lt_size_of_edge h₂.1
  have hd₂x : g.Dominates d₂ x := h₂.dominates_naturalLoop hx₂
  have hd₂r : g.Reachable d₂ := Dominates.reachable hxr hd₂x
  by_cases hxd₂ : x = d₂
  · exact hxd₂ ▸ hx₁
  have hxd₁ : x ≠ d₁ := fun h => hne (Dominates.antisymm hd₂r hdom (h ▸ hd₂x))
  obtain ⟨B, hB, hBav⟩ := path_of_mem_naturalLoop hx₁ hxd₁
  have hnd : ¬ g.Dominates d₂ d₁ := fun hc => hne (Dominates.antisymm hd₂r hdom hc)
  obtain ⟨P, hP, hPav⟩ := walk_iff_path.mp
    (by by_contra hc; exact hnd (dominates_iff_not_walk.mpr hc))
  obtain ⟨Q, hQ⟩ := hxr
  obtain ⟨j, hj, hjmax⟩ := exists_last_index (hd₂x Q hQ)
  have hjlt : j < Q.length := (List.getElem?_eq_some_iff.mp hj).1
  have hQj : Q[j] = d₂ := (List.getElem?_eq_some_iff.mp hj).2
  have hR : g.Path d₂ x (Q.drop j) := hQj ▸ hQ.drop hjlt
  have hRav : ∀ z ∈ Q.drop j, z ≠ d₁ := by
    intro z hz hzd
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hz
    rw [List.getElem?_drop, hzd] at hk
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, Nat.add_zero, hj] at hk
      exact hne (Option.some.inj hk).symm
    have hklt : j + k < Q.length := (List.getElem?_eq_some_iff.mp hk).1
    have hQjk : Q[j + k] = d₁ := (List.getElem?_eq_some_iff.mp hk).2
    have hsuf : g.Path d₁ x (Q.drop (j + k)) := hQjk ▸ hQ.drop hklt
    have hsufav : ∀ w ∈ Q.drop (j + k), w ≠ d₂ := by
      intro w hw hwd
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hw
      rw [List.getElem?_drop, hwd] at hm
      have := hjmax _ hm
      omega
    refine (dominates_iff_not_walk.mp hd₂x) (walk_iff_path.mpr
      ⟨P ++ (Q.drop (j + k)).tail, hP.append hsuf, fun w hw => ?_⟩)
    rcases List.mem_append.mp hw with hw | hw
    · exact hPav w hw
    · simpa using hsufav w (List.mem_of_mem_tail hw)
  refine mem_naturalLoop_of_path (hR.append hB) (fun z hz => ?_) hd₂lt
  rcases List.mem_append.mp hz with hz | hz
  · exact hRav z hz
  · exact hBav z (List.mem_of_mem_tail hz)

/-- **Once the inner header lies in the outer loop, so does the whole inner
loop.** Stated separately from the step above because the loops of a header with
several back edges are unions, and this half is applied once per back edge while
the step above is applied once. -/
theorem naturalLoop_subset_of_mem_header {s₁ d₁ s₂ d₂ : Nat}
    (h₂ : g.BackEdge s₂ d₂) (hne : d₁ ≠ d₂)
    (hdom : g.Dominates d₁ d₂) (hd₂r : g.Reachable d₂) (hs₂ : s₂ < g.size)
    (hhdr : g.InNaturalLoop s₁ d₁ d₂) :
    ∀ y, g.InNaturalLoop s₂ d₂ y → g.InNaturalLoop s₁ d₁ y := by
  intro y hy
  have hd₂lt : d₂ < g.size := lt_size_of_edge h₂.1
  by_cases hyd₂ : y = d₂
  · exact hyd₂ ▸ hhdr
  obtain ⟨A, hA, hAav⟩ := path_of_mem_naturalLoop hy hyd₂
  have hylt : y < g.size := lt_size_of_mem_naturalLoop hy hs₂ hd₂lt
  have hAav₁ : ∀ z ∈ A, z ≠ d₁ := by
    intro z hz hzd
    have hz₂ : g.InNaturalLoop s₂ d₂ z := mem_naturalLoop_of_mem_path hA hAav hylt hz
    exact hne (Dominates.antisymm hd₂r hdom (hzd ▸ h₂.dominates_naturalLoop hz₂))
  obtain ⟨C, hC, hCav⟩ := path_of_mem_naturalLoop hhdr (fun h => hne h.symm)
  refine mem_naturalLoop_of_path ((hA.snoc h₂.1).append hC) (fun z hz => ?_) hylt
  rcases List.mem_append.mp hz with hz | hz
  · rcases List.mem_append.mp hz with hz | hz
    · exact hAav₁ z hz
    · exact (List.mem_singleton.mp hz) ▸ (fun h => hne h.symm)
  · exact hCav z (List.mem_of_mem_tail hz)

/-- One half of nesting, with the dominance between the headers given: when the
header of the first loop dominates the header of the second and the two loops
meet, the second is contained in the first. -/
theorem naturalLoop_subset_of_dominates {s₁ d₁ s₂ d₂ : Nat}
    (h₂ : g.BackEdge s₂ d₂) (hs₂ : s₂ < g.size) (hne : d₁ ≠ d₂)
    (hdom : g.Dominates d₁ d₂) (hx₁ : g.InNaturalLoop s₁ d₁ x)
    (hx₂ : g.InNaturalLoop s₂ d₂ x) (hxr : g.Reachable x) :
    ∀ y, g.InNaturalLoop s₂ d₂ y → g.InNaturalLoop s₁ d₁ y :=
  naturalLoop_subset_of_mem_header h₂ hne hdom
    (Dominates.reachable hxr (h₂.dominates_naturalLoop hx₂)) hs₂
    (mem_naturalLoop_header_of_dominates h₂ hne hdom hx₁ hx₂ hxr)

/-- **Natural loops with distinct headers are disjoint or nested.** This is the
fact that makes a loop forest, and so a nest of single-entry regions, possible:
no two loops partially overlap. It needs the graph to be pruned, because
dominance is vacuous at an unreachable node; it does **not** need the graph to
be reducible. -/
theorem naturalLoop_nested {s₁ d₁ s₂ d₂ : Nat} (hp : g.Pruned)
    (h₁ : g.BackEdge s₁ d₁) (h₂ : g.BackEdge s₂ d₂) (hs₁ : s₁ < g.size)
    (hs₂ : s₂ < g.size) (hne : d₁ ≠ d₂) :
    (∀ x, ¬ (g.InNaturalLoop s₁ d₁ x ∧ g.InNaturalLoop s₂ d₂ x)) ∨
    (∀ y, g.InNaturalLoop s₂ d₂ y → g.InNaturalLoop s₁ d₁ y) ∨
    (∀ y, g.InNaturalLoop s₁ d₁ y → g.InNaturalLoop s₂ d₂ y) := by
  by_cases hmeet : ∀ z, ¬ (g.InNaturalLoop s₁ d₁ z ∧ g.InNaturalLoop s₂ d₂ z)
  · exact .inl hmeet
  push Not at hmeet
  obtain ⟨z, hz₁, hz₂⟩ := hmeet
  have hd₁lt : d₁ < g.size := lt_size_of_edge h₁.1
  have hzlt : z < g.size := lt_size_of_mem_naturalLoop hz₁ hs₁ hd₁lt
  have hzr : g.Reachable z := hp.reachable z (List.mem_range.mpr hzlt)
  rcases Dominates.total hzr (h₁.dominates_naturalLoop hz₁)
      (h₂.dominates_naturalLoop hz₂) with hdom | hdom
  · exact .inr (.inl (naturalLoop_subset_of_dominates h₂ hs₂ hne hdom hz₁ hz₂ hzr))
  · exact .inr (.inr (naturalLoop_subset_of_dominates h₁ hs₁ (Ne.symm hne) hdom hz₂ hz₁ hzr))

/-! ## Loops of a header

Several back edges may share a header; their natural loops need not be
comparable, and the loop of the header is their union. -/

/-- The union of the natural loops of the back edges `t → dst` for `t` in
`tails`. -/
def naturalLoops (g : Digraph) (dst : Nat) (tails : List Nat) : List Nat :=
  tails.flatMap fun t => g.naturalLoop t dst

/-- Membership in the union of the natural loops of a header. -/
def InNaturalLoops (g : Digraph) (dst : Nat) (tails : List Nat) (x : Nat) : Prop :=
  x ∈ g.naturalLoops dst tails

instance {tails : List Nat} : Decidable (g.InNaturalLoops dst tails x) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The tails of every back edge whose target is `dst`. -/
def backEdgeTails (g : Digraph) (dst : Nat) : List Nat :=
  (List.range g.size).filter fun t => decide (g.BackEdge t dst)

/-- `backEdgeTails` lists exactly the in-range tails of the back edges into a
header, which is where the nesting theorems get their range hypotheses. -/
theorem mem_backEdgeTails_iff : x ∈ g.backEdgeTails dst ↔ (x < g.size ∧ g.BackEdge x dst) := by
  simp [backEdgeTails, List.mem_filter, List.mem_range]

/-- **The header dominates every node of the union of its natural loops**, so
the loop of a header is a single-entry region however many back edges close
it. -/
theorem dominates_naturalLoops {tails : List Nat} (hbe : ∀ t ∈ tails, g.BackEdge t dst)
    (hx : g.InNaturalLoops dst tails x) : g.Dominates dst x := by
  simp only [InNaturalLoops, naturalLoops, List.mem_flatMap] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact (hbe t ht).dominates_naturalLoop hxt

/-- **The loops of distinct headers are disjoint or nested**, for the unions
too. -/
theorem naturalLoops_nested {t₁ t₂ : List Nat} {d₁ d₂ : Nat} (hp : g.Pruned)
    (hb₁ : ∀ t ∈ t₁, g.BackEdge t d₁) (hb₂ : ∀ t ∈ t₂, g.BackEdge t d₂)
    (hl₁ : ∀ t ∈ t₁, t < g.size) (hl₂ : ∀ t ∈ t₂, t < g.size) (hne : d₁ ≠ d₂) :
    (∀ x, ¬ (g.InNaturalLoops d₁ t₁ x ∧ g.InNaturalLoops d₂ t₂ x)) ∨
    (∀ y, g.InNaturalLoops d₂ t₂ y → g.InNaturalLoops d₁ t₁ y) ∨
    (∀ y, g.InNaturalLoops d₁ t₁ y → g.InNaturalLoops d₂ t₂ y) := by
  by_cases hmeet : ∀ z, ¬ (g.InNaturalLoops d₁ t₁ z ∧ g.InNaturalLoops d₂ t₂ z)
  · exact .inl hmeet
  push Not at hmeet
  obtain ⟨z, hz₁, hz₂⟩ := hmeet
  simp only [InNaturalLoops, naturalLoops, List.mem_flatMap] at hz₁ hz₂
  obtain ⟨u₁, hu₁, hzu₁⟩ := hz₁
  obtain ⟨u₂, hu₂, hzu₂⟩ := hz₂
  have hd₁lt : d₁ < g.size := lt_size_of_edge (hb₁ u₁ hu₁).1
  have hzlt : z < g.size := lt_size_of_mem_naturalLoop hzu₁ (hl₁ u₁ hu₁) hd₁lt
  have hzr : g.Reachable z := hp.reachable z (List.mem_range.mpr hzlt)
  have hdx₁ := (hb₁ u₁ hu₁).dominates_naturalLoop hzu₁
  have hdx₂ := (hb₂ u₂ hu₂).dominates_naturalLoop hzu₂
  rcases Dominates.total hzr hdx₁ hdx₂ with hdom | hdom
  · refine .inr (.inl fun y hy => ?_)
    have hhdr := mem_naturalLoop_header_of_dominates (hb₂ u₂ hu₂) hne hdom hzu₁ hzu₂ hzr
    simp only [InNaturalLoops, naturalLoops, List.mem_flatMap] at hy ⊢
    obtain ⟨t, ht, hyt⟩ := hy
    exact ⟨u₁, hu₁, naturalLoop_subset_of_mem_header (hb₂ t ht) hne hdom
      (Dominates.reachable hzr hdx₂) (hl₂ t ht) hhdr y hyt⟩
  · refine .inr (.inr fun y hy => ?_)
    have hhdr := mem_naturalLoop_header_of_dominates (hb₁ u₁ hu₁) (Ne.symm hne) hdom
      hzu₂ hzu₁ hzr
    simp only [InNaturalLoops, naturalLoops, List.mem_flatMap] at hy ⊢
    obtain ⟨t, ht, hyt⟩ := hy
    exact ⟨u₂, hu₂, naturalLoop_subset_of_mem_header (hb₁ t ht) (Ne.symm hne)
      hdom (Dominates.reachable hzr hdx₁) (hl₁ t ht) hhdr y hyt⟩

end Digraph

end Silmaril.Machine.Graph
