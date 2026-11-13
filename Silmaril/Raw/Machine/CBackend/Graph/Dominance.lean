module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation
public import Mathlib.Data.Nat.Find

/-!
# Finite rooted digraphs, reachability and dominance

A `Digraph` is the control-flow skeleton shared by every pass that needs graph
theory rather than a particular syntax: the nodes `0 … size - 1`, a successor
function and an entry node. `RTL.SSA` builds one from a function's blocks; CFG
recovery from machine code and loop recovery for region-structured IRs are
expected to build one too, so the definitions and proofs live here once.

A successor outside `0 … size - 1` is **not** an edge: `Digraph.step` filters
the successor list against the node range, and `Digraph.Edge` is membership in
the filtered list. This keeps every definition below total and every predicate
decidable without a well-formedness hypothesis. A client whose successors are
already in range (as `RTL.SSA.Func.WellFormedSig` guarantees) sees `step = succ`.
The entry is not required to be in range; it is simply a node with no incoming
edges and, when out of range, no outgoing ones.

`Path`, `Reachable` and `Dominates` are the mathematical definitions: a path is
a list of nodes joined by edges, `a` dominates `b` when every path from the
entry to `b` contains `a`. `doms` and `domsets` compute dominator sets by an
iterative fixpoint, and `mem_doms_iff` proves the two agree on reachable nodes.
That agreement is one of the two real theorems here; the other is
`Dominates.total`, that the strict dominators of a reachable node are totally
ordered by dominance. The remaining facts (reflexivity, transitivity, the entry
dominating everything, antisymmetry on reachable nodes and the step lemma
`Dominates.of_edge`) are proved from the path definition.

## The dominator tree

`Dominates.total` is what makes the dominator tree a tree: the strict dominators
of a reachable node form a chain, so they have a greatest element, the immediate
dominator. `idom` computes it and `idom_spec` characterises it; `idom` is `none`
at the entry and at unreachable nodes. `domTreeChildren a` lists the nodes whose
immediate dominator is `a`, and `mem_domTreeChildren_iff` ties the two together.
A later pass recovering nested regions from a CFG nests exactly the blocks
immediately dominated by a region's entry, which is why these live here rather
than in the pass.

Antisymmetry and totality are both proved by comparing *positions along one
path*: antisymmetry compares first occurrences, totality compares last
occurrences of two incomparable dominators and derives that each must occur
after the other.

`DomAncestor` is the reflexive-transitive closure of `idom`, and
`domAncestor_iff_dominates` is the third real theorem here: on reachable nodes,
dominating and being an ancestor in the dominator tree are the same relation, so
a dominance-based invariant may be established by recursion over
`domTreeChildren`. It is proved by induction on `domDepth`, the number of strict
dominators of a node, which `domDepth_lt_of_idom` shows strictly increases down
the tree and `domDepth_le` bounds by `size`. Both are counting arguments, so
they rest on `nodes_nodup`: `nodes` lists the entry once, and `doms` and
`strictDoms` are filters of it.

## The fixpoint

`closure keep` is the set of nodes reachable from the entry through nodes
admitted by `keep`, computed by `size + 1` rounds of successor closure from the
entry. The bound is honest: each round either adds a node or has reached the
fixpoint, every round stays inside `nodes`, which lists the entry and
`0 … size - 1` without duplicates and so has at most `size + 1` entries, and a
strictly increasing chain of duplicate-free sublists of such a list stabilises
within `size + 1` steps. Dominance is read off it: `a` dominates `b`
exactly when no path from the entry to `b` avoids `a`, that is, when `b` is not
in `closure (· ≠ a)`.

Not provided: the Lengauer-Tarjan algorithm or any other asymptotically good
dominator computation — `closure` is run once per candidate dominator, so
`doms` is quadratic; dominance frontiers; or any loop theorems —
`Graph/Loops.lean` states the loop definitions, and their theory is left to the
pass that needs it.
-/

@[expose] public section

namespace Silmaril.Machine.Graph

/-- A finite rooted digraph: the nodes `0 … size - 1`, a successor function and
an entry node. Successors outside the node range are ignored. -/
structure Digraph where
  size : Nat
  succ : Nat → List Nat
  entry : Nat

namespace Digraph

variable {g : Digraph} {a b x y : Nat} {keep : Nat → Bool}

/-- The successors of `a` that are nodes of the graph. -/
def step (g : Digraph) (a : Nat) : List Nat := (g.succ a).filter fun b => decide (b < g.size)

/-- An edge of the graph. -/
def Edge (g : Digraph) (a b : Nat) : Prop := b ∈ g.step a

instance : Decidable (g.Edge a b) := inferInstanceAs (Decidable (_ ∈ _))

theorem lt_size_of_edge (h : g.Edge a b) : b < g.size := by
  have h' : b ∈ g.succ a ∧ b < g.size := by simpa [Edge, step, List.mem_filter] using h
  exact h'.2

/-- `g.Path a b ls`: `ls` lists the nodes of a walk from `a` to `b`, in order. -/
def Path (g : Digraph) (a b : Nat) (ls : List Nat) : Prop :=
  ls.head? = some a ∧ ls.getLast? = some b ∧ List.IsChain g.Edge ls

/-- A node is reachable when some path leads to it from the entry. -/
def Reachable (g : Digraph) (b : Nat) : Prop := ∃ ls, g.Path g.entry b ls

/-- `a` dominates `b` when every path from the entry to `b` passes through `a`.
An unreachable node is dominated by every node. -/
def Dominates (g : Digraph) (a b : Nat) : Prop := ∀ ls, g.Path g.entry b ls → a ∈ ls

/-! ## Paths

The utilities every proof below runs on: a path is nonempty and contains its
endpoints, it can be extended by an edge, and it can be cut at any index into a
prefix and a suffix which are themselves paths. -/

/-- The one-node path. -/
theorem path_singleton (g : Digraph) (a : Nat) : g.Path a a [a] := ⟨rfl, rfl, .singleton a⟩

theorem Path.ne_nil {ls : List Nat} (h : g.Path a b ls) : ls ≠ [] := by
  rintro rfl
  exact absurd h.1 (by simp)

/-- The first node of a path is on it. -/
theorem Path.mem_left {ls : List Nat} (h : g.Path a b ls) : a ∈ ls := by
  cases ls with
  | nil => exact absurd rfl h.ne_nil
  | cons c t =>
    have : c = a := by simpa using h.1
    simp [this]

/-- The last node of a path is on it. -/
theorem Path.mem_right {ls : List Nat} (h : g.Path a b ls) : b ∈ ls :=
  List.mem_of_getLast? h.2.1

/-- A path extended by an edge is a path. -/
theorem Path.snoc {ls : List Nat} {c : Nat} (h : g.Path a b ls) (he : g.Edge b c) :
    g.Path a c (ls ++ [c]) := by
  refine ⟨?_, by simp, h.2.2.append (.singleton c) ?_⟩
  · rw [List.head?_append, h.1]; rfl
  · intro p hp q hq
    rw [h.2.1] at hp
    rw [Option.mem_def] at hp hq
    simp only [Option.some.injEq, List.head?_cons] at hp hq
    exact hp ▸ hq ▸ he

/-- The prefix of a path up to its `i`-th node. -/
theorem Path.take {ls : List Nat} (h : g.Path a b ls) {i : Nat} (hi : i < ls.length) :
    g.Path a ls[i] (ls.take (i + 1)) := by
  have hlen : (ls.take (i + 1)).length = i + 1 := by
    rw [List.length_take]; omega
  refine ⟨?_, ?_, h.2.2.take _⟩
  · cases ls with
    | nil => simp at hi
    | cons c t => simpa using h.1
  · rw [List.getLast?_eq_getElem?, hlen]
    simp

/-- The suffix of a path from its `i`-th node. -/
theorem Path.drop {ls : List Nat} (h : g.Path a b ls) {i : Nat} (hi : i < ls.length) :
    g.Path ls[i] b (ls.drop i) := by
  refine ⟨?_, ?_, h.2.2.drop _⟩
  · rw [List.head?_eq_getElem?, List.getElem?_drop]
    simp
  · rw [List.getLast?_eq_getElem?, List.length_drop, List.getElem?_drop,
      show i + (ls.length - i - 1) = ls.length - 1 by omega, ← List.getLast?_eq_getElem?]
    exact h.2.1

/-- Concatenating a path to `b` with a path from `b`. -/
theorem Path.append {p q : List Nat} {c : Nat} (h₁ : g.Path a b p) (h₂ : g.Path b c q) :
    g.Path a c (p ++ q.tail) := by
  cases q with
  | nil => exact absurd rfl h₂.ne_nil
  | cons d t =>
    have hd : d = b := by simpa using h₂.1
    subst hd
    refine ⟨?_, ?_, h₁.2.2.append h₂.2.2.tail ?_⟩
    · rw [List.head?_append, h₁.1]; rfl
    · cases t with
      | nil =>
        have : d = c := by simpa using h₂.2.1
        simpa [this] using h₁.2.1
      | cons e u =>
        rw [List.tail_cons, List.getLast?_append]
        simpa using h₂.2.1
    · intro x hx y hy
      rw [h₁.2.1, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ h₂.2.2.rel_head? hy

/-! ## Walks through a set of nodes -/

/-- `g.Walk keep b`: some path from the entry to `b` visits only nodes admitted
by `keep`. -/
inductive Walk (g : Digraph) (keep : Nat → Bool) : Nat → Prop
  | entry : keep g.entry = true → Walk g keep g.entry
  | step {x y : Nat} : Walk g keep x → g.Edge x y → keep y = true → Walk g keep y

/-- The nodes a walk or a round may visit: the entry and the graph's own nodes.
The entry is prepended only when it is out of range, so the list is
duplicate-free and can therefore be counted against. -/
def nodes (g : Digraph) : List Nat :=
  if g.entry < g.size then List.range g.size else g.entry :: List.range g.size

/-- The nodes are the entry and the nodes in range. -/
@[simp] theorem mem_nodes_iff : b ∈ g.nodes ↔ b = g.entry ∨ b < g.size := by
  unfold nodes
  split
  · rename_i h
    simp only [List.mem_range]
    omega
  · simp

/-- `nodes` is duplicate-free: the entry is listed once, whether or not it is in
range. This is what lets the lists filtered out of it be counted. -/
theorem nodes_nodup (g : Digraph) : g.nodes.Nodup := by
  unfold nodes
  split <;> rename_i h
  · exact List.nodup_range
  · exact List.nodup_cons.mpr ⟨by simp; omega, List.nodup_range⟩

/-- `nodes` has at most `size + 1` entries, the bound the fixpoint runs on. -/
theorem length_nodes_le (g : Digraph) : g.nodes.length ≤ g.size + 1 := by
  unfold nodes
  split <;> simp

private theorem walk_of_path_aux :
    ∀ {ls : List Nat} {a b : Nat}, g.Path a b ls → (∀ x ∈ ls, keep x = true) →
      g.Walk keep a → g.Walk keep b
  | [], _, _, h, _, _ => absurd rfl h.ne_nil
  | [c], a, b, h, _, hw => by
    have hca : c = a := by simpa using h.1
    have hcb : c = b := by simpa using h.2.1
    subst hca; subst hcb; exact hw
  | c :: d :: t, a, b, h, hk, hw => by
    have hca : c = a := by simpa using h.1
    have hcd : g.Edge c d := h.2.2.rel
    have hd : g.Walk keep d := .step (hca ▸ hw) hcd (hk d (by simp))
    exact walk_of_path_aux (ls := d :: t) ⟨rfl, by simpa using h.2.1, h.2.2.tail⟩
      (fun x hx => hk x (by simp [hx])) hd

/-- A path through admitted nodes gives a walk. -/
private theorem walk_of_path {ls : List Nat} (h : g.Path g.entry b ls)
    (hk : ∀ x ∈ ls, keep x = true) : g.Walk keep b :=
  walk_of_path_aux h hk (.entry (hk g.entry h.mem_left))

/-- A walk gives a path through admitted nodes. -/
private theorem path_of_walk (h : g.Walk keep b) :
    ∃ ls, g.Path g.entry b ls ∧ ∀ x ∈ ls, keep x = true := by
  induction h with
  | entry hk => exact ⟨[g.entry], path_singleton g g.entry, by simp [hk]⟩
  | step _ he hk ih =>
    obtain ⟨ls, hp, hall⟩ := ih
    refine ⟨ls ++ [_], hp.snoc he, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x hx
    · rw [List.mem_singleton.mp hx]; exact hk

/-- A walk through admitted nodes is a path all of whose nodes are admitted. -/
theorem walk_iff_path : g.Walk keep b ↔ ∃ ls, g.Path g.entry b ls ∧ ∀ x ∈ ls, keep x = true :=
  ⟨path_of_walk, fun ⟨_, hp, hk⟩ => walk_of_path hp hk⟩

theorem mem_nodes_of_walk (h : g.Walk keep b) : b ∈ g.nodes := by
  cases h with
  | entry _ => exact mem_nodes_iff.mpr (Or.inl rfl)
  | step _ he _ => exact mem_nodes_iff.mpr (Or.inr (lt_size_of_edge he))

theorem mem_nodes_of_path {ls : List Nat} (h : g.Path g.entry b ls) :
    ∀ x ∈ ls, x ∈ g.nodes := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact mem_nodes_of_walk (keep := fun _ => true) (walk_of_path (h.take hi) (by simp))

/-! ## The fixpoint -/

/-- One round of successor closure, keeping only admitted nodes. -/
def round (g : Digraph) (keep : Nat → Bool) (s : List Nat) : List Nat :=
  (s ++ (s.flatMap g.step).filter keep).dedup

/-- `n` rounds of closure from the entry. -/
def closureAux (g : Digraph) (keep : Nat → Bool) : Nat → List Nat
  | 0 => if keep g.entry then [g.entry] else []
  | n + 1 => g.round keep (g.closureAux keep n)

/-- The nodes reachable from the entry through admitted nodes. `size + 1`
rounds suffice: the chain of rounds is increasing inside a set of
`size + 1` nodes. -/
def closure (g : Digraph) (keep : Nat → Bool) : List Nat := g.closureAux keep (g.size + 1)

private theorem mem_round {s : List Nat} :
    b ∈ g.round keep s ↔ b ∈ s ∨ ((∃ x ∈ s, g.Edge x b) ∧ keep b = true) := by
  simp [round, List.mem_dedup, List.mem_filter, List.mem_flatMap, Edge, and_comm]

private theorem closureAux_subset_succ (g : Digraph) (keep : Nat → Bool) (n : Nat) :
    g.closureAux keep n ⊆ g.closureAux keep (n + 1) :=
  fun _ hx => mem_round.mpr (Or.inl hx)

private theorem round_mono {s t : List Nat} (h : s ⊆ t) :
    g.round keep s ⊆ g.round keep t := by
  intro x hx
  rcases mem_round.mp hx with hx | ⟨⟨y, hy, he⟩, hkb⟩
  · exact mem_round.mpr (Or.inl (h hx))
  · exact mem_round.mpr (Or.inr ⟨⟨y, h hy, he⟩, hkb⟩)

private theorem closureAux_mono {m n : Nat} (h : m ≤ n) :
    g.closureAux keep m ⊆ g.closureAux keep n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact fun x hx => closureAux_subset_succ g keep n (ih (Nat.lt_succ_iff.mp h') hx)
    · exact fun _ hx => hx

private theorem closureAux_nodup (n : Nat) : (g.closureAux keep n).Nodup := by
  cases n with
  | zero => unfold closureAux; split <;> simp
  | succ n => exact List.nodup_dedup _

private theorem closureAux_subset_nodes (n : Nat) : g.closureAux keep n ⊆ g.nodes := by
  induction n with
  | zero =>
    intro x hx
    unfold closureAux at hx
    split at hx
    · rw [List.mem_singleton.mp hx]; exact mem_nodes_iff.mpr (Or.inl rfl)
    · simp at hx
  | succ n ih =>
    intro x hx
    rcases mem_round.mp hx with hx | ⟨⟨_, _, he⟩, _⟩
    · exact ih hx
    · exact mem_nodes_iff.mpr (Or.inr (lt_size_of_edge he))

private theorem closureAux_sound {n : Nat} (h : b ∈ g.closureAux keep n) : g.Walk keep b := by
  induction n generalizing b with
  | zero =>
    unfold closureAux at h
    split at h
    · rename_i hk
      rw [List.mem_singleton.mp h]
      exact .entry hk
    · simp at h
  | succ n ih =>
    rcases mem_round.mp h with h | ⟨⟨_, hy, he⟩, hkb⟩
    · exact ih h
    · exact .step (ih hy) he hkb

private theorem exists_mem_closureAux (h : g.Walk keep b) :
    ∃ n, b ∈ g.closureAux keep n := by
  induction h with
  | entry hk => exact ⟨0, by simp [closureAux, hk]⟩
  | step _ he hkb ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, mem_round.mpr (Or.inr ⟨⟨_, hn, he⟩, hkb⟩)⟩

/-- Once a round adds nothing, no later round adds anything. -/
private theorem closureAux_stable {n : Nat}
    (h : g.closureAux keep (n + 1) ⊆ g.closureAux keep n) :
    ∀ m, g.closureAux keep (n + m) ⊆ g.closureAux keep n := by
  intro m
  induction m with
  | zero => exact fun _ hx => hx
  | succ m ih =>
    have : g.closureAux keep (n + m + 1) ⊆ g.closureAux keep (n + 1) := round_mono ih
    exact fun x hx => h (this hx)

/-- **`size + 1` rounds reach the fixpoint.** A round either adds a node or is
stationary, every round stays inside the `size + 1` nodes of `nodes`, and the
rounds are duplicate-free, so a strictly increasing chain cannot outrun the
bound. -/
private theorem closureAux_subset_closure (n : Nat) :
    g.closureAux keep n ⊆ g.closure keep := by
  by_cases hk : keep g.entry = true
  · have hex : ∃ k, k ≤ g.size + 1 ∧ g.closureAux keep (k + 1) ⊆ g.closureAux keep k := by
      by_contra hno
      have hgrow : ∀ k, k ≤ g.size + 1 →
          ∃ y ∈ g.closureAux keep (k + 1), y ∉ g.closureAux keep k := by
        intro k hk0
        by_contra hc
        push Not at hc
        exact hno ⟨k, hk0, fun y hy => hc y hy⟩
      have hlen : ∀ k, k ≤ g.size + 1 → k + 1 ≤ (g.closureAux keep k).length := by
        intro k
        induction k with
        | zero => intro _; simp [closureAux, hk]
        | succ k ih =>
          intro hk1
          have hk0 : k ≤ g.size + 1 := by omega
          obtain ⟨y, hy, hy'⟩ := hgrow k hk0
          have hnd : (y :: g.closureAux keep k).Nodup :=
            List.nodup_cons.mpr ⟨hy', closureAux_nodup k⟩
          have hsub : (y :: g.closureAux keep k) ⊆ g.closureAux keep (k + 1) := by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact closureAux_subset_succ g keep k hz
          have hle := List.Nodup.length_le_of_subset hnd hsub
          have := ih hk0
          simp only [List.length_cons] at hle
          omega
      have h1 := hlen (g.size + 1) le_rfl
      have h2 := List.Nodup.length_le_of_subset (closureAux_nodup (g := g) (keep := keep)
        (g.size + 1)) (closureAux_subset_nodes (g.size + 1))
      have h3 := g.length_nodes_le
      omega
    obtain ⟨k, hk1, hk2⟩ := hex
    intro x hx
    rcases Nat.le_total n k with h | h
    · exact closureAux_mono (le_trans h hk1) hx
    · have hstab := closureAux_stable hk2 (n - k)
      rw [show k + (n - k) = n by omega] at hstab
      exact closureAux_mono hk1 (hstab hx)
  · have hempty : ∀ m, g.closureAux keep m = [] := by
      intro m
      induction m with
      | zero => simp [closureAux, hk]
      | succ m ih => simp [closureAux, round, ih]
    rw [hempty n]
    exact fun _ hx => absurd hx (by simp)

/-- **The fixpoint computes the admitted walks.** -/
theorem mem_closure_iff : b ∈ g.closure keep ↔ g.Walk keep b :=
  ⟨closureAux_sound, fun h => (exists_mem_closureAux h).elim fun _ hn =>
    closureAux_subset_closure _ hn⟩

instance : Decidable (g.Walk keep b) := decidable_of_iff _ mem_closure_iff

/-! ## Reachability -/

theorem reachable_iff_walk : g.Reachable b ↔ g.Walk (fun _ => true) b :=
  ⟨fun ⟨ls, hp⟩ => walk_iff_path.mpr ⟨ls, hp, by simp⟩,
   fun h => (walk_iff_path.mp h).elim fun ls hls => ⟨ls, hls.1⟩⟩

instance : Decidable (g.Reachable b) := decidable_of_iff _ reachable_iff_walk.symm

theorem reachable_entry (g : Digraph) : g.Reachable g.entry := ⟨[g.entry], path_singleton g g.entry⟩

theorem Reachable.step (h : g.Reachable x) (he : g.Edge x y) : g.Reachable y :=
  h.elim fun ls hls => ⟨ls ++ [y], hls.snoc he⟩

theorem mem_nodes_of_reachable (h : g.Reachable b) : b ∈ g.nodes :=
  mem_nodes_of_walk (keep := fun _ => true) (reachable_iff_walk.mp h)

/-! ## Dominance -/

/-- `a` dominates `b` exactly when no path from the entry to `b` avoids `a`. -/
theorem dominates_iff_not_walk : g.Dominates a b ↔ ¬ g.Walk (fun x => x != a) b := by
  constructor
  · intro hd hw
    obtain ⟨ls, hp, hk⟩ := walk_iff_path.mp hw
    have := hk a (hd ls hp)
    simp at this
  · intro hw ls hp
    by_contra hmem
    refine hw (walk_iff_path.mpr ⟨ls, hp, fun x hx => ?_⟩)
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact hmem hx

instance : Decidable (g.Dominates a b) := decidable_of_iff _ dominates_iff_not_walk.symm

/-- The dominators of `b`, by the fixpoint. -/
def doms (g : Digraph) (b : Nat) : List Nat :=
  g.nodes.filter fun a => decide (b ∉ g.closure fun x => x != a)

/-- The dominator set of every node of the graph, indexed by node. -/
def domsets (g : Digraph) : Array (List Nat) := (Array.range g.size).map g.doms

/-- **The computed dominator sets agree with the path definition** on reachable
nodes. An unreachable node is dominated by every node, including nodes outside
the graph, so it has no finite dominator set. -/
theorem mem_doms_iff (hb : g.Reachable b) : a ∈ g.doms b ↔ g.Dominates a b := by
  rw [doms, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    rw [dominates_iff_not_walk, ← mem_closure_iff]
    simpa using h
  · intro hd
    obtain ⟨ls, hp⟩ := hb
    refine ⟨mem_nodes_of_path hp a (hd ls hp), ?_⟩
    simp only [decide_eq_true_eq, mem_closure_iff]
    exact dominates_iff_not_walk.mp hd

theorem getElem!_domsets (g : Digraph) (hs : b < g.size) : g.domsets[b]! = g.doms b := by
  have hlt : b < g.domsets.size := by simp [domsets, hs]
  rw [getElem!_pos g.domsets b hlt]
  simp [domsets]

theorem mem_domsets_iff (hb : g.Reachable b) (hs : b < g.size) :
    a ∈ g.domsets[b]! ↔ g.Dominates a b := by
  rw [getElem!_domsets g hs]
  exact mem_doms_iff hb

/-- Every path from the entry to a node on it can be cut at that node. -/
private theorem path_prefix {ls : List Nat} (h : g.Path g.entry b ls) (hx : x ∈ ls) :
    ∃ p, g.Path g.entry x p ∧ p ⊆ ls := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨ls.take (i + 1), h.take hi, List.take_subset _ _⟩

theorem Dominates.refl (g : Digraph) (b : Nat) : g.Dominates b b := fun _ hp => hp.mem_right

theorem Dominates.trans (hab : g.Dominates a b) (hbc : g.Dominates b x) : g.Dominates a x := by
  intro ls hp
  obtain ⟨p, hp', hsub⟩ := path_prefix hp (hbc ls hp)
  exact hsub (hab p hp')

/-- The entry dominates every node. -/
theorem Dominates.entry (g : Digraph) (b : Nat) : g.Dominates g.entry b := fun _ hp => hp.mem_left

/-- Nothing but the entry dominates the entry. -/
theorem Dominates.eq_entry (h : g.Dominates a g.entry) : a = g.entry :=
  List.mem_singleton.mp (h [g.entry] (path_singleton g g.entry))

/-- A dominator of a reachable node is reachable. -/
theorem Dominates.reachable (hb : g.Reachable b) (h : g.Dominates a b) : g.Reachable a := by
  obtain ⟨ls, hp⟩ := hb
  obtain ⟨p, hp', -⟩ := path_prefix hp (h ls hp)
  exact ⟨p, hp'⟩

/-- The first index at which a node occurs on a list. -/
private theorem exists_min_index {ls : List Nat} {a : Nat} (hx : a ∈ ls) :
    ∃ i : Nat, ls[i]? = some a ∧ ∀ j : Nat, ls[j]? = some a → i ≤ j := by
  have h : ∃ i, ls[i]? = some a := List.mem_iff_getElem?.mp hx
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hj => Nat.find_min' h hj⟩

/-- The last index at which a node occurs on a list. -/
private theorem exists_max_index {ls : List Nat} {a : Nat} (hx : a ∈ ls) :
    ∃ i : Nat, ls[i]? = some a ∧ ∀ j : Nat, ls[j]? = some a → j ≤ i := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hx
  have hmlt : m < ls.length := (List.getElem?_eq_some_iff.mp hm).1
  refine ⟨Nat.findGreatest (fun i => ls[i]? = some a) ls.length, ?_, fun j hj => ?_⟩
  · exact Nat.findGreatest_spec (P := fun i => ls[i]? = some a) (le_of_lt hmlt) hm
  · exact Nat.le_findGreatest (P := fun i => ls[i]? = some a)
      (le_of_lt (List.getElem?_eq_some_iff.mp hj).1) hj

/-- If `v` dominates `u` and `u` occurs on a path from the entry at index `iu`,
then `v` occurs on it at or before `iu`. -/
private theorem dominates_index_le {ls : List Nat} {c u v iu iv : Nat}
    (hp : g.Path g.entry c ls) (hd : g.Dominates v u) (hiu : ls[iu]? = some u)
    (hminv : ∀ j, ls[j]? = some v → iv ≤ j) : iv ≤ iu := by
  obtain ⟨hiult, hu⟩ := List.getElem?_eq_some_iff.mp hiu
  have hmem : v ∈ ls.take (iu + 1) := hd _ (hu ▸ hp.take hiult)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < iu + 1 := by
    have h := (List.getElem?_eq_some_iff.mp hj).1
    rw [List.length_take] at h
    omega
  have : ls[j]? = some v := by rw [← List.getElem?_take_of_lt hjlt]; exact hj
  have := hminv j this
  omega

theorem Dominates.antisymm (hb : g.Reachable b) (hab : g.Dominates a b) (hba : g.Dominates b a) :
    a = b := by
  obtain ⟨ls, hp⟩ := hb
  obtain ⟨ia, hia, hmina⟩ := exists_min_index (hab ls hp)
  obtain ⟨ib, hib, hminb⟩ := exists_min_index hp.mem_right
  have h1 : ib ≤ ia := dominates_index_le hp hba hia hminb
  have h2 : ia ≤ ib := dominates_index_le hp hab hib hmina
  rw [show ia = ib from le_antisymm h2 h1, hib] at hia
  exact (Option.some.inj hia).symm

/-- **The step lemma.** A dominator of the target of an edge, other than the
target itself, dominates the source. This is what makes a dominance-based
invariant inductive along edges. -/
theorem Dominates.of_edge (he : g.Edge x y) (hd : g.Dominates a y) (hne : a ≠ y) :
    g.Dominates a x := by
  intro ls hp
  rcases List.mem_append.mp (hd (ls ++ [y]) (hp.snoc he)) with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hne

/-- The core of the totality lemma: if `u` dominates `b`, `v` occurs on a path
to `b` at index `lv`, and some path to `v` avoids `u`, then `u` occurs on that
path strictly after `lv`. -/
private theorem last_index_lt {ls P : List Nat} {b u v lu lv : Nat}
    (hls : g.Path g.entry b ls) (hdu : g.Dominates u b) (hv : ls[lv]? = some v)
    (hlu : ∀ j, ls[j]? = some u → j ≤ lu) (hP : g.Path g.entry v P) (hPu : u ∉ P) : lv < lu := by
  obtain ⟨hlvlt, hvv⟩ := List.getElem?_eq_some_iff.mp hv
  have hsuf : g.Path v b (ls.drop lv) := hvv ▸ hls.drop hlvlt
  rcases List.mem_append.mp (hdu _ (hP.append hsuf)) with h | h
  · exact absurd h hPu
  · rw [List.tail_drop] at h
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
    rw [List.getElem?_drop] at hj
    have := hlu _ hj
    omega

/-- **The strict dominators of a reachable node are totally ordered by
dominance.** This is what makes the dominator tree a tree. -/
theorem Dominates.total (hb : g.Reachable b) (ha : g.Dominates a b) (hc : g.Dominates x b) :
    g.Dominates a x ∨ g.Dominates x a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnac, hnca⟩ := hcon
  rw [Dominates] at hnac hnca
  push Not at hnac hnca
  obtain ⟨P, hP, hPa⟩ := hnac
  obtain ⟨Q, hQ, hQc⟩ := hnca
  obtain ⟨ls, hls⟩ := hb
  obtain ⟨la, hla, hlamax⟩ := exists_max_index (ha ls hls)
  obtain ⟨lx, hlx, hlxmax⟩ := exists_max_index (hc ls hls)
  have h1 : lx < la := last_index_lt hls ha hlx hlamax hP hPa
  have h2 : la < lx := last_index_lt hls hc hla hlxmax hQ hQc
  omega

/-! ## The dominator tree -/

/-- Strict dominance. -/
def StrictlyDominates (g : Digraph) (a b : Nat) : Prop := g.Dominates a b ∧ a ≠ b

instance : Decidable (g.StrictlyDominates a b) := inferInstanceAs (Decidable (_ ∧ _))

/-- The strict dominators of `b`. -/
def strictDoms (g : Digraph) (b : Nat) : List Nat := (g.doms b).filter fun a => a != b

theorem mem_strictDoms_iff (hb : g.Reachable b) :
    a ∈ g.strictDoms b ↔ g.StrictlyDominates a b := by
  rw [strictDoms, List.mem_filter, mem_doms_iff hb, StrictlyDominates]
  simp

/-- The immediate dominator: the strict dominator that every other strict
dominator dominates. `none` at the entry and at unreachable nodes. -/
def idom (g : Digraph) (b : Nat) : Option Nat :=
  if g.Reachable b then
    (g.strictDoms b).find? fun a => (g.strictDoms b).all fun c => decide (g.Dominates c a)
  else none

/-- The children of `a` in the dominator tree. -/
def domTreeChildren (g : Digraph) (a : Nat) : List Nat :=
  g.nodes.filter fun b => g.idom b == some a

/-- A nonempty list on which dominance is total has a greatest element. -/
private theorem exists_greatest : ∀ {L : List Nat}, L ≠ [] →
    (∀ u ∈ L, ∀ v ∈ L, g.Dominates u v ∨ g.Dominates v u) →
    ∃ u ∈ L, ∀ c ∈ L, g.Dominates c u
  | [], h, _ => absurd rfl h
  | [u], _, _ => ⟨u, by simp, by
      intro c hc
      rw [List.mem_singleton.mp hc]
      exact Dominates.refl g u⟩
  | u :: v :: t, _, htot => by
    obtain ⟨w, hw, hwmax⟩ := exists_greatest (L := v :: t) (by simp)
      (fun p hp q hq => htot p (by simp [hp]) q (by simp [hq]))
    rcases htot u (by simp) w (by simp [hw]) with h | h
    · refine ⟨w, by simp [hw], fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h
      · exact hwmax c hc
    · refine ⟨u, by simp, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Dominates.refl g c
      · exact (hwmax c hc).trans h

/-- **The immediate dominator exists** at every reachable node other than the
entry, and is the greatest strict dominator. -/
theorem idom_spec (hb : g.Reachable b) (hne : b ≠ g.entry) :
    ∃ a, g.idom b = some a ∧ g.StrictlyDominates a b ∧
      ∀ c, g.StrictlyDominates c b → g.Dominates c a := by
  have hentry : g.entry ∈ g.strictDoms b :=
    (mem_strictDoms_iff hb).mpr ⟨Dominates.entry g b, fun h => hne h.symm⟩
  have hne' : g.strictDoms b ≠ [] := fun h => by rw [h] at hentry; simp at hentry
  obtain ⟨u, hu, humax⟩ := exists_greatest hne' fun p hp q hq =>
    Dominates.total hb ((mem_strictDoms_iff hb).mp hp).1 ((mem_strictDoms_iff hb).mp hq).1
  have hfind : (g.strictDoms b).find?
      (fun a => (g.strictDoms b).all fun c => decide (g.Dominates c a)) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    exact hnone u hu (by simpa using humax)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hfind
  refine ⟨a, by simp only [idom, hb, ite_true, ha], (mem_strictDoms_iff hb).mp
    (List.mem_of_find?_eq_some ha), fun c hc => ?_⟩
  have := List.find?_some ha
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this c ((mem_strictDoms_iff hb).mpr hc)

theorem idom_none_entry (g : Digraph) : g.idom g.entry = none := by
  have : g.strictDoms g.entry = [] := by
    rw [strictDoms, List.filter_eq_nil_iff]
    intro a ha
    have := (mem_doms_iff (reachable_entry g)).mp ha _ (path_singleton g g.entry)
    simp [List.mem_singleton.mp this]
  simp only [idom, reachable_entry g, ite_true, this]
  rfl

theorem mem_domTreeChildren_iff : b ∈ g.domTreeChildren a ↔ g.idom b = some a := by
  rw [domTreeChildren, List.mem_filter]
  refine ⟨fun h => by simpa using h.2, fun h => ⟨?_, by simp [h]⟩⟩
  by_cases hb : g.Reachable b
  · exact mem_nodes_of_reachable hb
  · rw [idom] at h; simp only [hb, ite_false] at h; exact absurd h (by simp)

/-! ## Dominator depth

The number of strict dominators of a node strictly increases along an edge of
the dominator tree and is bounded by `size`, so a recursion that walks the tree
upwards may use `size` as fuel and one that walks it downwards may use
`size - domDepth` as a measure. The counting is only sound because `nodes`, and
hence `doms` and `strictDoms`, is duplicate-free. -/

/-- The number of strict dominators of a node. -/
def domDepth (g : Digraph) (b : Nat) : Nat := (g.strictDoms b).length

/-- The computed dominator list is duplicate-free, being a filter of `nodes`. -/
theorem doms_nodup (g : Digraph) (b : Nat) : (g.doms b).Nodup :=
  List.Sublist.nodup List.filter_sublist g.nodes_nodup

/-- The computed strict dominator list is duplicate-free. -/
theorem strictDoms_nodup (g : Digraph) (b : Nat) : (g.strictDoms b).Nodup :=
  List.Sublist.nodup List.filter_sublist (g.doms_nodup b)

/-- A node is never one of its own strict dominators. -/
theorem not_mem_strictDoms_self (g : Digraph) (b : Nat) : b ∉ g.strictDoms b := by
  simp [strictDoms, List.mem_filter]

/-- The strict dominators of a node are nodes. -/
theorem strictDoms_subset_nodes (g : Digraph) (b : Nat) : g.strictDoms b ⊆ g.nodes :=
  fun _ hx => List.mem_of_mem_filter (List.mem_of_mem_filter hx)

/-- **The dominator depth of a reachable node is at most `size`**, so the number
of nodes is enough fuel to walk from any node up to the entry. -/
theorem domDepth_le (hb : g.Reachable b) : g.domDepth b ≤ g.size := by
  have hnd : (b :: g.strictDoms b).Nodup :=
    List.nodup_cons.mpr ⟨g.not_mem_strictDoms_self b, g.strictDoms_nodup b⟩
  have hsub : (b :: g.strictDoms b) ⊆ g.nodes := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_nodes_of_reachable hb
    · exact g.strictDoms_subset_nodes b hx
  have hle := List.Nodup.length_le_of_subset hnd hsub
  have hbound := g.length_nodes_le
  simp only [List.length_cons] at hle
  simp only [domDepth]
  omega

/-- Only a reachable node has an immediate dominator. -/
theorem reachable_of_idom (h : g.idom b = some a) : g.Reachable b := by
  rw [idom] at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- The immediate dominator strictly dominates. -/
theorem idom_strictlyDominates (h : g.idom b = some a) : g.StrictlyDominates a b := by
  have hb := reachable_of_idom h
  simp only [idom, hb, ite_true] at h
  exact (mem_strictDoms_iff hb).mp (List.mem_of_find?_eq_some h)

/-- The immediate dominator is the greatest strict dominator: every strict
dominator of `b` dominates it. -/
theorem dominates_idom (h : g.idom b = some a) (hc : g.StrictlyDominates x b) :
    g.Dominates x a := by
  have hb := reachable_of_idom h
  have hne : b ≠ g.entry := by
    rintro rfl
    rw [idom_none_entry] at h
    exact absurd h (by simp)
  obtain ⟨p, hp, -, hmax⟩ := idom_spec hb hne
  rw [hp] at h
  have : p = a := Option.some.inj h
  subst this
  exact hmax x hc

/-- **The dominator depth strictly increases along an edge of the dominator
tree.** The strict dominators of the immediate dominator are strict dominators
of the node, and the immediate dominator is one of the latter and none of the
former. -/
theorem domDepth_lt_of_idom (h : g.idom b = some a) : g.domDepth a < g.domDepth b := by
  have hb := reachable_of_idom h
  obtain ⟨hab, hne⟩ := idom_strictlyDominates h
  have ha : g.Reachable a := hab.reachable hb
  have hsub : (a :: g.strictDoms a) ⊆ g.strictDoms b := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (mem_strictDoms_iff hb).mpr ⟨hab, hne⟩
    · obtain ⟨hxa, -⟩ := (mem_strictDoms_iff ha).mp hx
      refine (mem_strictDoms_iff hb).mpr ⟨hxa.trans hab, ?_⟩
      rintro rfl
      exact hne (Dominates.antisymm ha hxa hab).symm
  have hnd : (a :: g.strictDoms a).Nodup :=
    List.nodup_cons.mpr ⟨g.not_mem_strictDoms_self a, g.strictDoms_nodup a⟩
  have hle := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_cons] at hle
  simp only [domDepth]
  omega

/-- **The step lemma for immediate dominators.** The immediate dominator of the
target of an edge dominates the source: it strictly dominates the target, so
`Dominates.of_edge` applies. -/
theorem idom_dominates_of_edge {l t p : Nat} (he : g.Edge l t) (h : g.idom t = some p) :
    g.Dominates p l :=
  have ⟨hd, hne⟩ := idom_strictlyDominates h
  Dominates.of_edge he hd hne

/-! ## Ancestry in the dominator tree -/

/-- `a` is an ancestor of `b` in the dominator tree: `a` is reached from `b` by
finitely many steps to the immediate dominator. -/
inductive DomAncestor (g : Digraph) : Nat → Nat → Prop where
  /-- Every node is its own ancestor. -/
  | refl (b : Nat) : DomAncestor g b b
  /-- An ancestor of the immediate dominator of `c` is an ancestor of `c`. -/
  | step {a b c : Nat} : g.idom c = some b → DomAncestor g a b → DomAncestor g a c

/-- An ancestor in the dominator tree dominates. -/
theorem DomAncestor.dominates (h : g.DomAncestor a b) : g.Dominates a b := by
  induction h with
  | refl => exact Dominates.refl g _
  | step hi _ ih => exact ih.trans (idom_strictlyDominates hi).1

/-- A dominator of a reachable node is an ancestor of it, by induction on the
dominator depth: a proper dominator of `b` dominates the immediate dominator of
`b`, which has strictly smaller depth. -/
private theorem domAncestor_of_dominates_aux :
    ∀ (n : Nat) {b a : Nat}, g.domDepth b ≤ n → g.Reachable b → g.Dominates a b →
      g.DomAncestor a b := by
  intro n
  induction n with
  | zero =>
    intro b a hn hb h
    by_cases hab : a = b
    · subst hab; exact .refl a
    · have hpos := List.length_pos_of_mem ((mem_strictDoms_iff hb).mpr ⟨h, hab⟩)
      rw [domDepth] at hn
      omega
  | succ n ih =>
    intro b a hn hb h
    by_cases hab : a = b
    · subst hab; exact .refl a
    · have hne : b ≠ g.entry := by
        rintro rfl
        exact hab (Dominates.eq_entry h)
      obtain ⟨p, hp, hps, hmax⟩ := idom_spec hb hne
      have hlt : g.domDepth p < g.domDepth b := domDepth_lt_of_idom hp
      exact .step hp (ih (by omega) (hps.1.reachable hb) (hmax a ⟨h, hab⟩))

/-- **Dominance is ancestry in the dominator tree** at every reachable node.
This is what licenses recursing over `domTreeChildren` to establish a
dominance-based invariant. -/
theorem domAncestor_iff_dominates (hb : g.Reachable b) :
    g.DomAncestor a b ↔ g.Dominates a b :=
  ⟨DomAncestor.dominates, domAncestor_of_dominates_aux (g.domDepth b) le_rfl hb⟩

end Digraph

end Silmaril.Machine.Graph
