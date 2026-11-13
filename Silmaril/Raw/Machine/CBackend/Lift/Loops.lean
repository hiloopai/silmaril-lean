module

public import Silmaril.Machine.CBackend.Graph.Reducible.Defs
public import Silmaril.Machine.CBackend.Lift.Diff.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-!
# Rung 5: loop and region recovery

An agent proposes a loop nest — the back edges of a control-flow graph with the
loop each one closes — and `checkLoops` verifies it. The checker is decidable
and total, and every rejection names the node, edge or header at fault.

## What is checked

* The graph is **pruned**: its entry is one of its nodes and every node is
  reachable. This is not bookkeeping. Dominance is vacuously true at an
  unreachable node, so an "edge" into dead code is a back edge by default and
  the loops it closes are arbitrary; a proposal about unreachable code would be
  accepted and would mean nothing. A recovered control-flow graph with its dead
  code pruned has no such nodes.
* The graph is **reducible**: deleting its back edges leaves an acyclic graph,
  so every cycle contains a back edge and no cycle escapes the loop analysis
  (`Digraph.Reducible.exists_backEdge`). An irreducible graph — a loop entered
  at two different nodes — is rejected rather than silently mis-structured.
* Every proposed back edge **is** one: the header dominates the tail.
* The tails listed for a header are **exactly** the tails of the back edges into
  it, in the order `Digraph.backEdgeTails` computes them. The checker does not
  sort or complete its input: a proposal that lists them otherwise names a bug
  in the proposer.
* The body is **exactly** the union of the natural loops of those back edges,
  deduplicated. A header with several back edges — two `continue`s — has one
  loop, their union, because their individual natural loops need not be
  comparable and a nest of incomparable loops is not a nest.
* Headers are pairwise distinct, and **every** back edge of the graph is covered
  by some entry, so the proposal is a complete loop forest and not a selection.

## What acceptance buys

`checkLoops_sound_nesting` is the deliverable: any two proposed loops are
disjoint or one contains the other. That is what makes the next step — lifting
to λSSA's nested `cfg`s, where a loop must be a single-entry region — possible,
and it is proved rather than checked: `Digraph.naturalLoops_nested` shows the
condition could never fail for distinct headers, so a checker branch for it
could never fire.

`checkLoops_sound_header` is the other half: the header dominates every node of
its loop, so each loop is entered only at its header.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

open Silmaril.Machine.Graph (Digraph)

/-! ## Proposals -/

/-- One proposed loop: a header, the tails of the back edges that close it, and
its body. -/
structure LoopEntry where
  /-- The loop header. -/
  header : Nat
  /-- The tails of the back edges into the header. -/
  tails : List Nat
  /-- The nodes of the loop. -/
  body : List Nat
  deriving DecidableEq, Repr

/-- A proposed loop nest. -/
structure LoopSpec where
  /-- The loops, one per header. -/
  loops : List LoopEntry
  deriving DecidableEq, Repr

/-- The headers of a proposal. -/
def LoopSpec.headers (spec : LoopSpec) : List Nat := spec.loops.map LoopEntry.header

/-- Why a loop proposal was rejected. -/
inductive LoopReject where
  /-- The graph's entry is not one of its nodes. -/
  | entryOutOfRange (entry size : Nat)
  /-- This node is unreachable: prune it before proposing loops, because
  dominance, and so back-edge-hood, is vacuous there. -/
  | unreachable (node : Nat)
  /-- The graph is irreducible: this cycle edge is not a back edge and deleting
  the back edges leaves it on a cycle. A loop entered at two nodes cannot be
  structured. -/
  | irreducible (source target : Nat)
  /-- The proposal claims `source → header` is a back edge, but the header does
  not dominate the source, or there is no such edge. -/
  | notBackEdge (source header : Nat)
  /-- The tails listed for this header are not exactly the tails of the back
  edges into it, in the order the graph gives them. -/
  | wrongTails (header : Nat)
  /-- The body listed for this header is not the union of the natural loops of
  its back edges. -/
  | wrongBody (header : Nat)
  /-- Two entries claim the same header. A header has one loop, the union of
  the natural loops of all its back edges. -/
  | repeatedHeader (header : Nat)
  /-- The graph has this back edge and the proposal covers no loop with that
  header: the proposal is not a complete loop forest. -/
  | missingLoop (source header : Nat)
  deriving DecidableEq, Repr

/-! ## The checker -/

/-- The canonical body of a header: the union of the natural loops of its back
edges, with repetitions removed. -/
def canonicalBody (g : Digraph) (header : Nat) (tails : List Nat) : List Nat :=
  (g.naturalLoops header tails).dedup

/-- Every back edge of the graph, as a source-target pair. -/
def allBackEdges (g : Digraph) : List (Nat × Nat) :=
  (List.range g.size).flatMap fun a =>
    ((g.step a).filter fun b => decide (g.BackEdge a b)).map fun b => (a, b)

/-- An edge of the back-edge-free graph that lies on a cycle of it, which is
what reducibility forbids. -/
def irreducibleWitness (g : Digraph) : Option (Nat × Nat) :=
  (List.range g.size).findSome? fun a =>
    (g.dropBackEdges.step a).findSome? fun b =>
      if g.dropBackEdges.Reaches b a then some (a, b) else none

/-- Check one proposed loop. -/
def checkLoop (g : Digraph) (e : LoopEntry) : Option LoopReject :=
  match e.tails.find? fun t => !decide (g.BackEdge t e.header) with
  | some t => some (.notBackEdge t e.header)
  | none =>
    if e.tails ≠ g.backEdgeTails e.header then some (.wrongTails e.header)
    else if e.body ≠ canonicalBody g e.header e.tails then some (.wrongBody e.header)
    else none

/-- **Check a proposed loop nest.** -/
def checkLoops (g : Digraph) (spec : LoopSpec) : Except LoopReject Unit :=
  if g.entry < g.size then
    match (List.range g.size).find? fun n => !decide (g.Reachable n) with
    | some n => .error (.unreachable n)
    | none =>
      match irreducibleWitness g with
      | some (a, b) => .error (.irreducible a b)
      | none =>
        match firstDuplicate spec.headers with
        | some (i, _) => .error (.repeatedHeader (spec.headers[i]?.getD 0))
        | none =>
          match spec.loops.findSome? (checkLoop g) with
          | some r => .error r
          | none =>
            match (allBackEdges g).find? fun e => !decide (e.2 ∈ spec.headers) with
            | some e => .error (.missingLoop e.1 e.2)
            | none => .ok ()
  else .error (.entryOutOfRange g.entry g.size)

/-! ## Inverting the checker

`checkLoops_inv` is the single inversion; every statement below reads one
conjunct of it back into the fact the checker established. -/

/-- A pair is a back edge of the graph with its source in range exactly when
`allBackEdges` lists it. -/
theorem mem_allBackEdges {g : Digraph} {a b : Nat} :
    (a, b) ∈ allBackEdges g ↔ (a < g.size ∧ g.BackEdge a b) := by
  simp only [allBackEdges, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨c, hc, d, ⟨-, hbe⟩, rfl, rfl⟩
    exact ⟨hc, hbe⟩
  · rintro ⟨ha, hbe⟩
    exact ⟨a, ha, b, ⟨hbe.1, hbe⟩, rfl, rfl⟩

/-- Everything a successful `checkLoops` established, in one statement. -/
theorem checkLoops_inv {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    g.entry < g.size ∧
      ((List.range g.size).find? fun n => !decide (g.Reachable n)) = none ∧
      irreducibleWitness g = none ∧
      firstDuplicate spec.headers = none ∧
      spec.loops.findSome? (checkLoop g) = none ∧
      ((allBackEdges g).find? fun e => !decide (e.2 ∈ spec.headers)) = none := by
  rw [checkLoops] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hentry
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hreach
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hirr
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hdup
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hloops
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hcover
  exact ⟨hentry, hreach, hirr, hdup, hloops, hcover⟩

/-- Everything a successful `checkLoop` established about one entry. -/
theorem checkLoop_inv {g : Digraph} {e : LoopEntry} (h : checkLoop g e = none) :
    (∀ t ∈ e.tails, g.BackEdge t e.header) ∧ e.tails = g.backEdgeTails e.header ∧
      e.body = canonicalBody g e.header e.tails := by
  rw [checkLoop] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hbe
  split_ifs at h with h₁ h₂
  all_goals first
    | exact ⟨fun t ht => by simpa using List.find?_eq_none.mp hbe t ht,
        not_not.mp h₁, not_not.mp h₂⟩

/-- Acceptance establishes that the graph is pruned. -/
theorem checkLoops_pruned {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    g.Pruned := by
  obtain ⟨hentry, hreach, -, -, -, -⟩ := checkLoops_inv h
  exact ⟨hentry, fun n hn => by simpa using List.find?_eq_none.mp hreach n hn⟩

/-- Acceptance establishes that the graph is reducible, so every cycle of it
contains a back edge (`Digraph.Reducible.exists_backEdge`) and the proposal's
loops account for every cycle. -/
theorem checkLoops_reducible {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    g.Reducible := by
  obtain ⟨-, -, hirr, -, -, -⟩ := checkLoops_inv h
  intro a ha b hb hr
  have h₁ := List.findSome?_eq_none_iff.mp hirr a ha
  have h₂ := List.findSome?_eq_none_iff.mp h₁ b hb
  simp [hr] at h₂

/-- Acceptance establishes that every tail of every entry closes a real back
edge into its header. -/
theorem checkLoops_backEdges {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    ∀ e ∈ spec.loops, ∀ t ∈ e.tails, g.BackEdge t e.header := by
  obtain ⟨-, -, -, -, hloops, -⟩ := checkLoops_inv h
  exact fun e he => (checkLoop_inv (List.findSome?_eq_none_iff.mp hloops e he)).1

/-- Acceptance establishes that the tails of each entry are exactly the tails of
the back edges into its header, so each tail is a node of the graph. -/
theorem checkLoops_tails {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    ∀ e ∈ spec.loops, e.tails = g.backEdgeTails e.header := by
  obtain ⟨-, -, -, -, hloops, -⟩ := checkLoops_inv h
  exact fun e he => (checkLoop_inv (List.findSome?_eq_none_iff.mp hloops e he)).2.1

/-- Acceptance establishes that every tail of every entry is a node of the
graph. -/
theorem checkLoops_tails_lt {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    ∀ e ∈ spec.loops, ∀ t ∈ e.tails, t < g.size := by
  intro e he t ht
  rw [checkLoops_tails h e he] at ht
  exact (Digraph.mem_backEdgeTails_iff.mp ht).1

/-- Acceptance establishes that every body is the union of the natural loops of
its header's back edges. -/
theorem checkLoops_body {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ()) :
    ∀ e ∈ spec.loops, ∀ x, x ∈ e.body ↔ g.InNaturalLoops e.header e.tails x := by
  obtain ⟨-, -, -, -, hloops, -⟩ := checkLoops_inv h
  intro e he x
  rw [(checkLoop_inv (List.findSome?_eq_none_iff.mp hloops e he)).2.2]
  exact List.mem_dedup

/-- Acceptance establishes that headers are pairwise distinct. -/
theorem checkLoops_headers_nodup {g : Digraph} {spec : LoopSpec}
    (h : checkLoops g spec = .ok ()) : spec.headers.Nodup := by
  obtain ⟨-, -, -, hdup, -, -⟩ := checkLoops_inv h
  exact nodup_of_firstDuplicate_none 0 _ hdup

/-- Distinct headers mean distinct entries, for a list whose headers are
pairwise distinct. -/
private theorem eq_of_header_eq : ∀ (l : List LoopEntry), (l.map LoopEntry.header).Nodup →
    ∀ e₁ ∈ l, ∀ e₂ ∈ l, e₁.header = e₂.header → e₁ = e₂ := by
  intro l
  induction l with
  | nil => intro _ e₁ he₁; exact absurd he₁ (by simp)
  | cons c t ih =>
    intro hnd e₁ he₁ e₂ he₂ hh
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he₁ with h1 | h1
    · rcases List.mem_cons.mp he₂ with h2 | h2
      · exact h1.trans h2.symm
      · exact absurd ⟨e₂, h2, by rw [← h1]; exact hh.symm⟩ hnd.1
    · rcases List.mem_cons.mp he₂ with h2 | h2
      · exact absurd ⟨e₁, h1, by rw [← h2]; exact hh⟩ hnd.1
      · exact ih hnd.2 e₁ h1 e₂ h2 hh

/-- Two entries of an accepted proposal with the same header are the same
entry. -/
theorem checkLoops_header_inj {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ())
    {e₁ e₂ : LoopEntry} (h₁ : e₁ ∈ spec.loops) (h₂ : e₂ ∈ spec.loops)
    (hh : e₁.header = e₂.header) : e₁ = e₂ :=
  eq_of_header_eq spec.loops (checkLoops_headers_nodup h) e₁ h₁ e₂ h₂ hh

/-- Acceptance establishes that no back edge of the graph is left out. -/
theorem checkLoops_complete {g : Digraph} {spec : LoopSpec} (h : checkLoops g spec = .ok ())
    {a b : Nat} (hb : g.BackEdge a b) (ha : a < g.size) :
    ∃ e ∈ spec.loops, e.header = b ∧ a ∈ e.tails := by
  obtain ⟨-, -, -, -, -, hcover⟩ := checkLoops_inv h
  have hmem : b ∈ spec.headers := by
    simpa using List.find?_eq_none.mp hcover (a, b) (mem_allBackEdges.mpr ⟨ha, hb⟩)
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  refine ⟨e, he, rfl, ?_⟩
  rw [checkLoops_tails h e he]
  exact Digraph.mem_backEdgeTails_iff.mpr ⟨ha, hb⟩

/-! ## Soundness -/

/-- **An accepted loop nest is properly nested**: any two of its loops are
disjoint or one contains the other. This is the fact that makes structuring
possible — a loop that partially overlapped another could not be lifted to a
single-entry region — and it is a theorem, not a check: for distinct headers it
could never fail, so a checker branch for it could never fire. -/
theorem checkLoops_sound_nesting {g : Digraph} {spec : LoopSpec}
    (h : checkLoops g spec = .ok ()) {e₁ e₂ : LoopEntry} (h₁ : e₁ ∈ spec.loops)
    (h₂ : e₂ ∈ spec.loops) (hne : e₁ ≠ e₂) :
    (∀ x, ¬ (x ∈ e₁.body ∧ x ∈ e₂.body)) ∨
    (∀ y ∈ e₂.body, y ∈ e₁.body) ∨ (∀ y ∈ e₁.body, y ∈ e₂.body) := by
  have hhne : e₁.header ≠ e₂.header := fun hh => hne (checkLoops_header_inj h h₁ h₂ hh)
  have hb₁ := checkLoops_backEdges h e₁ h₁
  have hb₂ := checkLoops_backEdges h e₂ h₂
  have hl₁ := checkLoops_tails_lt h e₁ h₁
  have hl₂ := checkLoops_tails_lt h e₂ h₂
  have hm₁ := checkLoops_body h e₁ h₁
  have hm₂ := checkLoops_body h e₂ h₂
  rcases Digraph.naturalLoops_nested (checkLoops_pruned h) hb₁ hb₂ hl₁ hl₂ hhne with
    hdis | hsub | hsub
  · exact .inl fun x hx => hdis x ⟨(hm₁ x).mp hx.1, (hm₂ x).mp hx.2⟩
  · exact .inr (.inl fun y hy => (hm₁ y).mpr (hsub y ((hm₂ y).mp hy)))
  · exact .inr (.inr fun y hy => (hm₂ y).mpr (hsub y ((hm₁ y).mp hy)))

/-- **The header of an accepted loop dominates every node of it**, so each loop
is a single-entry region: control reaches the loop only through its header. -/
theorem checkLoops_sound_header {g : Digraph} {spec : LoopSpec}
    (h : checkLoops g spec = .ok ()) {e : LoopEntry} (he : e ∈ spec.loops)
    {x : Nat} (hx : x ∈ e.body) : g.Dominates e.header x :=
  Digraph.dominates_naturalLoops (checkLoops_backEdges h e he) ((checkLoops_body h e he x).mp hx)

/-- A node on a cycle of at least two nodes is a node of the graph. -/
theorem lt_size_of_cycle {g : Digraph} {a : Nat} {ls : List Nat} (hp : g.Path a a ls)
    (hlen : 2 ≤ ls.length) : a < g.size := by
  match ls, hlen, hp with
  | x :: c :: t, _, hp =>
    have hx : x = a := by simpa using hp.1
    have hch := List.isChain_cons_cons.mp hp.2.2
    have hsuf : g.Path c a (c :: t) :=
      ⟨rfl, by rw [← List.getLast?_cons_cons]; exact hp.2.1, hch.2⟩
    rcases Digraph.eq_or_lt_size_of_path hsuf with heq | hlt
    · exact heq ▸ Digraph.lt_size_of_edge (hx ▸ hch.1)
    · exact hlt

/-- **The headers of an accepted loop nest are cut points**: every cycle of the
graph passes through the header of some proposed loop. This is the form a
verification-condition generator needs — put an invariant at each header and
every remaining path is acyclic — and the reason a loop proposal (from DWARF
line tables, a decompiler or a human) is worth checking: once accepted, no cycle
escapes the invariants placed on it. -/
theorem checkLoops_sound_cutpoints {g : Digraph} {spec : LoopSpec}
    (h : checkLoops g spec = .ok ()) {a : Nat} {ls : List Nat} (hp : g.Path a a ls)
    (hlen : 2 ≤ ls.length) :
    ∃ e ∈ spec.loops, e.header ∈ ls := by
  obtain ⟨u, v, hu, hv, hbe⟩ := (checkLoops_reducible h).exists_backEdge hp hlen
  have hult : u < g.size := Digraph.mem_lt_size_of_path hp (lt_size_of_cycle hp hlen) u hu
  obtain ⟨e, he, hhdr, -⟩ := checkLoops_complete h hbe hult
  exact ⟨e, he, hhdr ▸ hv⟩

/-- **Every cycle of an accepted graph passes through a proposed loop.** Taken
with the two theorems above, this is what a structuring pass needs: the loops
are a forest, each is single-entry, and nothing cyclic is left over. -/
theorem checkLoops_sound_cycles {g : Digraph} {spec : LoopSpec}
    (h : checkLoops g spec = .ok ()) {a : Nat} {ls : List Nat} (hp : g.Path a a ls)
    (hlen : 2 ≤ ls.length) :
    ∃ e ∈ spec.loops, ∃ x ∈ ls, x ∈ e.body := by
  have halt : a < g.size := lt_size_of_cycle hp hlen
  obtain ⟨u, v, hu, hv, hbe⟩ := (checkLoops_reducible h).exists_backEdge hp hlen
  have hult : u < g.size := Digraph.mem_lt_size_of_path hp halt u hu
  obtain ⟨e, he, hhdr, htail⟩ := checkLoops_complete h hbe hult
  refine ⟨e, he, u, hu, (checkLoops_body h e he u).mpr ?_⟩
  simp only [Digraph.InNaturalLoops, Digraph.naturalLoops, List.mem_flatMap]
  refine ⟨u, htail, ?_⟩
  by_cases huv : u = e.header
  · rw [huv]
    exact Digraph.inNaturalLoop_header g _ _
  · exact Digraph.mem_naturalLoop_of_path (Digraph.path_singleton g u)
      (fun z hz => by rw [List.mem_singleton.mp hz]; exact huv) hult

end Silmaril.Machine.Lift
