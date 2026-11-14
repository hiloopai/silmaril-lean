module

public import Silmaril.Machine.CBackend.Graph.Dominance.Defs
public import Silmaril.Automata.Machine.Defs
public import Silmaril.Automata.Spec.Defs

@[expose] public section

/-!
# Rooted graphs: dominator-tree problems, multiple entries, region trees

The generic graph-analysis API shared by control-flow graphs (Wasm functions, machine code) and
finite state machines. Graphs are `Silmaril.Machine.Graph.Digraph`: nodes `0 … size - 1`, a
successor function and **one distinguished entry**; `Reachable`, `Dominates`, `idom` and their
proofs are that library's. This module states the *problems* about trees over such a graph and
keeps apart notions that are easy to conflate:

**Dominator trees.** A tree over the nodes is given by a parent function `p : Nat → Option Nat`
(`Ancestor p` is its transitive closure).

* `DomSound g p`: the entry has no parent, and every reachable non-entry node has a parent that
  strictly dominates it. Many trees are sound: the immediate-dominator tree, but also the star `starTree`
  that hangs every node from the entry.
* `DomExact g p`: on reachable nodes, the ancestors of `b` are **exactly** its strict dominators.
  On a finite rooted graph this tree exists (`g.idom`) and is **unique** on reachable nodes
  (`Thms`: `idom_exact`, `exact_unique`). Uniqueness holds because dominance restricted to the
  dominators of a reachable node is a total order (`Dominates.total`), so the parent of `b` must
  be the greatest strict dominator. Nothing is claimed about unreachable nodes.

**Multiple entries.** `SetDominates g E a b`: every path from a node of `E` (in range) to `b`
passes through `a`. `withRoot g E` adds a synthetic root (node `g.size`) whose successors are
`E`; for nodes of `g`, dominance in `withRoot g E` is exactly `SetDominates g E`
(`Thms`: `withRoot_dominates_iff`), so the single-entry theory (and its unique exact tree, rooted
at the synthetic node) covers entry sets.

**Region trees.** `RTree` brackets nodes into nested groups (`leaf n`, `group cs`); `flatten`
lists its nodes. Unlike the dominator tree, region trees are **not** unique: many bracketings
have the same flattening, and `Coarsens t t'` (dissolve inner groups, one at a time) relates a
finer tree to coarser ones with the same flattening (`Thms`: `Coarsens.flatten_eq`). A group is
*valid* for a graph when its node set is a single-entry region (`SingleEntry`): every edge into it
from outside lands on its header. The bridge to dominance is `Thms`: `header_dominates`: the
header of a single-entry region not containing the entry (or headed by it) dominates every node
of the region. No thesis-specific notion (braces) is assumed beyond these definitions.
-/

namespace Silmaril.Automata.Graph

open Silmaril.Machine.Graph

/-- A tree over the nodes, as a parent function. -/
abbrev Parent := Nat → Option Nat

/-- The ancestor relation of a parent function: `Ancestor p a b` when `a` is reached from `b`
by following parents one or more times. -/
inductive Ancestor (p : Parent) : Nat → Nat → Prop
  | parent {a b : Nat} : p b = some a → Ancestor p a b
  | up {a b c : Nat} : p c = some b → Ancestor p a b → Ancestor p a c

/-- **Sound dominator tree**: parents strictly dominate (on reachable nodes). -/
def DomSound (g : Digraph) (p : Parent) : Prop :=
  p g.entry = none ∧ ∀ b, g.Reachable b → b ≠ g.entry → ∃ a, p b = some a ∧ g.StrictlyDominates a b

/-- **Exact dominator tree**: on reachable nodes, ancestors are exactly strict dominators. -/
def DomExact (g : Digraph) (p : Parent) : Prop :=
  ∀ a b, g.Reachable b → (Ancestor p a b ↔ g.StrictlyDominates a b)

/-- The star tree: every reachable non-entry node hangs from the entry (sound, rarely exact). -/
noncomputable def starTree (g : Digraph) : Parent := fun b =>
  open Classical in if g.Reachable b ∧ b ≠ g.entry then some g.entry else none

/-! ## Multiple entries -/

/-- The entries of `E` that are nodes of `g`. -/
def inRange (g : Digraph) (E : List Nat) : List Nat := E.filter fun e => decide (e < g.size)

/-- `a` dominates `b` for the entry set `E`: every path from an entry (in range) to `b` passes
through `a`. -/
def SetDominates (g : Digraph) (E : List Nat) (a b : Nat) : Prop :=
  ∀ e ∈ inRange g E, ∀ ls, g.Path e b ls → a ∈ ls

/-- `g` with a synthetic root `g.size` whose successors are the entries `E`; successors outside
the old node range are dropped, so the root has no incoming edge. -/
def withRoot (g : Digraph) (E : List Nat) : Digraph where
  size := g.size + 1
  succ n := if n = g.size then inRange g E else (g.succ n).filter fun m => decide (m < g.size)
  entry := g.size

/-! ## Region trees -/

/-- A bracketing of graph nodes into nested groups. -/
inductive RTree where
  | leaf (n : Nat)
  | group (cs : List RTree)
  deriving Repr, Inhabited

namespace RTree

/-- The nodes of a tree, left to right. -/
def flatten : RTree → List Nat
  | leaf n => [n]
  | group cs => flattenList cs
where
  flattenList : List RTree → List Nat
    | [] => []
    | c :: cs => flatten c ++ flattenList cs

/-- One coarsening step: dissolve one group that is a direct child, splicing its children in
place (the coarser tree has the same nodes in the same order). -/
inductive Dissolve : RTree → RTree → Prop
  | here (pre post cs : List RTree) :
      Dissolve (group (pre ++ group cs :: post)) (group (pre ++ cs ++ post))
  | inside (pre post : List RTree) {c c' : RTree} :
      Dissolve c c' → Dissolve (group (pre ++ c :: post)) (group (pre ++ c' :: post))

/-- `Coarsens t t'`: `t'` is obtained from `t` by dissolving groups (reflexive, transitive). -/
def Coarsens : RTree → RTree → Prop := Relation.ReflTransGen Dissolve

/-- The groups of a tree, each as its node list. -/
def groups : RTree → List (List Nat)
  | leaf _ => []
  | group cs => flatten (group cs) :: groupsList cs
where
  groupsList : List RTree → List (List Nat)
    | [] => []
    | c :: cs => groups c ++ groupsList cs

end RTree

/-- `S` is a single-entry region with header `h`: every edge into `S` from outside lands on `h`. -/
def SingleEntry (g : Digraph) (S : List Nat) (h : Nat) : Prop :=
  h ∈ S ∧ ∀ x y, g.Edge x y → x ∉ S → y ∈ S → y = h

/-- A region tree is valid for `g` when each of its groups is a single-entry region, with a
header in the group that is the entry whenever the entry is in it. -/
def RTree.Valid (g : Digraph) (t : RTree) : Prop :=
  ∀ S ∈ t.groups, ∃ h, SingleEntry g S h ∧ (g.entry ∈ S → h = g.entry)

/-! ## State machines as rooted graphs

A finite machine and a distinguished initial state give a rooted graph: node `i` is the `i`-th
state of `FinNamed.elems`, with an edge to every state reachable in one step by some label
(labels are forgotten). `Thms`: `machine_reachable_iff` (reachability in the graph is
unrestricted reachability in the machine). Every graph problem above then applies to
machines: dominators of states, exact dominator trees, region trees of states. -/

section Machines

variable {S L : Type} [FinNamed S] [FinNamed L] [DecidableEq S]

/-- The node of a state. -/
def stateIndex (s : S) : Nat := (FinNamed.elems (α := S)).idxOf s

/-- The rooted graph of a nondeterministic machine from `init`. -/
def _root_.Silmaril.Automata.NMachine.toDigraph (M : NMachine S L) (init : S) : Digraph where
  size := (FinNamed.elems (α := S)).length
  succ i := match (FinNamed.elems (α := S))[i]? with
    | some s => ((FinNamed.elems (α := S)).filter fun t =>
        (FinNamed.elems (α := L)).any fun l => decide (t ∈ M.step s l)).map stateIndex
    | none => []
  entry := stateIndex init

/-- The rooted graph of a deterministic machine from `init`. -/
def _root_.Silmaril.Automata.DMachine.toDigraph (M : DMachine S L) (init : S) : Digraph := M.toN.toDigraph init

end Machines

/-- The rooted graph of a machine document from the state named `init`: node `i` is the `i`-th
declared state (edges to undeclared names are dropped, labels are forgotten). -/
def _root_.Silmaril.Automata.Spec.toDigraph (sp : Spec) (init : String) : Digraph where
  size := sp.states.length
  succ i := match sp.states[i]? with
    | some s => (sp.edges.filter fun e => e.src == s).map fun e => sp.states.idxOf e.dst
    | none => []
  entry := sp.states.idxOf init

/-- The immediate dominator of every node, as a table (`none` at the entry and unreachable
nodes): what the registry records and the explorer draws, checked by the kernel. -/
def idomTable (g : Digraph) : List (Option Nat) := (List.range g.size).map g.idom

end Silmaril.Automata.Graph
