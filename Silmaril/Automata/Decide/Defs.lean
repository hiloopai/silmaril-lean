module

public import Silmaril.Automata.Machine.Thms
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Option

@[expose] public section

/-!
# Decision procedures for finite machines

Verified fixpoint computations over Mathlib `Finset`s, for nondeterministic machines
(`NMachine`, finitely many successors) with finite state and label types, and through
`DMachine.toN` for deterministic ones:

* `reachSet M P a`: the states reachable from `a` by labels in `P` (least fixpoint of
  `X ↦ X ∪ post X` from `{a}`);
* `simSet M N`: the greatest simulation between `M` and `N` (greatest fixpoint of the
  refinement of `univ`);
* `bisimSet M N`: the greatest bisimulation.

Each iteration runs `Fintype.card` steps, which suffices because the iteration is monotone
in a finite lattice (`iterate_fix_of_inflationary`, `iterate_fix_of_deflationary` in `Thms`).
`Thms` proves each set exact (`mem_reachSet`, `mem_simSet`, `mem_bisimSet`) against
`ReachVia` and CSLib's `Similarity`/`Bisimilarity`, and derives `Decidable` instances, so
`decide` proves or refutes reachability, similarity and bisimilarity of concrete states.
-/

namespace Silmaril.Automata

variable {S T L : Type} [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T]

namespace NMachine

/-- One step of the reachability iteration: `X` and its successors by labels in `P`. -/
def reachStep (M : NMachine S L) (P : L → Bool) (X : Finset S) : Finset S :=
  X ∪ X.biUnion fun s => (Finset.univ.filter fun l => P l).biUnion fun l => M.step s l

/-- The states reachable from `a` by labels in `P`. -/
def reachSet (M : NMachine S L) (P : L → Bool) (a : S) : Finset S :=
  (reachStep M P)^[Fintype.card S] {a}

/-- The simulation condition at a pair, against the candidate `R`. -/
def simOK (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) (p : S × T) : Bool :=
  decide (∀ l : L, ∀ s' ∈ M.step p.1 l, ∃ t' ∈ N.step p.2 l, (s', t') ∈ R)

/-- One refinement step of the greatest simulation. -/
def simStep (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) : Finset (S × T) :=
  R.filter fun p => simOK M N R p

/-- The greatest simulation of `M` by `N`. -/
def simSet (M : NMachine S L) (N : NMachine T L) : Finset (S × T) :=
  (simStep M N)^[Fintype.card (S × T)] Finset.univ

/-- The bisimulation condition at a pair. -/
def bisimOK (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) (p : S × T) : Bool :=
  decide (∀ l : L, (∀ s' ∈ M.step p.1 l, ∃ t' ∈ N.step p.2 l, (s', t') ∈ R) ∧
    (∀ t' ∈ N.step p.2 l, ∃ s' ∈ M.step p.1 l, (s', t') ∈ R))

/-- One refinement step of the greatest bisimulation. -/
def bisimStep (M : NMachine S L) (N : NMachine T L) (R : Finset (S × T)) : Finset (S × T) :=
  R.filter fun p => bisimOK M N R p

/-- The greatest bisimulation between `M` and `N`. -/
def bisimSet (M : NMachine S L) (N : NMachine T L) : Finset (S × T) :=
  (bisimStep M N)^[Fintype.card (S × T)] Finset.univ

end NMachine

/-- The states a deterministic machine reaches from `a` by labels in `P`. -/
def reachSet (M : DMachine S L) (P : L → Bool) (a : S) : Finset S := M.toN.reachSet P a

/-- The greatest simulation between deterministic machines. -/
def simSet (M : DMachine S L) (N : DMachine T L) : Finset (S × T) := M.toN.simSet N.toN

/-- The greatest bisimulation between deterministic machines. -/
def bisimSet (M : DMachine S L) (N : DMachine T L) : Finset (S × T) := M.toN.bisimSet N.toN

end Silmaril.Automata
