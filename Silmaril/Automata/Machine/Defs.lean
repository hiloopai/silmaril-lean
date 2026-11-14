module

public import Silmaril.Automata.Named.Defs
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.Simulation
public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Prod
public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

/-!
# Finite machines: typed machines, relational machines, graphs, marks

Three levels of transition systems, each forgetting more:

| Level | Lean | Data |
| --- | --- | --- |
| typed deterministic machine | `DMachine S L` | `step : S → L → Option S` (partial: `none` rejects) |
| typed nondeterministic machine | `NMachine S L` | `step : S → L → Finset S` (`DMachine.toN` embeds the deterministic ones) |
| relational machine (LTS) | `Cslib.LTS S L` | `Tr : S → L → S → Prop` (CSLib's labelled transition systems) |
| unlabelled graph | `S → S → Prop` | `Cslib.LTS.UnlabelledTr` forgets labels |

There is no separate silmaril LTS type: relational machines **are** CSLib's `LTS`, so CSLib's
simulation (`Cslib.LTS.IsSimulation`, `Similarity`) and bisimulation (`IsBisimulation`,
`Bisimilarity`) are the notions used by the problem shapes and decided in
`Silmaril.Automata.Decide`.

**Reachability** is relative to a set of allowed labels (`ReachVia lts P a b`: `b` is reachable
from `a` by steps whose labels satisfy `P`, in zero or more steps). Restricting labels is what
makes reachability stable under signature morphisms in the machine institution
(`Silmaril.Automata.Institution`); unrestricted reachability is `ReachVia lts (fun _ => True)`.

**Composition.** `DMachine.prod`, `NMachine.prod` and `Marked.prod` are synchronous products
(both machines take every label); the product of marked machines accepts the intersection of
the languages (`Thms`).

**Words and CSLib automata.** `DMachine.run` runs a word; `Marked.Accepts` is acceptance
(from an initial to an accepting state), and `Marked.toNFA` is the same machine as a CSLib
`NA.FinAcc` (an NFA), with the same language (`accepts_toNFA_iff` in `Thms`).

**Marks** (`Marks S`) are a layer over a machine, not part of it: initial, accepting,
rejecting and error states as Boolean predicates. A `Marked` machine is a machine with marks,
and forgetting marks is a functor (`Silmaril.Automata.Category`). The same layering holds for
documents (`Silmaril.Automata.Spec.Layers`).
-/

namespace Silmaril.Automata

/-- A deterministic partial machine with states `S` and labels `L`. -/
structure DMachine (S L : Type) where
  /-- The next state, or `none` when the label is not accepted in the state. -/
  step : S → L → Option S

namespace DMachine

variable {S L : Type}

/-- The relational machine (CSLib LTS) of a deterministic machine. -/
def toLTS (M : DMachine S L) : Cslib.LTS S L := ⟨fun s l s' => M.step s l = some s'⟩

/-- Run a word of labels. -/
def run (M : DMachine S L) : S → List L → Option S
  | s, [] => some s
  | s, l :: ls => (M.step s l).bind fun s' => M.run s' ls

/-- A deterministic machine of an `Except`-valued step: errors reject. -/
def ofExcept {E : Type} (f : S → L → Except E S) : DMachine S L :=
  ⟨fun s l => (f s l).toOption⟩

end DMachine

/-- A nondeterministic machine with finitely many successors per state and label. -/
structure NMachine (S L : Type) where
  step : S → L → Finset S

/-- The relational machine (CSLib LTS) of a nondeterministic machine. -/
def NMachine.toLTS {S L : Type} (M : NMachine S L) : Cslib.LTS S L := ⟨fun s l s' => s' ∈ M.step s l⟩

/-- A deterministic machine as a nondeterministic one. -/
def DMachine.toN {S L : Type} (M : DMachine S L) : NMachine S L := ⟨fun s l => (M.step s l).toFinset⟩

/-- The synchronous product: both machines take the label. -/
def DMachine.prod {S T L : Type} (M : DMachine S L) (N : DMachine T L) : DMachine (S × T) L :=
  ⟨fun p l => match M.step p.1 l, N.step p.2 l with
    | some s, some t => some (s, t)
    | _, _ => none⟩

/-- The synchronous product of nondeterministic machines. -/
def NMachine.prod {S T L : Type} (M : NMachine S L) (N : NMachine T L) : NMachine (S × T) L :=
  ⟨fun p l => M.step p.1 l ×ˢ N.step p.2 l⟩

/-- `b` is reachable from `a` by steps whose labels satisfy `P` (reflexive-transitive). -/
def ReachVia {S L : Type} (lts : Cslib.LTS S L) (P : L → Prop) : S → S → Prop :=
  Relation.ReflTransGen fun s s' => ∃ l, P l ∧ lts.Tr s l s'

/-- Some state in `B` is reachable (set reachability). -/
def ReachSet {S L : Type} (lts : Cslib.LTS S L) (P : L → Prop) (a : S) (B : S → Prop) : Prop :=
  ∃ b, B b ∧ ReachVia lts P a b

/-- The marking layer: initial, accepting, rejecting and error states. -/
structure Marks (S : Type) where
  initial : S → Bool := fun _ => false
  accepting : S → Bool := fun _ => false
  rejecting : S → Bool := fun _ => false
  error : S → Bool := fun _ => false

/-- A machine with marks. -/
structure Marked (S L : Type) where
  machine : DMachine S L
  marks : Marks S

/-- Accepted words: from some initial state to some accepting state. -/
def Marked.Accepts {S L : Type} (M : Marked S L) (w : List L) : Prop :=
  ∃ s, M.marks.initial s = true ∧ ∃ s', M.machine.run s w = some s' ∧ M.marks.accepting s' = true

/-- The product of marks: initial and accepting in both, rejecting or error in either. -/
def Marks.prod {S T : Type} (m : Marks S) (n : Marks T) : Marks (S × T) where
  initial p := m.initial p.1 && n.initial p.2
  accepting p := m.accepting p.1 && n.accepting p.2
  rejecting p := m.rejecting p.1 || n.rejecting p.2
  error p := m.error p.1 || n.error p.2

/-- The synchronous product of marked machines (it accepts the intersection). -/
def Marked.prod {S T L : Type} (M : Marked S L) (N : Marked T L) : Marked (S × T) L :=
  ⟨M.machine.prod N.machine, M.marks.prod N.marks⟩

/-- A marked machine as a CSLib NFA (`Cslib.Automata.NA.FinAcc`). -/
def Marked.toNFA {S L : Type} (M : Marked S L) : Cslib.Automata.NA.FinAcc S L where
  Tr := M.machine.toLTS.Tr
  start := {s | M.marks.initial s = true}
  accept := {s | M.marks.accepting s = true}

end Silmaril.Automata
