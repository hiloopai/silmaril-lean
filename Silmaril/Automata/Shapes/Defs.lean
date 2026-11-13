module

public import Silmaril.Project.Defs
public import Silmaril.Automata.Institution.Defs
public import Silmaril.Automata.Machine.Defs
public import Mathlib.Data.Fintype.Basic

/-!
# Standard problem shapes: finite machines

The basic problems over machines, for typed machines (`DMachine` over `FinNamed` types) and for
JSON machines (`Document`s, on names):

| name | statement |
| --- | --- |
| `silmaril.shapes.machine.reach` | `Reach M P a b`: `b` reachable from `a` by labels in `P` |
| `silmaril.shapes.machine.reach_set` | `ReachSetB M P a B`: some state of `B` reachable |
| `silmaril.shapes.machine.simulates` | `Simulates M N s t`: `N` from `t` simulates `M` from `s` (CSLib `Similarity`) |
| `silmaril.shapes.machine.bisimilar` | `Bisimilar M N s t` (CSLib `Bisimilarity`) |
| `silmaril.shapes.machine.sat` | `SatSen M φ`: `M` satisfies a sentence of the machine institution |
| `silmaril.shapes.machine.json.reach` | `JsonReach d ls a b`, on a document's names |
| `silmaril.shapes.machine.json.bisimilar` | `JsonBisimilar d e a b`, on two documents' names |
| `silmaril.shapes.machine.json.simulates` | `JsonSimulates d e a b` |
| `silmaril.shapes.machine.accepts` | `Accepts M w`: a marked machine accepts the word `w` |
| `silmaril.shapes.machine.nonempty` | `Nonempty M`: it accepts some word |
| `silmaril.shapes.machine.json.accepts` | `JsonAccepts d w`, along a document's edges and layers |

`Thms` makes **every** shape decidable: the typed ones through the verified procedures, the
JSON ones on their own (`Spec.restrict`: a document only mentions finitely many names), and
gives the transfer from a bound typed machine to its document (`jsonReach_iff_of_bound`,
`jsonBisimilar_iff_of_bound`).
-/

@[expose] public section

namespace Silmaril.Automata.Shapes

open Silmaril.Automata

/-- **Reachability** by labels in `P`. -/
@[problem "silmaril.shapes.machine.reach"
  (title := "A state of a finite machine is reachable from another")]
def Reach {S L : Type} (M : DMachine S L) (P : L → Bool) (a b : S) : Prop :=
  ReachVia M.toLTS (fun l => P l = true) a b

/-- **Set reachability**: some state in `B` is reachable. -/
@[problem "silmaril.shapes.machine.reach_set"
  (title := "Some state of a set is reachable in a finite machine")]
def ReachSetB {S L : Type} (M : DMachine S L) (P : L → Bool) (a : S) (B : S → Bool) : Prop :=
  ∃ b, B b = true ∧ ReachVia M.toLTS (fun l => P l = true) a b

/-- **Simulation**: `N` from `t` simulates `M` from `s`. -/
@[problem "silmaril.shapes.machine.simulates"
  (title := "One finite machine simulates another")]
def Simulates {S T L : Type} (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) : Prop :=
  Cslib.LTS.Similarity M.toLTS N.toLTS s t

/-- **Bisimilarity**. -/
@[problem "silmaril.shapes.machine.bisimilar"
  (title := "Two states of finite machines are bisimilar")]
def Bisimilar {S T L : Type} (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) : Prop :=
  Cslib.LTS.Bisimilarity M.toLTS N.toLTS s t

/-- **A sentence of the machine institution** holds of a typed machine. -/
@[problem "silmaril.shapes.machine.sat"
  (title := "A finite machine satisfies a machine-institution sentence")]
def SatSen {S L : Type} (M : DMachine S L) (φ : Inst.Sen (Inst.sigOf S L)) : Prop :=
  Inst.Sat (Inst.DMachine.model M) φ

/-- **Reachability in a JSON machine**, on names, by labels in `ls`. -/
@[problem "silmaril.shapes.machine.json.reach"
  (title := "A state of a JSON machine is reachable from another")]
def JsonReach (d : Document) (ls : List String) (a b : String) : Prop :=
  ReachVia d.spec.toLTS (· ∈ ls) a b

/-- **Bisimilarity of JSON machines**, on names. -/
@[problem "silmaril.shapes.machine.json.bisimilar"
  (title := "Two states of JSON machines are bisimilar")]
def JsonBisimilar (d e : Document) (a b : String) : Prop :=
  Cslib.LTS.Bisimilarity d.spec.toLTS e.spec.toLTS a b

/-- **A marked machine accepts a word.** -/
@[problem "silmaril.shapes.machine.accepts"
  (title := "A finite machine accepts a word")]
def Accepts {S L : Type} (M : Marked S L) (w : List L) : Prop := M.Accepts w

/-- **A marked machine's language is nonempty.** -/
@[problem "silmaril.shapes.machine.nonempty"
  (title := "A finite machine accepts some word")]
def Nonempty {S L : Type} (M : Marked S L) : Prop := ∃ w, M.Accepts w

/-- **Simulation of JSON machines**, on names. -/
@[problem "silmaril.shapes.machine.json.simulates"
  (title := "One JSON machine simulates another")]
def JsonSimulates (d e : Document) (a b : String) : Prop :=
  Cslib.LTS.Similarity d.spec.toLTS e.spec.toLTS a b

/-- **A JSON machine with layers accepts a word** (of label names): a run, along edges, from an
initial to an accepting state. -/
@[problem "silmaril.shapes.machine.json.accepts"
  (title := "A JSON machine accepts a word")]
def JsonAccepts (d : Document) (w : List String) : Prop :=
  ∃ s ∈ d.layers.initial, ∃ t ∈ d.layers.accepting, d.spec.toLTS.MTr s w t

/-! ## Deciding problems of standalone JSON machines

A spec's LTS is on all strings, but only finitely many are ever involved: the declared and
mentioned names. `Spec.restrict sp U LU` is the nondeterministic machine on the names in `U` and
the labels in `LU`; when `U` and `LU` contain every edge's endpoints and label (`Spec.allStates`,
`Spec.allLabels`), reachability and (bi)similarity on the spec are those of the restriction
(`Thms`), which the verified procedures decide. -/

/-- Every state name a spec mentions (declared, or an endpoint of an edge). -/
def _root_.Silmaril.Automata.Spec.allStates (sp : Spec) : List String :=
  sp.states ++ sp.edges.flatMap fun e => [e.src, e.dst]

/-- Every label name a spec mentions. -/
def _root_.Silmaril.Automata.Spec.allLabels (sp : Spec) : List String := sp.labels ++ sp.edges.map Edge.label

/-- The states reachable by running a word from a list of states, along edges. -/
def _root_.Silmaril.Automata.Spec.runSet (sp : Spec) : List String → List String → List String
  | X, [] => X
  | X, l :: w => Spec.runSet sp ((sp.edges.filter fun e => decide (e.src ∈ X) && e.label == l).map
      Edge.dst) w

/-- The finite type of the members of a list. -/
@[instance_reducible] def memFintype (l : List String) : Fintype {x // x ∈ l} :=
  Fintype.ofList l.attach (fun x => List.mem_attach _ x)

attribute [local instance] memFintype

/-- A spec restricted to the names in `U` and the labels in `LU`. -/
def _root_.Silmaril.Automata.Spec.restrict (sp : Spec) (U LU : List String) : NMachine {x // x ∈ U} {x // x ∈ LU} :=
  ⟨fun x l => Finset.univ.filter fun y => sp.Step x.1 l.1 y.1⟩

end Silmaril.Automata.Shapes
