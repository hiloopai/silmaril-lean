module

public import Silmaril.Project.Defs
public import Silmaril.Automata.Institution.Defs

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

`Thms` gives the decision procedures (typed shapes are `Decidable`) and the transfer from a
bound typed machine to its document (`jsonReach_iff_of_bound`, `jsonBisimilar_iff_of_bound`).
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

end Silmaril.Automata.Shapes
