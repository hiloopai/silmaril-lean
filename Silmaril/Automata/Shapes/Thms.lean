module

public import Silmaril.Automata.Shapes.Defs
public import Silmaril.Automata.Decide.Thms
import Silmaril.Proofs.Automata.Shapes

@[expose] public section

/-!
# Standard problem shapes for finite machines: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Shapes.lean` and
`Silmaril/Proofs/Automata/Decide.lean`):

* the typed shapes `Reach`, `ReachSetB`, `Simulates`, `Bisimilar` are **decidable** for
  finite machines, through the verified fixpoint procedures, so `decide` (or
  `machine_decide`) proves or refutes them;
* `toLTS_eq_of_canon_eq`: documents with the same canonical spec have the same LTS;
* `jsonReach_iff_of_bound`, `jsonBisimilar_iff_of_bound`: for typed machines bound to
  documents (`machine_binding`), the typed and the JSON problems are equivalent, so a
  decision on the typed side answers the JSON problem.
-/

namespace Silmaril.Automata.Shapes

open Silmaril.Automata

variable {S T L : Type} [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T]

instance (M : DMachine S L) (P : L → Bool) (a b : S) : Decidable (Reach M P a b) :=
  decReachVia M P a b

instance (M : DMachine S L) (P : L → Bool) (a : S) (B : S → Bool) :
    Decidable (ReachSetB M P a B) :=
  inferInstanceAs (Decidable (∃ b, B b = true ∧ ReachVia M.toLTS (fun l => P l = true) a b))

instance (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    Decidable (Simulates M N s t) :=
  decSimilarity M N s t

instance (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    Decidable (Bisimilar M N s t) :=
  decBisimilarity M N s t

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem toLTS_eq_of_canon_eq {sp sp' : Spec} (h : sp.canon = sp'.canon) :
    sp.toLTS = sp'.toLTS :=
  Silmaril.Proofs.Automata.toLTS_eq_of_canon_eq h

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonReach_iff_of_bound [FinNamed S] [FinNamed L] (M : DMachine S L) (d : Document)
    (h : M.toSpec.canon = d.spec.canon) (P : L → Bool) (a b : S) :
    Reach M P a b ↔ JsonReach d (((FinNamed.elems (α := L)).filter P).map FinNamed.name)
      (FinNamed.name a) (FinNamed.name b) :=
  Silmaril.Proofs.Automata.jsonReach_iff_of_bound M d h P a b

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonBisimilar_iff_of_bound [FinNamed S] [FinNamed T] [FinNamed L] (M : DMachine S L)
    (N : DMachine T L) (d e : Document) (hd : M.toSpec.canon = d.spec.canon)
    (he : N.toSpec.canon = e.spec.canon) (s : S) (t : T) :
    Bisimilar M N s t ↔ JsonBisimilar d e (FinNamed.name s) (FinNamed.name t) :=
  Silmaril.Proofs.Automata.jsonBisimilar_iff_of_bound M N d e hd he s t

end Silmaril.Automata.Shapes
