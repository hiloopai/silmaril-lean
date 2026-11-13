module

public import Silmaril.Automata.Decide.Defs
import Silmaril.Proofs.Automata.Decide

@[expose] public section

/-!
# Decision procedures for finite machines: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Decide.lean`):

* `iterate_fix_of_inflationary`, `iterate_fix_of_deflationary`: a monotone iteration on the
  finsets of a finite type reaches its fixpoint within `Fintype.card` steps;
* `mem_reachSet`: `reachSet` is exactly the label-restricted reachable set (`ReachVia`);
* `mem_simSet`: `simSet` is exactly CSLib's `Similarity` (the greatest simulation);
* `mem_bisimSet`: `bisimSet` is exactly CSLib's `Bisimilarity`.

The `Decidable` instances below make `decide` a verified decision procedure for these
problems on concrete machines; `machine_decide` is `decide` with kernel reduction for larger
instances.
-/

namespace Silmaril.Automata

theorem iterate_fix_of_inflationary {α : Type} [Fintype α] [DecidableEq α]
    (F : Finset α → Finset α) (hF : ∀ X, X ⊆ F X) (X : Finset α) :
    F (F^[Fintype.card α] X) = F^[Fintype.card α] X :=
  Silmaril.Proofs.Automata.iterate_fix_of_inflationary F hF X

theorem iterate_fix_of_deflationary {α : Type} [Fintype α] [DecidableEq α]
    (F : Finset α → Finset α) (hF : ∀ X, F X ⊆ X) (X : Finset α) :
    F (F^[Fintype.card α] X) = F^[Fintype.card α] X :=
  Silmaril.Proofs.Automata.iterate_fix_of_deflationary F hF X

variable {S T L : Type} [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T]

theorem mem_reachSet (M : DMachine S L) (P : L → Bool) (a b : S) :
    b ∈ reachSet M P a ↔ ReachVia M.toLTS (fun l => P l = true) a b :=
  Silmaril.Proofs.Automata.mem_reachSet M P a b

theorem mem_simSet (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    (s, t) ∈ simSet M N ↔ Cslib.LTS.Similarity M.toLTS N.toLTS s t :=
  Silmaril.Proofs.Automata.mem_simSet M N s t

theorem mem_bisimSet (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    (s, t) ∈ bisimSet M N ↔ Cslib.LTS.Bisimilarity M.toLTS N.toLTS s t :=
  Silmaril.Proofs.Automata.mem_bisimSet M N s t

instance decReachVia (M : DMachine S L) (P : L → Bool) (a b : S) :
    Decidable (ReachVia M.toLTS (fun l => P l = true) a b) :=
  decidable_of_iff _ (mem_reachSet M P a b)

instance decSimilarity (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    Decidable (Cslib.LTS.Similarity M.toLTS N.toLTS s t) :=
  decidable_of_iff _ (mem_simSet M N s t)

instance decBisimilarity (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) :
    Decidable (Cslib.LTS.Bisimilarity M.toLTS N.toLTS s t) :=
  decidable_of_iff _ (mem_bisimSet M N s t)

/-- Decide a reachability, similarity or bisimilarity fact of a concrete finite machine. -/
macro "machine_decide" : tactic => `(tactic| decide +kernel)

end Silmaril.Automata
