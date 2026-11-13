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
* the word shapes: `Accepts` is decidable, and `Nonempty` through `Marked.nonempty_iff_reach`;
* **standalone JSON machines**: `jsonReach_iff_restrict`, `jsonSimulates_iff_restrict`,
  `jsonBisimilar_iff_restrict` (a document's problems are those of its restriction to the
  finitely many names it mentions) and `jsonAccepts_iff` (runs as successor sets), so every
  JSON shape is decidable without a typed binding;
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

/-! ## Words -/

omit [Fintype T] [DecidableEq T] in
instance (M : Marked S L) (w : List L) : Decidable (Accepts M w) :=
  inferInstanceAs (Decidable (∃ s, M.marks.initial s = true ∧
    ∃ s', M.machine.run s w = some s' ∧ M.marks.accepting s' = true))

omit [Fintype T] [DecidableEq T] in
/-- Language nonemptiness is reachability (`Marked.nonempty_iff_reach`), hence decidable. -/
instance (M : Marked S L) : Decidable (Shapes.Nonempty M) :=
  decidable_of_iff (∃ s, M.marks.initial s = true ∧ ∃ t, M.marks.accepting t = true ∧
      ReachVia M.machine.toLTS (fun l => (fun _ : L => true) l = true) s t) (by
    have : (fun l : L => (fun _ : L => true) l = true) = (fun _ => True) := by funext l; simp
    rw [this]; exact (Marked.nonempty_iff_reach M).symm)

/-! ## Standalone JSON machines -/

attribute [local instance] memFintype

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonReach_iff_restrict (d : Document) (ls : List String) (a b : String) :
    JsonReach d ls a b ↔ ReachVia (d.spec.restrict ([a, b] ++ d.spec.allStates)
      ([] ++ d.spec.allLabels)).toLTS (fun l => decide (l.1 ∈ ls) = true)
      ⟨a, by simp⟩ ⟨b, by simp⟩ :=
  Silmaril.Proofs.Automata.reach_iff_restrict (Silmaril.Proofs.Automata.closed_all _ _ _) ls _ _

instance (d : Document) (ls : List String) (a b : String) : Decidable (JsonReach d ls a b) :=
  decidable_of_iff _ (jsonReach_iff_restrict d ls a b).symm

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonBisimilar_iff_restrict (d e : Document) (a b : String) :
    JsonBisimilar d e a b ↔ Cslib.LTS.Bisimilarity
      (d.spec.restrict ([a] ++ d.spec.allStates) (d.spec.allLabels ++ e.spec.allLabels)).toLTS
      (e.spec.restrict ([b] ++ e.spec.allStates) (d.spec.allLabels ++ e.spec.allLabels)).toLTS
      ⟨a, by simp⟩ ⟨b, by simp⟩ := by
  have hd := Silmaril.Proofs.Automata.closed_all d.spec [a] []
  have he := Silmaril.Proofs.Automata.closed_all e.spec [b] d.spec.allLabels
  have hd' : Silmaril.Proofs.Automata.Closed d.spec ([a] ++ d.spec.allStates)
      (d.spec.allLabels ++ e.spec.allLabels) := fun x hx =>
    let ⟨h1, h2, h3⟩ := hd x hx; ⟨h1, List.mem_append_left _ (by simpa using h2), h3⟩
  exact Silmaril.Proofs.Automata.bisimilar_iff_restrict hd' he _ _

instance (d e : Document) (a b : String) : Decidable (JsonBisimilar d e a b) :=
  decidable_of_iff _ (jsonBisimilar_iff_restrict d e a b).symm

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonSimulates_iff_restrict (d e : Document) (a b : String) :
    JsonSimulates d e a b ↔ Cslib.LTS.Similarity
      (d.spec.restrict ([a] ++ d.spec.allStates) (d.spec.allLabels ++ e.spec.allLabels)).toLTS
      (e.spec.restrict ([b] ++ e.spec.allStates) (d.spec.allLabels ++ e.spec.allLabels)).toLTS
      ⟨a, by simp⟩ ⟨b, by simp⟩ := by
  have hd := Silmaril.Proofs.Automata.closed_all d.spec [a] []
  have he := Silmaril.Proofs.Automata.closed_all e.spec [b] d.spec.allLabels
  have hd' : Silmaril.Proofs.Automata.Closed d.spec ([a] ++ d.spec.allStates)
      (d.spec.allLabels ++ e.spec.allLabels) := fun x hx =>
    let ⟨h1, h2, h3⟩ := hd x hx; ⟨h1, List.mem_append_left _ (by simpa using h2), h3⟩
  exact Silmaril.Proofs.Automata.similar_iff_restrict hd' he _ _

instance (d e : Document) (a b : String) : Decidable (JsonSimulates d e a b) :=
  decidable_of_iff _ (jsonSimulates_iff_restrict d e a b).symm

omit [Fintype S] [Fintype T] [Fintype L] [DecidableEq S] [DecidableEq T] in
theorem jsonAccepts_iff (d : Document) (w : List String) :
    JsonAccepts d w ↔ ∃ t ∈ Spec.runSet d.spec d.layers.initial w,
      t ∈ d.layers.accepting :=
  Silmaril.Proofs.Automata.jsonAccepts_iff d w

instance (d : Document) (w : List String) : Decidable (JsonAccepts d w) :=
  decidable_of_iff _ (jsonAccepts_iff d w).symm

end Silmaril.Automata.Shapes
