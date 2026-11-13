module

public import Silmaril.Automata.Spec.Defs
import Silmaril.Proofs.Automata.Spec

@[expose] public section

/-!
# Machine documents: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Spec.lean`):

* names: `FinNamed.name_inj`, `FinNamed.ofName?_name`, `FinNamed.mem_names_iff`;
* **typed ↔ JSON**: `toSpec_step_iff` (the spec of a typed machine has exactly its steps, on
  names), `mem_toSpec_edges`, `toSpec_wf`, `toSpec_deterministic`, and `stepFn_toSpec` (the
  step function a document denotes is the typed step function, mapped to names);
* `deterministic_of_B`: the edge-by-edge check `deterministicB` is sound;
* `stepFn_eq_some_iff`: on a deterministic spec, the step function and the relation agree;
* **canonical identity**: `canon_eq_iff`, `equivB_iff`, `canon_eq_of_equivB` (the
  kernel-evaluable membership check used by bindings), `Layers.canon_eq_of_equivB`, (same canonical form iff same states, labels and
  edges), `canon_step_iff`, `canon_canon`;
* **attachments**: `step_iff_of_canon_eq`: two typed machines (possibly over different
  inductive types) bound to the same canonical spec have the same steps on corresponding
  names, so facts about one transfer to the other;
* `typed_step_iff`: on a deterministic spec, `Spec.Typed` has exactly the spec's steps.
-/

namespace Silmaril.Automata

namespace FinNamed

variable {α : Type} [FinNamed α]

theorem name_inj {a b : α} (h : name a = name b) : a = b := Silmaril.Proofs.Automata.name_inj h

theorem ofName?_name (a : α) : ofName? (name a) = some a := Silmaril.Proofs.Automata.ofName?_name a

theorem mem_names_iff (n : String) : n ∈ names α ↔ ∃ a : α, name a = n :=
  Silmaril.Proofs.Automata.mem_names_iff n

end FinNamed

section ToSpec

variable {S L : Type} [FinNamed S] [FinNamed L]

theorem mem_toSpec_edges (M : DMachine S L) (e : Edge) :
    e ∈ M.toSpec.edges ↔ ∃ s l s', M.step s l = some s' ∧
      e = ⟨FinNamed.name s, FinNamed.name l, FinNamed.name s'⟩ :=
  Silmaril.Proofs.Automata.mem_toSpec_edges M e

theorem toSpec_step_iff (M : DMachine S L) (s : S) (l : L) (s' : S) :
    M.toSpec.Step (FinNamed.name s) (FinNamed.name l) (FinNamed.name s') ↔ M.step s l = some s' :=
  Silmaril.Proofs.Automata.toSpec_step_iff M s l s'

theorem toSpec_wf (M : DMachine S L) : M.toSpec.wf = true := Silmaril.Proofs.Automata.toSpec_wf M

theorem toSpec_deterministic (M : DMachine S L) : M.toSpec.Deterministic :=
  Silmaril.Proofs.Automata.toSpec_deterministic M

theorem stepFn_toSpec (M : DMachine S L) (s : S) (l : L) :
    M.toSpec.stepFn (FinNamed.name s) (FinNamed.name l) = (M.step s l).map FinNamed.name :=
  Silmaril.Proofs.Automata.stepFn_toSpec M s l

end ToSpec

namespace Spec

theorem stepFn_eq_some_iff {sp : Spec} (hd : sp.Deterministic) (s l d : String) :
    sp.stepFn s l = some d ↔ sp.Step s l d :=
  Silmaril.Proofs.Automata.stepFn_eq_some_iff hd s l d

theorem deterministic_of_B {sp : Spec} (h : sp.deterministicB = true) : sp.Deterministic :=
  Silmaril.Proofs.Automata.deterministic_of_B h

theorem canon_eq_iff (sp sp' : Spec) : sp.canon = sp'.canon ↔ sp.Equiv sp' :=
  Silmaril.Proofs.Automata.canon_eq_iff sp sp'

theorem canon_step_iff (sp : Spec) (s l d : String) : sp.canon.Step s l d ↔ sp.Step s l d :=
  Silmaril.Proofs.Automata.canon_step_iff sp s l d

theorem canon_canon (sp : Spec) : sp.canon.canon = sp.canon := Silmaril.Proofs.Automata.canon_canon sp

theorem equivB_iff (sp sp' : Spec) : sp.equivB sp' = true ↔ sp.Equiv sp' :=
  Silmaril.Proofs.Automata.equivB_iff sp sp'

/-- The kernel-checkable route to a binding: membership equivalence gives equal canonical
forms. -/
theorem canon_eq_of_equivB {sp sp' : Spec} (h : sp.equivB sp' = true) : sp.canon = sp'.canon :=
  (canon_eq_iff sp sp').mpr ((equivB_iff sp sp').mp h)

theorem typed_step_iff (sp : Spec) (hd : sp.Deterministic) (s : sp.State) (l : sp.Label)
    (s' : sp.State) : sp.Typed.step s l = some s' ↔ sp.Step s.1 l.1 s'.1 :=
  Silmaril.Proofs.Automata.typed_step_iff sp hd s l s'

end Spec

theorem Layers.canon_eq_of_equivB {ly ly' : Layers} (h : ly.equivB ly' = true) :
    ly.canon = ly'.canon :=
  Silmaril.Proofs.Automata.layers_canon_eq_of_equivB h

theorem step_iff_of_canon_eq {S₁ L₁ S₂ L₂ : Type} [FinNamed S₁] [FinNamed L₁] [FinNamed S₂]
    [FinNamed L₂] (M₁ : DMachine S₁ L₁) (M₂ : DMachine S₂ L₂)
    (h : M₁.toSpec.canon = M₂.toSpec.canon) {s : S₁} {l : L₁} {s' : S₁} {t : S₂} {k : L₂}
    {t' : S₂} (hs : FinNamed.name s = FinNamed.name t) (hl : FinNamed.name l = FinNamed.name k)
    (hs' : FinNamed.name s' = FinNamed.name t') :
    M₁.step s l = some s' ↔ M₂.step t k = some t' :=
  Silmaril.Proofs.Automata.step_iff_of_canon_eq M₁ M₂ h hs hl hs'

end Silmaril.Automata
