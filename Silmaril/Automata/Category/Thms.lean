module

public import Silmaril.Automata.Category.Defs
public import Mathlib.CategoryTheory.Equivalence
import Silmaril.Proofs.Automata.Category

@[expose] public section

/-!
# Categories of finite machines: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Category.lean` and inline):

* `JMach.typedFunctor_isEquivalence`: **valid deterministic JSON machines and typed finite
  machines are equivalent categories** (`JMach.equivalence : JMach ≌ TMach`). The functor is
  fully faithful by construction and essentially surjective: every typed machine is isomorphic,
  through the names of its states and labels, to the machine its spec denotes;
* `JMarked.typedFunctor_isEquivalence`: **marked JSON machines (documents with layers) and
  marked typed machines are equivalent** (`JMarked.equivalence`): the isomorphism of the
  unmarked case preserves and reflects every layer;
* `MarkedMach.forget_faithful`, `toLTSCat_faithful`: forgetting marks, and passing to CSLib's
  LTS category, lose no morphisms.
-/

namespace Silmaril.Automata

open CategoryTheory

instance JMach.typedFunctor_isEquivalence : JMach.typedFunctor.IsEquivalence :=
  Silmaril.Proofs.Automata.typedFunctor_isEquivalence

/-- JSON machines and typed machines are equivalent. -/
noncomputable def JMach.equivalence : JMach ≌ TMach := JMach.typedFunctor.asEquivalence

instance JMarked.typedFunctor_isEquivalence : JMarked.typedFunctor.IsEquivalence :=
  Silmaril.Proofs.Automata.markedFunctor_isEquivalence

/-- Marked JSON machines (documents with layers) and marked typed machines are equivalent. -/
noncomputable def JMarked.equivalence : JMarked ≌ MarkedMach := JMarked.typedFunctor.asEquivalence

instance MarkedMach.forget_faithful : MarkedMach.forget.Faithful :=
  ⟨fun {_ _} _ _ h => MarkedMach.Hom.ext h⟩

instance toLTSCat_faithful : toLTSCat.Faithful := ⟨fun {_ _} h k e => by
  have e1 := congrArg Cslib.LTS.Morphism.stateMap e
  have e2 := congrArg Cslib.LTS.Morphism.labelMap e
  exact TMach.hom_ext e1 (funext fun l => Option.some.inj (congrFun e2 l))⟩

end Silmaril.Automata
