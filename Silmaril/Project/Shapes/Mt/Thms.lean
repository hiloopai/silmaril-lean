module

public import Silmaril.Project.Shapes.Mt.Defs
public import Silmaril.Process.Mt.Csl.Thms

/-!
# Multi-threaded shapes: what is proved

* `safe_of_decomposed`: `silmaril.shapes.mt.decomposed` gives `silmaril.shapes.mt.safe`
  (`Csl.adequacy`);
* `model_of_decomposed`: through a sound concrete model (`silmaril.shapes.mt.sound`) the
  concrete system never faults and stands for `Good` configurations (`Csl.adequacy_model`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Mt

open Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V} {U : TIsa S} {I : HProp A V}
  {Q : Nat → U.St → Heap A V → Prop}

/-- A decomposed problem is safe. -/
theorem safe_of_decomposed {C₀ : Cfg U} (h : Decomposed U I Q C₀) : MtSafe U I Q C₀ :=
  fun _ r => let ⟨_, _, g⟩ := h; adequacy g r

/-- A decomposed problem is safe in every sound concrete model. -/
theorem model_of_decomposed {X : Model U} (hX : ModelSound X I Q) {C₀ : Cfg U}
    (h : Decomposed U I Q C₀) {c₀ c : X.Conf} (ha : X.abs c₀ C₀) (r : Star X.step c₀ c) :
    ¬ X.fault c ∧ ∃ C, X.abs c C ∧ Good U I Q C :=
  let ⟨_, _, g⟩ := h; adequacy_model hX g ha r

end Silmaril.Project.Shapes.Mt
