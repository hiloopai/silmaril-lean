module

public import Silmaril.Semantics.MemoryRefinement.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
public import Mathlib.CategoryTheory.Category.Basic

/-! # Transport, composition and changes of observation alphabet -/

@[expose] public section

namespace Silmaril.Semantics.MemoryRefinement

universe u v w
variable {Obs : Type v} {View : Type w} {first middle last : Model.{u} Obs}

/-- State the postcondition once. The no-UB half of the WP travels with it. -/
theorem Hom.transport (arrow : Hom first last) {left right} (related : arrow.rel left right)
    {post : Obs → Prop} (proved : first.wp post left) : last.wp post right :=
  let ⟨safe, back⟩ := arrow.sound related proved.1
  ⟨safe, fun out allowed => proved.2 out (back out allowed)⟩

/-- This is exactly the local law needed to transport *all* predicates, not just sufficient.
For the reverse implication choose the source's own set of possible observations as the post. -/
theorem soundAt_iff (left : first.Entry) (right : last.Entry) : SoundAt first last left right ↔
    ∀ post, first.wp post left → last.wp post right :=
  ⟨fun sound _ proved => let back := sound proved.1
    ⟨back.1, fun out allowed => proved.2 out (back.2 out allowed)⟩,
   fun move safe => move (first.may left) ⟨safe, fun _ allowed => allowed⟩⟩

instance : CategoryTheory.Category (Model.{u} Obs) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp arrow := Hom.ext (Operational.relComp_eq_left arrow.rel)
  comp_id arrow := Hom.ext (Operational.relComp_eq_right arrow.rel)
  assoc one two three := Hom.ext (Operational.relComp_assoc one.rel two.rel three.rel)

/-- A 2-cell is inclusion of certified entry pairs, not equivalence of machines. -/
instance : PartialOrder (Hom first last) := PartialOrder.lift Hom.rel fun _ _ => Hom.ext

theorem Hom.comp_mono {one one' : Hom first middle} {two two' : Hom middle last}
    (left : one ≤ one') (right : two ≤ two') : one.comp two ≤ one'.comp two' :=
  fun _ _ ⟨mid, h₁, h₂⟩ => ⟨mid, left _ _ h₁, right _ _ h₂⟩

theorem safeRefines_iff {State : Type u} (impl spec : Operational.WithUB State Obs) :
    impl.SafeRefines spec ↔ ∀ entry, SoundAt (ofOperational spec) (ofOperational impl) entry entry :=
  ⟨fun h _ safe => ⟨(h safe).1, fun _ allowed => (h safe).2 allowed⟩,
    fun h {_} safe => ⟨(h _ safe).1, fun {_} => (h _ safe).2 _⟩⟩

/-- The satisfaction condition for a change of alphabet, unlike one-way refinement. -/
theorem wp_map (model : Model Obs) (view : Obs → View) (post : View → Prop) (entry : model.Entry) :
    (model.map view).wp post entry ↔ model.wp (post ∘ view) entry :=
  ⟨fun h => ⟨h.1, fun out allowed => h.2 _ ⟨out, allowed, rfl⟩⟩,
   fun h => ⟨h.1, fun _ ⟨out, allowed, eq⟩ => eq ▸ h.2 out allowed⟩⟩

def Hom.map (arrow : Hom first last) (view : Obs → View) : Hom (first.map view) (last.map view) :=
  ⟨arrow.rel, fun related safe => let back := arrow.sound related safe
    ⟨back.1, fun _ ⟨out, allowed, eq⟩ => ⟨out, back.2 out allowed, eq⟩⟩⟩

/-- On a partial evaluator, safety means successful evaluation, not vacuous partial correctness. -/
theorem wp_ofEval {Entry : Type u} {eval : Entry → Option Obs} {post : Obs → Prop} {entry} :
    (ofEval eval).wp post entry ↔ ∃ out, eval entry = some out ∧ post out := by
  cases h : eval entry <;> simp [Model.wp, ofEval, h]

/-- For deterministic fragments, it suffices to match successful evaluations. -/
def Hom.ofEval {Left Right : Type u} {src : Left → Option Obs} {dst : Right → Option Obs}
    (rel : Left → Right → Prop)
    (matchOk : ∀ {left right out}, rel left right → src left = some out → dst right = some out) :
    Hom (ofEval src) (ofEval dst) :=
  ⟨rel, fun related safe => by
    obtain ⟨out, ok⟩ := Option.ne_none_iff_exists'.mp safe
    have hit := matchOk related ok
    exact ⟨fun bad => Option.some_ne_none _ (hit.symm.trans bad), fun _ h => ok.trans (hit.symm.trans h)⟩⟩

end Silmaril.Semantics.MemoryRefinement
