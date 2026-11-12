module

public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig

@[expose] public section

/-!
# Extensionality for signature morphisms that keep argument positions

A `TheoryModel.Signature.Hom` carries a sort map, an operation map whose result sort depends
on the sort map, a bijection of argument positions and a proof of argument-sort compatibility.
For the instruction relabellings of the exact Isotope syntaxes and the calculus inclusions, the
argument bijection is always the identity on underlying positions (`SigHomArgVal`). Two such
morphisms with the same sort map are equal as soon as their operation maps agree up to `HEq`
(`sigHom_ext_of_argVal`), which is how relabellings are compared when the target instruction's
result type agrees only propositionally (through `castOp`).
-/

namespace Silmaril.Isotope.Institution

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {I : Type u₁} {J : Type u₂} {K : Type u₃}
  {S : TheoryModel.Signature.{u₁, v₁} I} {T : TheoryModel.Signature.{u₂, v₂} J}
  {U : TheoryModel.Signature.{u₃, v₃} K}

/-- The argument bijection of a signature morphism keeps every underlying position. -/
def SigHomArgVal (f : TheoryModel.Signature.Hom S T) : Prop :=
  ∀ {i : I} (o : S.Op i) (j : Fin (T.arity (f.op o))), (f.arg o j).val = j.val

theorem sigHomArgVal_id (S : TheoryModel.Signature.{u₁, v₁} I) :
    SigHomArgVal (TheoryModel.Signature.Hom.id S) :=
  fun _ _ => rfl

theorem sigHomArgVal_comp {g : TheoryModel.Signature.Hom T U} {f : TheoryModel.Signature.Hom S T}
    (hg : SigHomArgVal g) (hf : SigHomArgVal f) : SigHomArgVal (g.comp f) :=
  fun o j => (hf o (g.arg (f.op o) j)).trans (hg (f.op o) j)

/-- Extensionality for position-preserving signature morphisms with a common sort map. -/
theorem sigHom_ext_of_argVal {f g : TheoryModel.Signature.Hom S T} (hs : f.sort = g.sort)
    (hop : ∀ {i : I} (o : S.Op i), HEq (f.op o) (g.op o))
    (hf : SigHomArgVal f) (hg : SigHomArgVal g) : f = g := by
  obtain ⟨fs, fo, fa, fas⟩ := f
  obtain ⟨gs, go, ga, gas⟩ := g
  cases hs
  have ho : @fo = @go := by
    funext i o
    exact eq_of_heq (hop o)
  cases ho
  have ha : @fa = @ga := by
    funext i o
    exact Equiv.ext fun j => Fin.ext ((hf o j).trans (hg o j).symm)
  cases ha
  rfl

/-- Transport along an equation of sorts is heterogeneously the identity. -/
theorem castOp_heq {i j : I} (h : i = j) (o : S.Op i) : HEq (castOp S h o) o := by
  subst h
  rfl

/-- A sort-indexed operation map applied to a transported symbol. -/
theorem heq_apply_castOp {σ : I → J} (F : ∀ i, S.Op i → T.Op (σ i)) {i j : I} (h : i = j)
    (o : S.Op i) : HEq (F j (castOp S h o)) (F i o) := by
  subst h
  rfl

end Silmaril.Isotope.Institution
