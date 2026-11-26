module

public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.SSA.Peggy.Bridge.Equational.Translation
import Silmaril.Proofs.SSA.Peggy.Bridge.Equational.Institution

/-! # The many-sorted equational comorphism to Peggy with total primitives -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational

open CategoryTheory Silmaril.Logic.Algebraic
open RVSDG (Tuple)

variable {S : Type} {A B : ManySorted.Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

theorem observe_compileTerm (m : TotalPrimitiveModel ((signature S).obj A)) (t : ManySorted.Term A Γ s)
    (env : Tuple m.val.Value (profile Γ)) (idx : PEG.Index 0) :
    (compileTerm t).2.observe m.val env idx =
      .cons (some ((algebra m).eval (fun j => env.get (port Γ j)) t)) .nil :=
  Proofs.observe_compileTerm m t env idx

theorem compileEquation_map (f : A ⟶ B) (e : ManySorted.Equation A) :
    compileEquation (ManySorted.Equation.map f e) = (compileEquation e).map ((signature S).map f) :=
  Proofs.compileEquation_map f e

theorem exact_satisfaction (m : TotalPrimitiveModel ((signature S).obj A)) (e : ManySorted.Equation A) :
    (compileEquation e).Holds m.val ↔ e.Satisfies (algebra m) :=
  Proofs.exact_satisfaction m e

theorem algebraFunctor_natural (f : A ⟶ B) :
    algebraFunctor B ⋙ ManySorted.Signature.Hom.reductFunctor f =
      Silmaril.Inst.Disc.functor (totalPrimitiveReduct ((signature S).map f)) ⋙ algebraFunctor A :=
  Proofs.algebraFunctor_natural f

/-- Sentences compile forward, while target models restrict to source algebras. -/
def comorphism (S : Type) : Silmaril.Inst.Comorphism (ManySorted.inst S) (totalPrimitiveInst S) :=
  Silmaril.Inst.Comorphism.ofTranslation (signature S) (fun _ => compileEquation)
    algebraFunctor (fun _ => exact_satisfaction) compileEquation_map algebraFunctor_natural

theorem algebra_expand (m : ManySorted.Model A) : algebra (expand m) = m := Proofs.algebra_expand m

/-- Every ordinary algebra is the reduct of a total Peggy model. -/
theorem modelExpansive (S : Type) : (comorphism S).ModelExpansive :=
  fun _ m => ⟨expand m, algebra_expand m⟩

theorem entails_compile_iff (A : ManySorted.Signature S) (axioms : Set (ManySorted.Equation A))
    (e : ManySorted.Equation A) :
    ((ManySorted.institution S).obj A).Entails axioms e ↔
      ((totalPrimitivePlain S).room ((signature S).obj A)).Entails (compileEquation '' axioms) (compileEquation e) :=
  (comorphism S).entails_iff (modelExpansive S) A axioms e

end Silmaril.SSA.Peggy.Bridge.Equational
