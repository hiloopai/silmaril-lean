module

public import Silmaril.SSA.LambdaRTL.Nameless.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Quotient.Defs

/-!
# Named and nameless λSSA institutions are isomorphic modulo semantic equivalence

`toDBCoHom R` and `ofDBCoHom S R` are identity on signatures and models. On the institutions
whose sentences are taken up to semantic equivalence (`Quotient.Inst.quot`), their sentence
translations are mutually inverse at every signature (`ofDB_toDB_quot`, `toDB_ofDB_quot`).

This is the precise sense in which the named and nameless institutions are equivalent. On the
raw institutions, nameless → named → nameless is the identity (`ofDB_toDB_sen`), but
named → nameless → named only renames binders and the context; it is not the identity on
sentences, so no isomorphism of the raw institutions is claimed.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.SSA.LambdaRTL.Quotient

variable (V L : Type) [DecidableEq V] [DecidableEq L] (M : Type → Type) [Monad M] (α : Type)

/-- Named → nameless → named is the identity on sentences up to semantic equivalence. -/
theorem ofDB_toDB_quot (S : Supply V) (R : M (L × α) → M (L × α) → Prop) (X : Sig)
    (q : ((Inst.quot (ssa V L M α R)).I.obj X).Sen) :
    (((CoHom.quot (ofDBCoHom V L M α S R)).ρ.app X).sen
      (((CoHom.quot (toDBCoHom V L M α R)).ρ.app X).sen q)) = q := by
  induction q using Quotient.ind with
  | _ j =>
    exact Quotient.sound fun m =>
      (((ofDBCoHom V L M α S R).ρ.app X).sat m _).trans
        (((toDBCoHom V L M α R).ρ.app X).sat m j)

/-- Nameless → named → nameless is the identity on sentences up to semantic equivalence. -/
theorem toDB_ofDB_quot (S : Supply V) (R : M (L × α) → M (L × α) → Prop) (X : Sig)
    (q : ((Inst.quot (dbInst L M α R)).I.obj X).Sen) :
    (((CoHom.quot (toDBCoHom V L M α R)).ρ.app X).sen
      (((CoHom.quot (ofDBCoHom V L M α S R)).ρ.app X).sen q)) = q := by
  induction q using Quotient.ind with
  | _ d =>
    exact Quotient.sound fun m =>
      (((toDBCoHom V L M α R).ρ.app X).sat m _).trans
        (((ofDBCoHom V L M α S R).ρ.app X).sat m d)

end Silmaril.SSA.LambdaRTL.Institution
