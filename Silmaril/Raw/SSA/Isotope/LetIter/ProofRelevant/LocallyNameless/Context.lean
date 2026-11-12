module

public import Silmaril.Raw.SSA.Isotope.Ctx.Weakening
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless

-- Infer indexed binders locally.
set_option autoImplicit true

namespace Silmaril.Isotope

namespace BoundCtx

/-- Proof-relevant, same-shape bound weakening. New slot types are subtypes of
the corresponding old slots; no bound slot can be dropped or shadowed. -/
inductive Wk [SubtypingCore τ] : BoundCtx τ n → BoundCtx τ n → Type u where
  | nil : Wk .nil .nil
  | snoc : Wk Γ' Γ → Subty A' A → Wk (.snoc Γ' A') (.snoc Γ A)

def Wk.at [SubtypingCore τ] : {n : Nat} →
    {Γ' Γ : BoundCtx τ n} → Wk Γ' Γ →
    (ι : Fin n) → Subty (Γ'.get ι) (Γ.get ι)
  | 0, .nil, .nil, .nil, ι => Fin.elim0 ι
  | _ + 1, .snoc _ _, .snoc _ _, .snoc w h, ι =>
      Fin.cases h (fun j => w.at j) ι

/-- Exact, same-shape weakening for bound contexts. -/
inductive StrictWk : BoundCtx τ n → BoundCtx τ n → Type u where
  | nil : StrictWk .nil .nil
  | snoc : StrictWk Γ' Γ → StrictWk (.snoc Γ' A) (.snoc Γ A)

def StrictWk.toWk {τ : Type u} [SubtypingCore τ]
    {n : Nat} {Γ' Γ : BoundCtx τ n} : StrictWk Γ' Γ → Wk Γ' Γ
  | .nil => .nil
  | .snoc w => .snoc w.toWk (Subty.refl _)

/-- Proposition-truncated bound weakening, exposed separately. -/
abbrev WkProp (Γ' Γ : BoundCtx τ n) [SubtypingCore τ] : Prop :=
  Nonempty (Wk Γ' Γ)

end BoundCtx
end Silmaril.Isotope

namespace Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless

/-- Proof-relevant lookup transport for one visible free variable. -/
structure LookupRefines {ν : Type u} {τ : Type v}
    [DecidableEq ν] [SubtypingCore τ]
    (Γ : Isotope.Ctx ν τ) (x : ν) (A : τ) : Type (max u v) where
  ty : τ
  found : Γ.lookup x = some ty
  subty : Subty ty A

/-- A shared free-context weakening together with exactly the lookup transport
needed by typing. Bare `Ctx.Wk` permits incompatible newly shadowing names;
this wrapper deliberately rejects those derivations. -/
structure FreeWk {ν : Type u} {τ : Type v}
    [DecidableEq ν] [SubtypingCore τ]
    (Γ' Γ : Isotope.Ctx ν τ) : Type (max u v) where
  structural : Isotope.Ctx.Wk Γ' Γ
  lookup : ∀ x A, Γ.lookup x = some A → LookupRefines Γ' x A

/-- Proposition-truncated free weakening, exposed separately. -/
abbrev FreeWkProp [DecidableEq ν] [SubtypingCore τ]
    (Γ' Γ : Isotope.Ctx ν τ) : Prop := Nonempty (FreeWk Γ' Γ)

end Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless
