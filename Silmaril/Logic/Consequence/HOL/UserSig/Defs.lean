module

public import Silmaril.Logic.Consequence.HOL.Standard.Defs

/-!
# HOL over a user signature and theory: the standard interpretation of models of a theory

* `pointsOf S Δ`: HOL's standard interpretation (`points S`) restricted to points whose model
  satisfies every axiom of the theory `Δ` (`Models`). `Thms.kernelFrom_soundFor`: HOL with the
  axioms `Δ` is sound for it.

**A concrete user signature** (`coinSig`): HOL Light's initial signature plus one boolean constant
`c` (constant number `0`, monomorphic). `cTheory` is the theory asserting `c`; `cModel` is the
standard model with `c` interpreted as true, and `cPoint` a point of it.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight Silmaril.Logic.Institution.Metatheory

universe u

/-- **The standard interpretation of models of a theory**: points whose model satisfies `Δ`. -/
def pointsOf (S : HolSig) (Δ : Theory) : Satisfaction.{0, 0, u + 1} (List (HOLProp S)) (HOLProp S) where
  Model := {x : (points.{u} S).Model // Models x.1 Δ}
  satAx x Γ := (points.{u} S).satAx x.1 Γ
  satC x p := (points.{u} S).satC x.1 p

/-- **A user signature**: one boolean constant `c`. -/
def coinSig : HolSig := ⟨⟨[], [⟨0, .bool⟩]⟩⟩

/-- The constant `c`. -/
def cTm : Tm := .const (.user 0 [])

/-- The theory asserting `c`. -/
def cTheory : Theory := [cTm]

/-- **The model interpreting `c` as true**: the standard type model, `c ↦ true`. -/
noncomputable def cModel : Model.{0} coinSig.sig where
  toTypeModel := TypeModel.standard
  constant := fun n s h _ => by
    have hs : s = ⟨0, .bool⟩ := by
      match n, h with
      | 0, h => exact (Option.some.inj h).symm
      | _ + 1, h => exact absurd h (by simp [coinSig])
    subst hs
    exact (⟨true⟩ : ULift Bool)

end Silmaril.Consequence.HOL
