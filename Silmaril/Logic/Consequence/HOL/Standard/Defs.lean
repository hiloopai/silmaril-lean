module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.HOLLight.Check.Thms
public import Silmaril.Logic.HOLLight.SExp.Defs
public import Silmaril.Logic.HOLLight.Consistency

/-!
# HOL's standard interpretation in Lean, over the abstract syntax and over S-expressions

**Models.** HOL Light's standard semantics (`Silmaril.Logic.HOLLight.Semantics`) interprets:
- `bool` as `ULift Bool` and `ind` as `ULift ℕ`;
- function types as Lean's full function spaces, `=` as Lean's equality and `@` as Hilbert choice;
- each user constant through the model.

A model lives in `Type u`. A *point* is a model with a type valuation and an assignment of the free
variables. `points S` is this semantics as an interpretation (`Satisfaction`) of the propositions
over `S`. It is the semantics of `HOL.seq`.

**Denotation.** `denote M ρ ν h` is the value of a typed closed term, from its typing `h`: the unique
value its evaluation relation gives (`Eval`, which exists and is unique). `HOLProp.meaning x p` is
the Lean proposition a HOL proposition means at the point `x`.

**The standard point** `standardPoint` is the standard model of the initial signature
(`Model.standard`, universe 0), with type variables read as `ind` and an arbitrary assignment.

**Over S-expressions.** `propCodec S` presents HOL propositions as the S-expressions of their terms.
Decoding is the pipeline: read the term (`HOLLight.SExp.decodeTm`), type-check it
(`Tm.typeOf?`) and require `bool`. Errors are exact (`Thms`): a form that is not canonical, a term
with no type, or a term of another type.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight Silmaril.Logic.Concrete
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

/-- **HOL's standard semantics as an interpretation**: points (a model in `Type u`, a type
valuation, an assignment), and truth at a point. -/
def points (S : HolSig) : Satisfaction.{0, 0, u + 1} (List (HOLProp S)) (HOLProp S) where
  Model := Σ M : Model.{u} S.sig, Σ ρ : TypeValuation.{u}, FreeEnv M ρ
  satAx x Γ := ∀ q ∈ Γ, satAt x.1 x.2 q
  satC x p := satAt x.1 x.2 p

/-- **The denotation of a typed closed term**: its unique value. -/
noncomputable def denote {S : HolSig} (M : Model.{u} S.sig) (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ)
    {t : Tm} {A : Ty} (h : HasType S.sig [] t A) : Value M ρ A :=
  Classical.choose (h.eval_exists M ρ ν BoundEnv.empty)

/-- **The Lean proposition a HOL proposition means** at a point. -/
def HOLProp.meaning {S : HolSig} (x : (points.{u} S).Model) (p : HOLProp S) : Prop :=
  (points.{u} S).satC x p

/-- An arbitrary assignment of the free variables (carriers are nonempty). -/
noncomputable def anyEnv {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u}) : FreeEnv M ρ :=
  fun _ A => Classical.choice (A.denote M.toTypeModel ρ).property

/-- HOL's initial signature. -/
def initialSig : HolSig := ⟨initialSignature⟩

/-- **The standard point**: the standard model of the initial signature, type variables read as
`ind`, an arbitrary assignment. -/
noncomputable def standardPoint : (points.{0} initialSig).Model :=
  ⟨Model.standard.{0}, fun _ => Carrier.ind, anyEnv _ _⟩

/-- `⊥` as a proposition of any signature. -/
def falsityProp (S : HolSig) : HOLProp S := HOLProp.falsity

/-- Decode an S-expression as a proposition: read the term, type-check it, require `bool`. -/
def decodeProp (S : HolSig) (e : Silmaril.Logic.Smt.SE) : Option (HOLProp S) :=
  match h : (SExp.decodeTm e).bind (fun t => if t.typeOf? S.sig [] = some .bool then some t else none) with
  | some t => some ⟨t, by
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t', -, h⟩ := h
      split at h
      · cases h; exact (Tm.typeOf?_eq_some_iff _ _ _ _).1 (by assumption)
      · cases h⟩
  | none => none

end Silmaril.Consequence.HOL
