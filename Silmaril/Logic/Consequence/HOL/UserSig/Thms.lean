module

public import Silmaril.Logic.Consequence.HOL.UserSig.Defs
public import Silmaril.Logic.Consequence.HOL.Standard.Thms
public import Silmaril.Logic.HOLLight.Check.Thms
import Silmaril.Proofs.Logic.Consequence.HOL.UserSig

/-!
# HOL over a user signature and theory: soundness, consistency, problems

* `kernelFrom_soundFor`: HOL with the axioms `Δ` is sound for the models of `Δ` (`pointsOf S Δ`),
  over any signature.
* Over `coinSig`: `cModel_models` (the model satisfies `c`), so `cTheory_consistent` (the theory `c`
  does not derive `⊥`).
* **Problems**: `cProp` (`c`), derived from the theory and true at `cPoint`; `cReflProp`
  (`c = c`), derived in pure HOL and true at every point of every model.
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight Silmaril.Logic.Institution.Metatheory

universe u

/-- **HOL with axioms is sound for the models of its axioms.** -/
theorem kernelFrom_soundFor (S : HolSig) (Δ : Theory) :
    (kernelFrom S Δ).SoundFor (pointsOf.{u} S Δ) :=
  Proofs.Logic.Consequence.HOL.UserSig.kernelFrom_soundFor S Δ

/-- The model satisfies the theory: `c` is true. -/
theorem cModel_models : Models cModel cTheory := Proofs.Logic.Consequence.HOL.UserSig.cModel_models

/-- A point of the model of the theory (type variables read as `ind`). -/
noncomputable def cPoint : (pointsOf.{0} coinSig cTheory).Model :=
  ⟨⟨cModel, fun _ => Carrier.ind, anyEnv _ _⟩, cModel_models⟩

/-- **The theory `c` is consistent**: it does not derive `⊥`. -/
theorem cTheory_consistent : (kernelFrom coinSig cTheory).ConsistentWrt (falsityProp coinSig) [] :=
  consistentWrt_of_sound (kernelFrom_soundFor.{0} coinSig cTheory) cPoint (fun _ h => by cases h)
    (fun h => Holds.not_falsity h)

/-- `c` has type `bool` (by the type checker). -/
theorem cTyping : HasType coinSig.sig [] cTm .bool := (Tm.typeOf?_eq_some_iff _ _ _ _).1 rfl

/-- `c` as a proposition. -/
def cProp : HOLProp coinSig := ⟨cTm, cTyping⟩

/-- `c = c`. -/
def cReflProp : HOLProp coinSig := ⟨Tm.equal .bool cTm cTm, HasType.equal trivial cTyping cTyping⟩

/-- `c`, from the theory, by its axiom. -/
theorem cProp_derived : kernelFrom coinSig cTheory [] cProp :=
  (Derives.axiom (List.mem_singleton_self _) cProp.2 : Derives coinSig.sig cTheory ∅ cTm)

/-- `c` is true at the point of the model. -/
theorem cProp_true : (pointsOf.{0} coinSig cTheory).satC cPoint cProp :=
  kernelFrom_soundFor.{0} coinSig cTheory [] _ cProp_derived cPoint (fun _ h => by cases h)

/-- `c = c`, in pure HOL, by REFL. -/
theorem cReflProp_derived : kernel coinSig [] cReflProp :=
  (Derives.refl cTyping : Derives coinSig.sig [] ∅ (Tm.equal .bool cTm cTm))

/-- `c = c` is true at every point of every model of the signature. -/
theorem cReflProp_true : ∀ x, (points.{0} coinSig).satC x cReflProp :=
  fun x => kernel_soundFor.{0} coinSig [] _ cReflProp_derived x (fun _ h => by cases h)

end Silmaril.Consequence.HOL
