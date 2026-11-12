module

public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Compilations

/-!
# The lambda-SSA / let-iter isomorphism as an isomorphism in `CoIns`

`Morphism.SSAIter.quotEquiv` is a bijection between single-exit scoped lambda-SSA regions modulo
`LambdaSSA.Region.Obs` and positional let-iter terms modulo `LetIter.LocallyNameless.Tm.Obs`.
This file lifts it to institutions.

Observational equivalence implies equal behaviour at every model (`iterBeh_eq_of_obs`,
`ssaBeh_eq_of_obs`), so behaviours descend to the observational quotients, giving two quotient
observational institutions `letIterQ Φ` and `lambdaSSAQ Φ` (sentences are equations and
refinements between equivalence classes). The quotient maps `compileQuot` and `encodeQuot` are
translations of behavioural semantics (`compileQ`, `encodeQ`), and their comorphisms are mutually
inverse in `CoIns`: `iterSSAIso` is an **isomorphism in `CoIns`** whose signature functors and
model functors are identities and whose sentence translations are `quotEquiv.symm`
(`compileQuot`, the forward map `hom`) and `quotEquiv` (`encodeQuot`, the inverse `inv`).
The two composites are identities on the nose, by `encodeQuot_compileQuot` and
`compileQuot_encodeQuot`.

Exactly this notion holds and no more:

* **On the unquotiented institutions** `letIter Φ` and `lambdaSSA Φ 1` the comorphisms
  `iterSSACoHom` and the single-exit encoding are *not* inverse: the sentence composites are
  only the identity up to observational equivalence (`roundTrip_term`, `roundTrip_single`), not
  syntactically. On sentences their composites are the identity modulo semantic equivalence of
  sentences, which is what the quotient construction turns into equality.
* **At `labels ≠ 1` exits** the encoding `ssaIterCoHom Φ labels` is a comorphism, and decoding
  is a retraction of it on valid equations (`lambdaSSA_obsEq_decode_encode`, from
  `roundTrip_region`), but decoding is not a comorphism: an untyped term need not produce a
  well-formed tag, so there is no inverse in `CoIns`.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Institution.Observational

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (ScopedRegion termSetoid regionSetoid compileQuot
  encodeQuot compileQuot_encodeQuot encodeQuot_compileQuot quotEquiv)

variable {Φ : Type u}

/-- The behavioural semantics of let-iter terms modulo observational equivalence. -/
def letIterQ (Φ : Type u) : Behaviour.{u, v, w} Φ where
  Prog n := Quotient (termSetoid.{u, v, w} Φ n)
  Out := Value
  beh M q := Quotient.lift (iterBeh M) (fun _ _ h => iterBeh_eq_of_obs h M) q

/-- The behavioural semantics of single-exit scoped lambda-SSA regions modulo observational
equivalence. -/
def lambdaSSAQ (Φ : Type u) : Behaviour.{u, v, w} Φ where
  Prog n := Quotient (regionSetoid.{u, v, w} Φ 1 n)
  Out α := Nat × Value α
  beh M q := Quotient.lift (ssaBeh 1 M) (fun _ _ h => ssaBeh_eq_of_obs h M) q

/-- `compileQuot` as a translation of the quotient behavioural semantics. -/
def compileQ (Φ : Type u) :
    Behaviour.Translation (letIterQ.{u, v, w} Φ) (lambdaSSAQ.{u, v, w} Φ) where
  prog := compileQuot
  out value := ((0 : Nat), value)
  dom := Set.univ
  injOn := @pair0_injOn
  beh_sub := fun _ _ o _ => by cases o <;> trivial
  beh_prog := fun M q => Quotient.inductionOn q fun t => ssaBeh_compileSingle M t

/-- `encodeQuot` as a translation of the quotient behavioural semantics. -/
def encodeQ (Φ : Type u) :
    Behaviour.Translation (lambdaSSAQ.{u, v, w} Φ) (letIterQ.{u, v, w} Φ) where
  prog := encodeQuot
  out := Prod.snd
  dom := {x | x.1 = 0}
  injOn := @snd_injOn
  beh_sub := fun M q => Quotient.inductionOn q fun r => ssaBeh_single_sub M r
  beh_prog := fun M q => Quotient.inductionOn q fun r => iterBeh_encodeSingle M r

/-- Compiling then encoding is the identity on quotient sentences, by
`Morphism.SSAIter.encodeQuot_compileQuot`. -/
theorem encodeQ_compileQ_sen {n : Nat} (φ : Sentence (Quotient (termSetoid.{u, v, w} Φ n))) :
    (φ.map compileQuot).map encodeQuot = φ := by
  cases φ with
  | eq a b => exact congrArg₂ Sentence.eq (encodeQuot_compileQuot a) (encodeQuot_compileQuot b)
  | le a b => exact congrArg₂ Sentence.le (encodeQuot_compileQuot a) (encodeQuot_compileQuot b)

/-- Encoding then compiling is the identity on quotient sentences, by
`Morphism.SSAIter.compileQuot_encodeQuot`. -/
theorem compileQ_encodeQ_sen {n : Nat}
    (φ : Sentence (Quotient (regionSetoid.{u, v, w} Φ 1 n))) :
    (φ.map encodeQuot).map compileQuot = φ := by
  cases φ with
  | eq a b => exact congrArg₂ Sentence.eq (compileQuot_encodeQuot a) (compileQuot_encodeQuot b)
  | le a b => exact congrArg₂ Sentence.le (compileQuot_encodeQuot a) (compileQuot_encodeQuot b)

/-- **The isomorphism.** The let-iter and single-exit lambda-SSA observational institutions,
taken modulo observational equivalence, are isomorphic in `CoIns`, by the comorphisms of the
compiler `IterSSA.compile` and the encoding `SSAIter.encodeSingle`; on sentences the forward map
`hom` is `Morphism.SSAIter.quotEquiv.symm` and the inverse `inv` is `quotEquiv`, and on signatures and models it is the identity. -/
def iterSSAIso (Φ : Type u) :
    Iso (C := CoIns.{0, 0, u, max u (v + 1) (w + 1), max u (v + 1) (w + 1)})
      (letIterQ.{u, v, w} Φ).inst (lambdaSSAQ.{u, v, w} Φ).inst where
  hom := (compileQ Φ).coHom
  inv := (encodeQ Φ).coHom
  hom_inv_id := by
    refine Inst.CoHom.ext rfl ?_
    apply NatTrans.ext
    funext n
    apply Room.hom_ext
    · funext φ
      exact encodeQ_compileQ_sen φ
    · rfl
  inv_hom_id := by
    refine Inst.CoHom.ext rfl ?_
    apply NatTrans.ext
    funext n
    apply Room.hom_ext
    · funext φ
      exact compileQ_encodeQ_sen φ
    · rfl

/-- On sentences, the inverse of the isomorphism is `quotEquiv` applied to both sides. -/
theorem iterSSAIso_inv_sen {n : Nat} (a b : Quotient (regionSetoid.{u, v, w} Φ 1 n)) :
    (((iterSSAIso.{u, v, w} Φ).inv : Inst.CoHom _ _).ρ.app (Discrete.mk n)).sen
        (Sentence.eq a b) =
      Sentence.eq (quotEquiv a) (quotEquiv b) := rfl

/-- On sentences, the isomorphism is `quotEquiv.symm` applied to both sides. -/
theorem iterSSAIso_hom_sen {n : Nat} (a b : Quotient (termSetoid.{u, v, w} Φ n)) :
    (((iterSSAIso.{u, v, w} Φ).hom : Inst.CoHom _ _).ρ.app (Discrete.mk n)).sen
        (Sentence.eq a b) =
      Sentence.eq (quotEquiv.symm a) (quotEquiv.symm b) := rfl

end Silmaril.Isotope.Institution.Observational
