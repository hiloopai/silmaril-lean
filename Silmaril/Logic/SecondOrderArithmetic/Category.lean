module

public import Silmaril.Logic.SecondOrderArithmetic.Systems
public import Silmaril.Logic.Metatheory.InferenceSystemCat

@[expose] public section

/-! Category objects retain independent syntax and finite proof trees. The
arithmetic-capable category's additional Q interpretation is a separate
obligation; none is inferred from standard-model truth. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open CategoryTheory Silmaril.Logic.Metatheory

variable (N : Type) [DecidableEq N]

def systemCat (S : Subsystem) : InferenceSystemCat.{0, 0} where
  Conclusion := Formula N
  Derivation := Proof S

def rcaWklArrow : systemCat N .RCA0 ⟶ systemCat N .WKL0Sep where
  map := id
  mapDerivation := Proof.rcaToWkl

def rcaACAArrow : systemCat N .RCA0 ⟶ systemCat N .ACA0 where
  map := id
  mapDerivation := Proof.rcaToACA

def acaZ2Arrow : systemCat N .ACA0 ⟶ systemCat N .Z2 where
  map := id
  mapDerivation := Proof.acaToZ2

/-- The two proof maps establish equal provability. A category isomorphism
would additionally require inverse maps on individual proof fibers. -/
theorem full_schema_derivability (φ : Formula N) :
    Nonempty ((systemCat N .Z2).Derivation φ) ↔
      Nonempty ((systemCat N .Z2Full).Derivation φ) := z2_iff_full φ

end Silmaril.Logic.SecondOrderArithmetic
