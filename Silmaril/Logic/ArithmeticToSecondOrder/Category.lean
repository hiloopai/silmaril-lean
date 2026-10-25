module

public import Silmaril.Logic.ArithmeticToSecondOrder.Compiler
public import Silmaril.Logic.ArithmeticToSecondOrder.Decode
public import Silmaril.Logic.Metatheory.ArithmeticSystems.Arithmetic
public import Silmaril.Logic.SecondOrderArithmetic.Category

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open CategoryTheory Metatheory Metatheory.ArithmeticSystems

/-- Closed target conclusions retain the target's existing finite proof trees. -/
def closedInference (S : SecondOrderArithmetic.Subsystem) : InferenceSystemCat where
  Conclusion := {p : SecondOrderArithmetic.Formula ℕ // p.Closed}
  Derivation p := SecondOrderArithmetic.Proof S p.val

/-- The canonical PA-to-full-SOA arrow carries the actual compiler. -/
def paToSOAInference : paInference ⟶ closedInference .Z2Full where
  map p := ⟨sentence p, sentence_closed p⟩
  mapDerivation := paToSOA

/-- Inclusion in the named SOA category forgets only the closedness certificate. -/
def closedInclusion (S : SecondOrderArithmetic.Subsystem) :
    closedInference S ⟶ SecondOrderArithmetic.systemCat ℕ S where
  map p := p.val
  mapDerivation d := d

def paToNamedSOA : paInference ⟶ SecondOrderArithmetic.systemCat ℕ .Z2Full :=
  paToSOAInference ≫ closedInclusion .Z2Full

/-- Full SOA as an arithmetic-capable system with a faithful Q interpretation. -/
def secondOrder : System qInference where
  inference := closedInference .Z2Full
  base := qToPAInference ≫ paToSOAInference
  faithfulSyntax := by
    intro p q h
    apply sentence_injective
    exact congrArg Subtype.val h

/-- PA-to-SOA commutes with the Q interpretation on both syntax and proof data. -/
def peanoToSecondOrder : peano ⟶ secondOrder where
  inference := paToSOAInference
  commutes := rfl

def robinsonToSecondOrder : robinson ⟶ secondOrder := System.fromBase secondOrder

@[simp] theorem forget_peanoToSecondOrder :
    System.forget.map peanoToSecondOrder = paToSOAInference := rfl

@[simp] theorem peanoToSecondOrder_map (p : Arithmetic.Sentence) :
    (peanoToSecondOrder.inference.map p).val = sentence p := rfl

@[simp] theorem peanoToSecondOrder_proof (p : Arithmetic.Sentence) (d : Arithmetic.PAProof [] p) :
    peanoToSecondOrder.inference.mapDerivation d = paToSOA d := rfl

theorem robinsonToSecondOrder_factor :
    robinsonToPeano ≫ peanoToSecondOrder = robinsonToSecondOrder := rfl

theorem peano_arithmetic_extension_soa : System.ArithmeticExtension peano secondOrder :=
  System.arithmeticExtension_of_hom peanoToSecondOrder

theorem secondOrder_provesInduction : ProvesInduction secondOrder :=
  ProvesInduction.transport peanoToSecondOrder peano_provesInduction

end Silmaril.Logic.ArithmeticToSecondOrder
