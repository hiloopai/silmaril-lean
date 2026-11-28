module

public import Silmaril.Logic.ManyValuedCatalogue.Defs
import Silmaril.Proofs.Logic.ManyValuedCatalogue.Chains

/-! Residuation and preservation laws for the many-valued chain examples. -/

public section

namespace Silmaril.Logic.ManyValuedCatalogue

namespace Goedel

variable {A : Type*} [LinearOrder A] [BoundedOrder A]

theorem residuation (x y z : A) : Goedel.and x y ≤ z ↔ y ≤ Goedel.imp x z :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Goedel.residuation x y z

theorem neg_eq (x : A) : Goedel.neg x = if x = ⊥ then ⊤ else ⊥ :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Goedel.neg_eq x

end Goedel

namespace UnitInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem luk_residuation (x y z : UnitInterval K) : lukAnd x y ≤ z ↔ y ≤ lukImp x z :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.luk_residuation x y z

theorem luk_neg_eq (x : UnitInterval K) : lukImp x ⊥ = lukNeg x :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.luk_neg_eq x

theorem prod_residuation (x y z : UnitInterval K) : prodAnd x y ≤ z ↔ y ≤ prodImp x z :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.prod_residuation x y z

theorem prod_neg_eq (x : UnitInterval K) : prodNeg x = Goedel.neg x :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.prod_neg_eq x

theorem prod_meet_eq (x y : UnitInterval K) : prodMeet x y = min x y :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.prod_meet_eq x y

theorem ofGrid_le_iff {n : ℕ} {x y : Grid n} :
    (ofGrid x : UnitInterval K) ≤ ofGrid y ↔ x ≤ y :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_le_iff

theorem ofGrid_bot (n : ℕ) : (ofGrid (⊥ : Grid n) : UnitInterval K) = ⊥ :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_bot n

theorem ofGrid_top (n : ℕ) : (ofGrid (⊤ : Grid n) : UnitInterval K) = ⊤ :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_top n

theorem ofGrid_and {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.and x y) : UnitInterval K) = Goedel.and (ofGrid x) (ofGrid y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_and x y

theorem ofGrid_or {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.or x y) : UnitInterval K) = Goedel.or (ofGrid x) (ofGrid y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_or x y

theorem ofGrid_goedelImp {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.imp x y) : UnitInterval K) = Goedel.imp (ofGrid x) (ofGrid y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_goedelImp x y

theorem ofGrid_goedelNeg {n : ℕ} (x : Grid n) :
    (ofGrid (Goedel.neg x) : UnitInterval K) = Goedel.neg (ofGrid x) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_goedelNeg x

theorem ofGrid_lukNeg {n : ℕ} (x : Grid n) :
    (ofGrid (Grid.lukNeg x) : UnitInterval K) = lukNeg (ofGrid x) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_lukNeg x

theorem ofGrid_lukImp {n : ℕ} (x y : Grid n) :
    (ofGrid (Grid.lukImp x y) : UnitInterval K) = lukImp (ofGrid x) (ofGrid y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_lukImp x y

theorem ofGrid_lukAnd {n : ℕ} (x y : Grid n) :
    (ofGrid (Grid.lukAnd x y) : UnitInterval K) = lukAnd (ofGrid x) (ofGrid y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofGrid_lukAnd x y

theorem ofRat_le_iff {x y : UnitInterval ℚ} : ofRat x ≤ ofRat y ↔ x ≤ y :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_le_iff

theorem ofRat_top : ofRat (⊤ : UnitInterval ℚ) = ⊤ :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_top

theorem ofRat_bot : ofRat (⊥ : UnitInterval ℚ) = ⊥ :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_bot

theorem ofRat_lukNeg (x : UnitInterval ℚ) : ofRat (lukNeg x) = lukNeg (ofRat x) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_lukNeg x

theorem ofRat_lukImp (x y : UnitInterval ℚ) :
    ofRat (lukImp x y) = lukImp (ofRat x) (ofRat y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_lukImp x y

theorem ofRat_lukAnd (x y : UnitInterval ℚ) :
    ofRat (lukAnd x y) = lukAnd (ofRat x) (ofRat y) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.UnitInterval.ofRat_lukAnd x y

end UnitInterval

end Silmaril.Logic.ManyValuedCatalogue
