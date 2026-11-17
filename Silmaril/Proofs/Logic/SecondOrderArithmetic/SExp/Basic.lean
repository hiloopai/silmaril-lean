module

public import Silmaril.Logic.SecondOrderArithmetic.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms

/-! Proofs for `Silmaril.Logic.SecondOrderArithmetic.SExp.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.SecondOrderArithmetic.SExp

open Silmaril.Logic.SecondOrderArithmetic Silmaril.Logic.SecondOrderArithmetic.SExp
open Silmaril.Logic.Smt (SE)

theorem readTerm?_encode : (t : Term String) → readTerm? (encodeTerm t) = some t
  | .var x => by simp [encodeTerm, readTerm?]
  | .zero => by simp [encodeTerm, readTerm?]
  | .succ t => by simp [encodeTerm, readTerm?, readTerm?_encode t]
  | .add t u => by simp [encodeTerm, readTerm?, readTerm?_encode t, readTerm?_encode u]
  | .mul t u => by simp [encodeTerm, readTerm?, readTerm?_encode t, readTerm?_encode u]

theorem readFormula?_encode : (φ : Formula String) → readFormula? (encodeFormula φ) = some φ
  | .equal t u => by simp [encodeFormula, readFormula?, readTerm?_encode]
  | .less t u => by simp [encodeFormula, readFormula?, readTerm?_encode]
  | .member t X => by simp [encodeFormula, readFormula?, readTerm?_encode]
  | .setEqual X Y => by simp [encodeFormula, readFormula?]
  | .neg φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | .imp φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | .iff φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | .conj φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | .all x φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | .ex x φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | .setAll X φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | .setEx X φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]

theorem decodeFormula_eq_some_iff {e : SE} {φ : Formula String} :
    decodeFormula e = some φ ↔ encodeFormula φ = e := by
  constructor
  · intro h
    simp only [decodeFormula, Option.bind_eq_some_iff] at h
    obtain ⟨φ', -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  · rintro rfl; simp [decodeFormula, readFormula?_encode]

end Silmaril.Proofs.Logic.SecondOrderArithmetic.SExp
