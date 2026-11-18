module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.SExp.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Thms
public import Silmaril.Logic.Concrete.SExp.Thms
public import Silmaril.Logic.Consequence.Derivation.Thms

/-!
# Proofs for first-order proofs as S-expressions: the judgment reader inverts the encoder
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.FirstOrder.DerivationSExp

open Silmaril.Consequence.FirstOrder.ND Silmaril.Logic.Institution.Examples.UFOL
open Silmaril.Logic.Institution.Examples.UFOL.SExp
open Silmaril.Logic.Concrete.SExp (num?_num)

variable {opArity relArity : String → Option ℕ}

theorem readFormulas_map (k : ℕ) :
    ∀ Γ : List (Formula (named opArity relArity) k),
      readFormulas opArity relArity k (Γ.map encodeFormula) = some Γ
  | [] => rfl
  | φ :: Γ => by simp [readFormulas, decodeFormula_eq_some_iff.2 rfl, readFormulas_map k Γ]

theorem readSeq_encode (s : Seq (named opArity relArity)) :
    readSeq opArity relArity (encodeSeq s) = some s := by
  obtain ⟨k, Γ, φ⟩ := s
  simp [encodeSeq, readSeq, num?_num, readFormulas_map, decodeFormula_eq_some_iff.2 rfl]

open Silmaril.Consequence
open Silmaril.Logic.Smt (SE)

theorem checkRawTree_sound {raw : ProofTree SE (Seq (named opArity relArity))}
    {s : Seq (named opArity relArity)} (h : checkRawTree opArity relArity raw = .ok s) :
    (system (named opArity relArity)).derives [] s := by
  unfold checkRawTree at h; split at h
  · cases h
  · split at h
    · cases h; exact DerivationSystem.derives_of_check (by assumption)
    · cases h

theorem checkRawLines_sound {raw : List (Line SE (Seq (named opArity relArity)))}
    {s : Seq (named opArity relArity)} (h : checkRawLines opArity relArity raw = .ok s) :
    (system (named opArity relArity)).derives [] s := by
  unfold checkRawLines at h; split at h
  · cases h
  · next last hlast =>
    split at h
    · cases h
    · next ls he =>
      split at h
      · cases h
        exact DerivationSystem.derives_of_elaborateLines he (by assumption) (by rw [hlast]; rfl)
      · cases h

end Silmaril.Proofs.Logic.Consequence.FirstOrder.DerivationSExp
