module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.SExp.Defs
public import Silmaril.Logic.Arithmetic.SExp.Thms
public import Silmaril.Logic.Concrete.SExp.Thms
public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Thms

/-!
# Proofs for PA proofs as S-expressions: the judgment reader inverts the encoder
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation.SExp

open Silmaril.Consequence.Arithmetic.ND Silmaril.Logic.Arithmetic Silmaril.Logic.Arithmetic.SExp
open Silmaril.Logic.Concrete.SExp (num?_num)

theorem readFormulas_map (n : ℕ) :
    ∀ Γ : Context n, readFormulas n (Γ.map encodeFormula) = some Γ
  | [] => rfl
  | φ :: Γ => by simp [readFormulas, decodeFormula_eq_some_iff.2 rfl, readFormulas_map n Γ]

theorem readSeq_encode (s : Seq) : readSeq (encodeSeq s) = some s := by
  obtain ⟨n, Γ, φ⟩ := s
  simp [encodeSeq, readSeq, num?_num, readFormulas_map, decodeFormula_eq_some_iff.2 rfl]

open Silmaril.Consequence
open Silmaril.Logic.Smt (SE)

theorem checkRawTree_sound {T : Theory} {raw : ProofTree SE Seq} {s : Seq}
    (h : (match raw.elaborate elabRule with
      | none => .error Rejection.elaboration
      | some t => if (system T).check [] t then .ok t.concl else .error .check :
        Except Rejection Seq) = .ok s) : s.Derivable T := by
  split at h
  · cases h
  · split at h
    · cases h; exact derives_of_check T (by assumption)
    · cases h

theorem checkRawLines_sound {T : Theory} {raw : List (Line SE Seq)} {s : Seq}
    (h : (match raw.getLast? with
      | none => .error Rejection.empty
      | some last =>
        match Line.elaborate elabRule [] raw with
        | none => .error .elaboration
        | some ls => if (system T).checkLines [] [] ls then .ok last.concl else .error .check :
        Except Rejection Seq) = .ok s) : s.Derivable T := by
  split at h
  · cases h
  · next last hlast =>
    split at h
    · cases h
    · next ls he =>
      split at h
      · cases h
        exact (tree_iff T _).1 (DerivationSystem.derives_of_elaborateLines he
          (by assumption) (by rw [hlast]; rfl))
      · cases h

end Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation.SExp
