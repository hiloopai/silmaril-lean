module

public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Defs
public import Silmaril.Logic.Concrete.SExp.Thms

/-! Proofs for `Silmaril.Logic.Institution.Examples.Unsorted.SExp.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Institution.Examples.UFOL.SExp

open Silmaril.Logic.Institution.Examples.UFOL Silmaril.Logic.Institution.Examples.UFOL.SExp
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete.SExp (num num? num?_num)

variable {opArity relArity : String → Option ℕ}

theorem readTerms?_ofFn {k : ℕ} : {n : ℕ} → (f : Fin n → Term (named opArity relArity) k) →
    (∀ j, readTerm? opArity relArity k (encodeTerm (f j)) = some (f j)) →
    readTerms? opArity relArity k (List.ofFn fun j => encodeTerm (f j)) = some (List.ofFn f)
  | 0, _, _ => by simp [readTerms?]
  | n + 1, f, h => by
    simp only [List.ofFn_succ, readTerms?, h 0]
    simp [readTerms?_ofFn (fun j => f j.succ) (fun j => h j.succ)]

theorem readTerm?_encode {k : ℕ} : (t : Term (named opArity relArity) k) →
    readTerm? opArity relArity k (encodeTerm t) = some t
  | .var i => by simp [encodeTerm, readTerm?, num?_num, i.isLt]
  | .app (n := n) o args => by
    have hr := readTerms?_ofFn args (fun j => readTerm?_encode (args j))
    obtain ⟨f, hf⟩ := o
    simp only [encodeTerm]
    rw [readTerm?]
    split
    · rename_i n' h'
      rw [hf] at h'; cases h'
      simp [hr]
    · rename_i h'; rw [hf] at h'; cases h'

theorem readFormula?_encode : {k : ℕ} → (φ : Formula (named opArity relArity) k) →
    readFormula? opArity relArity k (encodeFormula φ) = some φ
  | _, .eq t u => by simp [encodeFormula, readFormula?, readTerm?_encode]
  | _, .rel (n := n) r args => by
    have hr := readTerms?_ofFn args (fun j => readTerm?_encode (args j))
    obtain ⟨f, hf⟩ := r
    simp only [encodeFormula]
    rw [readFormula?]
    split
    · rename_i n' h'
      rw [hf] at h'; cases h'
      simp [hr]
    · rename_i h'; rw [hf] at h'; cases h'
  | _, .tt => by simp [encodeFormula, readFormula?]
  | _, .not φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | _, .and φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | _, .all φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]

theorem decodeFormula_eq_some_iff {k : ℕ} {e : SE} {φ : Formula (named opArity relArity) k} :
    decodeFormula opArity relArity k e = some φ ↔ encodeFormula φ = e := by
  constructor
  · intro h
    simp only [decodeFormula, Option.bind_eq_some_iff] at h
    obtain ⟨φ', -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  · rintro rfl; simp [decodeFormula, readFormula?_encode]

end Silmaril.Proofs.Logic.Institution.Examples.UFOL.SExp
