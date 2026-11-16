module

public import Silmaril.Logic.Concrete.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms
public import Std.Data.String.ToNat

/-! Proofs for `Silmaril.Logic.Concrete.SExp.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Concrete.SExp

open Silmaril.Logic.Concrete.SExp
open Silmaril.Logic.Smt.SExpr.Writer (LegalAtom LegalChar LegalExpr)

theorem num?_num (n : Nat) : num? (num n) = some n := by simp [num, num?]

theorem legal_num (n : Nat) : LegalExpr (num n) := by
  refine .atom ⟨by simp [Nat.toList_repr], fun c hc => ?_⟩
  rw [Nat.toList_repr] at hc
  have h := Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : 48 ≤ c.toNat := Nat.succ_le_of_lt h1
  have e2 : c.toNat ≤ 57 := Fin.mk_le_mk.mp h2
  unfold LegalChar; omega

end Silmaril.Proofs.Logic.Concrete.SExp
