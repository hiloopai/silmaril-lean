module

public import Silmaril.Logic.Arithmetic.SExp.Defs
public import Silmaril.Logic.Concrete.SExp.Thms

/-! Proofs for `Silmaril.Logic.Arithmetic.SExp.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Arithmetic.SExp

open Silmaril.Logic.Arithmetic Silmaril.Logic.Arithmetic.SExp
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Smt.SExpr.Writer (LegalAtom LegalChar LegalExpr)
open Silmaril.Logic.Concrete.SExp (num num? num?_num legal_num)

theorem readTerm?_encode : {n : ℕ} → (t : Term n) → readTerm? n (encodeTerm t) = some t
  | _, .var i => by simp [encodeTerm, readTerm?, num?_num, i.isLt]
  | _, .zero => by simp [encodeTerm, readTerm?]
  | _, .succ t => by simp [encodeTerm, readTerm?, readTerm?_encode t]
  | _, .add s t => by simp [encodeTerm, readTerm?, readTerm?_encode s, readTerm?_encode t]
  | _, .mul s t => by simp [encodeTerm, readTerm?, readTerm?_encode s, readTerm?_encode t]

theorem readFormula?_encode : {n : ℕ} → (φ : Formula n) → readFormula? n (encodeFormula φ) = some φ
  | _, .bot => by simp [encodeFormula, readFormula?]
  | _, .equal s t => by simp [encodeFormula, readFormula?, readTerm?_encode]
  | _, .imp φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | _, .conj φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | _, .disj φ ψ => by simp [encodeFormula, readFormula?, readFormula?_encode φ, readFormula?_encode ψ]
  | _, .all φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]
  | _, .ex φ => by simp [encodeFormula, readFormula?, readFormula?_encode φ]

theorem decodeFormula_eq_some_iff {n : ℕ} {e : SE} {φ : Formula n} :
    decodeFormula n e = some φ ↔ encodeFormula φ = e := by
  constructor
  · intro h
    simp only [decodeFormula, Option.bind_eq_some_iff] at h
    obtain ⟨φ', -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  · rintro rfl; simp [decodeFormula, readFormula?_encode]

theorem kw {s : String} (h : LegalAtom s) : LegalExpr (.atom s) := .atom h

macro "legal_list" : tactic => `(tactic| (
  try simp only [encodeTerm, encodeFormula]
  refine .list ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals try first | exact legal_num _ | (apply kw; simp [LegalAtom, LegalChar]; done)))

theorem legal_encodeTerm : {n : ℕ} → (t : Term n) → LegalExpr (encodeTerm t)
  | _, .var _ => by legal_list
  | _, .zero => by simp only [encodeTerm]; exact kw (by simp [LegalAtom, LegalChar])
  | _, .succ t => by legal_list; exact legal_encodeTerm t
  | _, .add s t | _, .mul s t => by legal_list <;> first | exact legal_encodeTerm s | exact legal_encodeTerm t

theorem legal_encodeFormula : {n : ℕ} → (φ : Formula n) → LegalExpr (encodeFormula φ)
  | _, .bot => by simp only [encodeFormula]; exact kw (by simp [LegalAtom, LegalChar])
  | _, .equal s t => by legal_list <;> first | exact legal_encodeTerm s | exact legal_encodeTerm t
  | _, .imp φ ψ | _, .conj φ ψ | _, .disj φ ψ => by
      legal_list <;> first | exact legal_encodeFormula φ | exact legal_encodeFormula ψ
  | _, .all φ | _, .ex φ => by legal_list; exact legal_encodeFormula φ

end Silmaril.Proofs.Logic.Arithmetic.SExp
