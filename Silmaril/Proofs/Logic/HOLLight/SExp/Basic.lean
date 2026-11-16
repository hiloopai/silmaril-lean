module

public import Silmaril.Logic.HOLLight.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms
public import Silmaril.Logic.Concrete.SExp.Thms

/-! Proofs for `Silmaril.Logic.HOLLight.SExp.Thms`: decoding inverts encoding, encoded atoms are
legal, and printing then parsing gives back the term. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.HOLLight.SExp

open Silmaril.Logic.HOLLight Silmaril.Logic.HOLLight.SExp
open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (LegalAtom LegalChar LegalExpr render read_render)
open Silmaril.Logic.Concrete.SExp (num num? num?_num legal_num)

mutual
theorem readTy?_encodeTy : (t : Ty) → readTy? (encodeTy t) = some t
  | .var n => by simp [encodeTy, readTy?, num?_num]
  | .bool => by simp [encodeTy, readTy?]
  | .ind => by simp [encodeTy, readTy?]
  | .arr a b => by simp [encodeTy, readTy?, readTy?_encodeTy a, readTy?_encodeTy b]
  | .app k as => by simp [encodeTy, readTy?, num?_num, readTys?_encodeTys as]
theorem readTys?_encodeTys : (ts : List Ty) → readTys? (encodeTys ts) = some ts
  | [] => by simp [encodeTys, readTys?]
  | a :: as => by simp [encodeTys, readTys?, readTy?_encodeTy a, readTys?_encodeTys as]
end

theorem readTm?_encodeTm : (t : Tm) → readTm? (encodeTm t) = some t
  | .bvar i => by simp [encodeTm, readTm?, num?_num]
  | .fvar n A => by simp [encodeTm, readTm?, num?_num, readTy?_encodeTy]
  | .const (.eq A) => by simp [encodeTm, readTm?, readTy?_encodeTy]
  | .const (.select A) => by simp [encodeTm, readTm?, readTy?_encodeTy]
  | .const (.user n As) => by simp [encodeTm, readTm?, num?_num, readTys?_encodeTys]
  | .app f x => by simp [encodeTm, readTm?, readTm?_encodeTm f, readTm?_encodeTm x]
  | .lam A b => by simp [encodeTm, readTm?, readTy?_encodeTy, readTm?_encodeTm b]

theorem decodeTy_encodeTy (t : Ty) : decodeTy (encodeTy t) = some t := by
  simp [decodeTy, readTy?_encodeTy]

theorem decodeTm_encodeTm (t : Tm) : decodeTm (encodeTm t) = some t := by
  simp [decodeTm, readTm?_encodeTm]

theorem decodeTm_eq_some_iff {e : SE} {t : Tm} : decodeTm e = some t ↔ encodeTm t = e := by
  constructor
  · intro h
    simp only [decodeTm, Option.bind_eq_some_iff] at h
    obtain ⟨t', -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  · rintro rfl; exact decodeTm_encodeTm t

theorem legal_kw {s : String} (h : LegalAtom s) : LegalExpr (.atom s) := .atom h

mutual
theorem legal_encodeTy : (t : Ty) → LegalExpr (encodeTy t)
  | .var n => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_num n)
  | .bool => legal_kw (by simp [LegalAtom, LegalChar])
  | .ind => legal_kw (by simp [LegalAtom, LegalChar])
  | .arr a b => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_encodeTy a
      · exact legal_encodeTy b)
  | .app k as => .list (by
      simp only [List.mem_cons]
      rintro e (rfl | rfl | h)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_num k
      · exact legal_encodeTys as e h)
theorem legal_encodeTys : (ts : List Ty) → ∀ e ∈ encodeTys ts, LegalExpr e
  | [] => by simp [encodeTys]
  | a :: as => by
      simp only [encodeTys, List.mem_cons]
      rintro e (rfl | h)
      · exact legal_encodeTy a
      · exact legal_encodeTys as e h
end

theorem legal_encodeTm : (t : Tm) → LegalExpr (encodeTm t)
  | .bvar i => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_num i)
  | .fvar n A => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_num n
      · exact legal_encodeTy A)
  | .const (.eq A) => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_encodeTy A)
  | .const (.select A) => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_encodeTy A)
  | .const (.user n As) => .list (by
      simp only [List.mem_cons]
      rintro e (rfl | rfl | h)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_num n
      · exact legal_encodeTys As e h)
  | .app f x => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_encodeTm f
      · exact legal_encodeTm x)
  | .lam A b => .list (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro e (rfl | rfl | rfl)
      · exact legal_kw (by simp [LegalAtom, LegalChar])
      · exact legal_encodeTy A
      · exact legal_encodeTm b)

theorem parseTm_printTm (t : Tm) : parseTm (printTm t) = some t := by
  simp [parseTm, printTm, read_render _ (legal_encodeTm t), decodeTm_encodeTm]

end Silmaril.Proofs.Logic.HOLLight.SExp
