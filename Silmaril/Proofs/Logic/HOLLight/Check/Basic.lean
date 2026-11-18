module

public import Silmaril.Logic.HOLLight.Check.Defs

/-! Proofs for `Silmaril.Logic.HOLLight.Check.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.HOLLight.Check

open Silmaril.Logic.HOLLight

mutual
theorem wf?_iff (ops : List Nat) : (A : Ty) → (A.wf? ops = true ↔ A.WellFormed ops)
  | .var _ => by simp [Ty.wf?, Ty.WellFormed]
  | .bool => by simp [Ty.wf?, Ty.WellFormed]
  | .ind => by simp [Ty.wf?, Ty.WellFormed]
  | .arr A B => by simp [Ty.wf?, Ty.WellFormed, wf?_iff ops A, wf?_iff ops B]
  | .app c args => by
    simp only [Ty.wf?, Ty.WellFormed, Bool.and_eq_true, beq_iff_eq, wfList?_iff ops args]
theorem wfList?_iff (ops : List Nat) : (args : List Ty) → (Ty.wfList? ops args = true ↔ Ty.WellFormedList ops args)
  | [] => by simp [Ty.wfList?, Ty.WellFormedList]
  | A :: args => by simp only [Ty.wfList?, Ty.WellFormedList, Bool.and_eq_true, wf?_iff ops A, wfList?_iff ops args]
end

mutual
theorem scoped?_iff (n : Nat) : (A : Ty) → (A.scoped? n = true ↔ A.Scoped n)
  | .var _ => by simp [Ty.scoped?, Ty.Scoped]
  | .bool => by simp [Ty.scoped?, Ty.Scoped]
  | .ind => by simp [Ty.scoped?, Ty.Scoped]
  | .arr A B => by simp [Ty.scoped?, Ty.Scoped, scoped?_iff n A, scoped?_iff n B]
  | .app c args => by simp only [Ty.scoped?, Ty.Scoped, scopedList?_iff n args]
theorem scopedList?_iff (n : Nat) : (args : List Ty) → (Ty.scopedList? n args = true ↔ Ty.ScopedList n args)
  | [] => by simp [Ty.scopedList?, Ty.ScopedList]
  | A :: args => by simp only [Ty.scopedList?, Ty.ScopedList, Bool.and_eq_true, scoped?_iff n A, scopedList?_iff n args]
end

theorem const_typeOf?_eq_some_iff (sig : Signature) (c : Const) (A : Ty) :
    c.typeOf? sig = some A ↔ c.HasType sig A := by
  constructor
  · intro h
    cases c with
    | eq B =>
      simp only [Const.typeOf?] at h
      split at h
      · cases h; exact .eq ((wf?_iff _ _).1 (by assumption))
      · cases h
    | select B =>
      simp only [Const.typeOf?] at h
      split at h
      · cases h; exact .select ((wf?_iff _ _).1 (by assumption))
      · cases h
    | user n As =>
      simp only [Const.typeOf?] at h
      split at h
      · rename_i s hs
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
          cases h
          exact .user hs ⟨(wf?_iff _ _).1 h1, (scoped?_iff _ _).1 h2⟩ h3
            (fun B hB => (wf?_iff _ _).1 (h4 B hB))
        · cases h
      · cases h
  · intro h
    cases h with
    | eq wf => simp [Const.typeOf?, (wf?_iff _ _).2 wf]
    | select wf => simp [Const.typeOf?, (wf?_iff _ _).2 wf]
    | @user c s As lookup scheme arity args =>
      have hc : (s.body.wf? sig.tyOps && s.body.scoped? s.arity && As.length == s.arity &&
          As.all (Ty.wf? sig.tyOps)) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        exact ⟨⟨⟨(wf?_iff _ _).2 scheme.1, (scoped?_iff _ _).2 scheme.2⟩, arity⟩,
          fun B hB => (wf?_iff _ _).2 (args B hB)⟩
      simp only [Const.typeOf?, lookup, hc, ite_true]

theorem typeOf?_sound (sig : Signature) : (t : Tm) → (Γ : List Ty) → (A : Ty) →
    t.typeOf? sig Γ = some A → HasType sig Γ t A
  | .bvar i, Γ, A, h => by
    simp only [Tm.typeOf?, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    split at h
    · cases h; exact .bvar hB ((wf?_iff _ _).1 (by assumption))
    · cases h
  | .fvar n B, Γ, A, h => by
    simp only [Tm.typeOf?] at h
    split at h
    · cases h; exact .fvar n ((wf?_iff _ _).1 (by assumption))
    · cases h
  | .const c, Γ, A, h => .const ((const_typeOf?_eq_some_iff sig c A).1 h)
  | .app f x, Γ, A, h => by
    simp only [Tm.typeOf?] at h
    split at h
    · rename_i B C B' hf hx
      split at h
      · rename_i e; subst e; cases h
        exact .app (typeOf?_sound sig f Γ _ hf) (typeOf?_sound sig x Γ _ hx)
      · cases h
    · cases h
  | .lam B b, Γ, A, h => by
    simp only [Tm.typeOf?] at h
    split at h
    · rename_i hB
      obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .lam ((wf?_iff _ _).1 hB) (typeOf?_sound sig b (B :: Γ) C hC)
    · cases h

theorem typeOf?_complete {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType sig Γ t A) :
    t.typeOf? sig Γ = some A := by
  induction h with
  | bvar lookup wf => simp [Tm.typeOf?, lookup, (wf?_iff _ _).2 wf]
  | fvar name wf => simp [Tm.typeOf?, (wf?_iff _ _).2 wf]
  | const typing => exact (const_typeOf?_eq_some_iff _ _ _).2 typing
  | app _ _ ihf ihx => simp [Tm.typeOf?, ihf, ihx]
  | lam wf _ ih => simp [Tm.typeOf?, (wf?_iff _ _).2 wf, ih]

end Silmaril.Proofs.Logic.HOLLight.Check
