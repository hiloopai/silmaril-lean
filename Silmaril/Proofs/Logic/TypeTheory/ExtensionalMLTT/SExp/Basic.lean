module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Defs
public import Silmaril.Logic.Concrete.SExp.Thms
public import Silmaril.Logic.Smt.SExpr.Reader.Thms

/-! Proofs for `Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms`: decoding inverts encoding,
legality of the printed atoms is exactly legality of the names, and the byte round trip. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp

open Silmaril.Logic.TypeTheory.ExtensionalMLTT Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp
open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (LegalAtom LegalChar LegalExpr render read_render readForms_legal)
open Silmaril.Logic.Concrete.SExp (num num? num?_num legal_num)

/-! ## Decoding inverts encoding -/

theorem readTm?_encodeTm : {k : ℕ} → (t : ETm k) → readTm? k (encodeTm t) = some t
  | _, .fv x => by simp [encodeTm, readTm?]
  | _, .bv i => by simp [encodeTm, readTm?, num?_num, i.isLt]
  | _, .univ n => by simp [encodeTm, readTm?, num?_num]
  | _, .empty => by simp [encodeTm, readTm?]
  | _, .unit => by simp [encodeTm, readTm?]
  | _, .star => by simp [encodeTm, readTm?]
  | _, .nats => by simp [encodeTm, readTm?]
  | _, .zero => by simp [encodeTm, readTm?]
  | _, .succ n => by simp [encodeTm, readTm?, readTm?_encodeTm n]
  | _, .natrec C s z n => by
      simp [encodeTm, readTm?, readTm?_encodeTm C, readTm?_encodeTm s, readTm?_encodeTm z,
        readTm?_encodeTm n]
  | _, .pi A B => by simp [encodeTm, readTm?, readTm?_encodeTm A, readTm?_encodeTm B]
  | _, .sigma A B => by simp [encodeTm, readTm?, readTm?_encodeTm A, readTm?_encodeTm B]
  | _, .abs A b => by simp [encodeTm, readTm?, readTm?_encodeTm A, readTm?_encodeTm b]
  | _, .app f a => by simp [encodeTm, readTm?, readTm?_encodeTm f, readTm?_encodeTm a]
  | _, .pair a b => by simp [encodeTm, readTm?, readTm?_encodeTm a, readTm?_encodeTm b]
  | _, .fst p => by simp [encodeTm, readTm?, readTm?_encodeTm p]
  | _, .snd p => by simp [encodeTm, readTm?, readTm?_encodeTm p]
  | _, .id A a b => by
      simp [encodeTm, readTm?, readTm?_encodeTm A, readTm?_encodeTm a, readTm?_encodeTm b]
  | _, .refl a => by simp [encodeTm, readTm?, readTm?_encodeTm a]
  | _, .absurd C e => by simp [encodeTm, readTm?, readTm?_encodeTm C, readTm?_encodeTm e]

theorem ctxOfDecls_ctxDecls : (Γ : ECtx) → ctxOfDecls (ctxDecls Γ) = Γ
  | .nil => rfl
  | .cons Γ x A => by
      simp only [ctxDecls, ctxOfDecls, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rw [show List.foldl (fun Γ d => ECtx.cons Γ d.1 d.2) ECtx.nil (ctxDecls Γ) = Γ from
        ctxOfDecls_ctxDecls Γ]

theorem readDecls?_encode : (ds : List (String × ETm 0)) →
    readDecls? (ds.map fun d => .list [.atom d.1, encodeTm d.2]) = some ds
  | [] => rfl
  | (x, A) :: ds => by simp [readDecls?, readTm?_encodeTm, readDecls?_encode ds]

theorem readCtx?_encodeCtx (Γ : ECtx) : readCtx? (encodeCtx Γ) = some Γ := by
  simp [encodeCtx, readCtx?, readDecls?_encode, ctxOfDecls_ctxDecls]

theorem readJdg?_encodeJdg (J : EJdg) : readJdg? (encodeJdg J) = some J := by
  simp [encodeJdg, readJdg?, readCtx?_encodeCtx, readTm?_encodeTm]

theorem decodeJdg_encodeJdg (J : EJdg) : decodeJdg (encodeJdg J) = some J := by
  simp [decodeJdg, readJdg?_encodeJdg]

theorem decodeJdg_eq_some_iff {e : SE} {J : EJdg} : decodeJdg e = some J ↔ encodeJdg J = e := by
  constructor
  · intro h
    simp only [decodeJdg, Option.bind_eq_some_iff] at h
    obtain ⟨J', -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  · rintro rfl; exact decodeJdg_encodeJdg J

/-! ## Legality: the printed atoms are legal exactly when the names are -/

theorem kw {s : String} (h : LegalAtom s) : LegalExpr (.atom s) := .atom h

theorem children {es : List SE} (h : LegalExpr (.list es)) : ∀ e ∈ es, LegalExpr e := by
  cases h; assumption

theorem atom_legal {s : String} (h : LegalExpr (.atom s)) : LegalAtom s := by cases h; assumption

/-- Split `∀ e ∈ [a, b, …], LegalExpr e` into one goal per element and close the keyword and
numeral goals. -/
macro "legal_list" : tactic => `(tactic| (
  refine .list ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals try first | exact legal_num _ | (apply kw; simp [LegalAtom, LegalChar]; done)))

theorem legal_encodeTm : {k : ℕ} → (t : ETm k) → (∀ x ∈ names t, LegalAtom x) →
    LegalExpr (encodeTm t)
  | _, .fv x, h => by legal_list; exact kw (h x (by simp [names]))
  | _, .bv _, _ => by legal_list
  | _, .univ _, _ => by legal_list
  | _, .empty, _ => kw (by simp [LegalAtom, LegalChar])
  | _, .unit, _ => kw (by simp [LegalAtom, LegalChar])
  | _, .star, _ => kw (by simp [LegalAtom, LegalChar])
  | _, .nats, _ => kw (by simp [LegalAtom, LegalChar])
  | _, .zero, _ => kw (by simp [LegalAtom, LegalChar])
  | _, .succ n, h => by legal_list; exact legal_encodeTm n h
  | _, .natrec C s z n, h => by
      legal_list
      · exact legal_encodeTm C fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm s fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm z fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm n fun x hx => h x (by simp [names, hx])
  | _, .pi A B, h | _, .sigma A B, h | _, .abs A B, h => by
      legal_list
      · exact legal_encodeTm A fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm B fun x hx => h x (by simp [names, hx])
  | _, .app A B, h | _, .pair A B, h | _, .absurd A B, h => by
      legal_list
      · exact legal_encodeTm A fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm B fun x hx => h x (by simp [names, hx])
  | _, .fst p, h | _, .snd p, h | _, .refl p, h => by legal_list; exact legal_encodeTm p h
  | _, .id A a b, h => by
      legal_list
      · exact legal_encodeTm A fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm a fun x hx => h x (by simp [names, hx])
      · exact legal_encodeTm b fun x hx => h x (by simp [names, hx])

/-- The legal names of a term, read back from a legal concrete form. -/
theorem names_legal : {k : ℕ} → (t : ETm k) → LegalExpr (encodeTm t) → ∀ x ∈ names t, LegalAtom x
  | _, .fv x, h, y, hy => by
      simp only [names, List.mem_singleton] at hy; subst hy
      exact atom_legal (children h _ (by simp))
  | _, .bv _, _, _, hy | _, .univ _, _, _, hy | _, .empty, _, _, hy | _, .unit, _, _, hy
  | _, .star, _, _, hy | _, .nats, _, _, hy | _, .zero, _, _, hy => by simp [names] at hy
  | _, .succ n, h, y, hy | _, .fst n, h, y, hy | _, .snd n, h, y, hy | _, .refl n, h, y, hy =>
      names_legal n (children h _ (by simp)) y hy
  | _, .natrec C s z n, h, y, hy => by
      simp only [names, List.mem_append] at hy
      rcases hy with ((hy | hy) | hy) | hy
      · exact names_legal C (children h _ (by simp)) y hy
      · exact names_legal s (children h _ (by simp)) y hy
      · exact names_legal z (children h _ (by simp)) y hy
      · exact names_legal n (children h _ (by simp)) y hy
  | _, .pi A B, h, y, hy | _, .sigma A B, h, y, hy | _, .abs A B, h, y, hy
  | _, .app A B, h, y, hy | _, .pair A B, h, y, hy | _, .absurd A B, h, y, hy => by
      simp only [names, List.mem_append] at hy
      rcases hy with hy | hy
      · exact names_legal A (children h _ (by simp)) y hy
      · exact names_legal B (children h _ (by simp)) y hy
  | _, .id A a b, h, y, hy => by
      simp only [names, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact names_legal A (children h _ (by simp)) y hy
      · exact names_legal a (children h _ (by simp)) y hy
      · exact names_legal b (children h _ (by simp)) y hy

theorem legal_encodeCtx (Γ : ECtx)
    (h : ∀ x ∈ (ctxDecls Γ).flatMap (fun d => d.1 :: names d.2), LegalAtom x) :
    LegalExpr (encodeCtx Γ) := by
  refine .list ?_
  simp only [List.mem_cons, List.mem_map]
  rintro e (rfl | ⟨d, hd, rfl⟩)
  · exact kw (by simp [LegalAtom, LegalChar])
  · refine .list ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨kw (h d.1 (List.mem_flatMap.2 ⟨d, hd, by simp⟩)),
      legal_encodeTm d.2 fun x hx => h x (List.mem_flatMap.2 ⟨d, hd, by simp [hx]⟩)⟩

theorem ctx_names_legal (Γ : ECtx) (h : LegalExpr (encodeCtx Γ)) :
    ∀ x ∈ (ctxDecls Γ).flatMap (fun d => d.1 :: names d.2), LegalAtom x := by
  intro x hx
  obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
  have hd' := children h _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hd))
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact atom_legal (children hd' _ (by simp))
  · exact names_legal d.2 (children hd' _ (by simp)) x hx

/-- **Legal names, exactly**: a judgment's concrete form is legal for the reader iff its names
are legal atoms. -/
theorem legal_encodeJdg_iff (J : EJdg) : LegalExpr (encodeJdg J) ↔ LegalNames J := by
  constructor
  · intro h x hx
    simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact ctx_names_legal J.Γ (children h _ (by simp)) x hx
    · exact names_legal J.A (children h _ (by simp)) x hx
    · exact names_legal J.a (children h _ (by simp)) x hx
    · exact names_legal J.b (children h _ (by simp)) x hx
  · intro h
    refine .list ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨kw (by simp [LegalAtom, LegalChar]),
      legal_encodeCtx J.Γ fun x hx => h x (by simp [hx]),
      legal_encodeTm J.A fun x hx => h x (by simp [hx]),
      legal_encodeTm J.a fun x hx => h x (by simp [hx]),
      legal_encodeTm J.b fun x hx => h x (by simp [hx])⟩

/-! ## Bytes -/

theorem parseJdg_printJdg (J : EJdg) (h : LegalNames J) : parseJdg (printJdg J) = some J := by
  simp [parseJdg, printJdg, read_render _ ((legal_encodeJdg_iff J).2 h), decodeJdg_encodeJdg]

theorem legalNames_of_parseJdg {bytes : List UInt8} {J : EJdg} (h : parseJdg bytes = some J) :
    LegalNames J := by
  unfold parseJdg at h
  split at h
  · rename_i e he
    rw [decodeJdg_eq_some_iff] at h
    subst h
    exact (legal_encodeJdg_iff J).1 (readForms_legal _ _ he _ (List.mem_singleton_self _))
  · cases h

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp
