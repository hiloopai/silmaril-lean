module

public import Silmaril.Proofs.Wasm.Wac.Text.Func

/-!
# WAC text: type declarations read back
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

/-- The next token is `,` or the symbol `c`. -/
abbrev CommaOr (c : Char) (r : Toks) : Prop := hd? r = some (.sym ',') ∨ hd? r = some (.sym c)

theorem CommaOr.ne {c d : Char} {r : Toks} (h : CommaOr c r) (h1 : d ≠ ',') (h2 : d ≠ c) :
    hd? r ≠ some (.sym d) := by
  rcases h with h | h <;> rw [h] <;> simp [Ne.symm h1, Ne.symm h2]

theorem CommaOr.ne' {c : Char} {r : Toks} {t : Tok} (h : CommaOr c r)
    (h1 : t ≠ .sym ',') (h2 : t ≠ .sym c) : hd? r ≠ some t := by
  rcases h with h | h <;> rw [h] <;> simp [Ne.symm h1, Ne.symm h2]

/-- `{ items }` around a nonempty comma list. -/
theorem braced_pr {α : Type} (p : Toks → Option (α × Toks)) (f : α → Toks) (as : List α)
    (n : Nat) (rest : Toks) (hne : as ≠ [])
    (hd : delim p '}' true n (commaList f as ++ sy '}' :: rest) = some (as, sy '}' :: rest)) :
    braced p n (sy '{' :: (commaList f as ++ sy '}' :: rest)) = some (as, rest) := by
  simp [braced, hd, hne]

/-- A comma list in braces, each item read back. -/
theorem commaBraced {α : Type} (p : Toks → Option (α × Toks)) (f : α → Toks) (as : List α)
    (n : Nat) (rest : Toks) (hne : as ≠ [])
    (hp : ∀ a ∈ as, ∀ r, CommaOr '}' r → p (f a ++ r) = some (a, r))
    (hf : ∀ a, f a ≠ [] ∧ hd? (f a) ≠ some (.sym '}'))
    (hl : (commaList f as).length < n) :
    braced p n (sy '{' :: (commaList f as ++ sy '}' :: rest)) = some (as, rest) :=
  braced_pr p f as n rest hne
    (delim_commaList p f '}' (by decide) as n rest hp (fun a _ => hf a)
      (by have := length_le_commaList' f (fun a => (hf a).1) as; omega))

theorem variantCase_pr (n : Nat) (c : VariantCase) (r : Toks) (hr : CommaOr '}' r)
    (hw : (match c.ty with | some t => Wf.ty t | none => true) = true)
    (hl : (Pr.variantCase c).length < n) :
    Parse.variantCase n (Pr.variantCase c ++ r) = some (c, r) := by
  obtain ⟨ds, id, t⟩ := c
  cases t with
  | none => simp [Pr.variantCase, Parse.variantCase, docsOf, sym_of_ne (hr.ne (d := '(') (by decide) (by decide))]
  | some t =>
    have hl' : (Pr.ty t).length < n := by simp [Pr.variantCase] at hl; omega
    have := ty_pr n t (sy ')' :: r) hw hl' (by simp)
    simp [Pr.variantCase, Parse.variantCase, docsOf, this]

theorem field_pr (n : Nat) (f : Field) (r : Toks) (hr : CommaOr '}' r) (hw : Wf.ty f.ty = true)
    (hl : (Pr.field f).length < n) : Parse.field n (Pr.field f ++ r) = some (f, r) := by
  have hl' : (Pr.ty f.ty).length < n := by simp [Pr.field] at hl; omega
  have := ty_pr n f.ty r hw hl' (hr.ne (d := '<') (by decide) (by decide))
  simp [Pr.field, Parse.field, Parse.namedType, docsOf, this]

theorem case_pr (c : Case) (r : Toks) : Parse.case (Pr.case c ++ r) = some (c, r) := by
  simp [Pr.case, Parse.case, docsOf]

theorem variantCases_pr (n : Nat) (cs : List VariantCase) (rest : Toks) (hne : cs ≠ [])
    (hw : ∀ c ∈ cs, (match c.ty with | some t => Wf.ty t | none => true) = true)
    (hl : (commaList Pr.variantCase cs).length < n) :
    braced (Parse.variantCase n) n (sy '{' :: (commaList Pr.variantCase cs ++ sy '}' :: rest)) =
      some (cs, rest) :=
  commaBraced _ _ cs n rest hne
    (fun c hc r hr => variantCase_pr n c r hr (hw c hc)
      (by have := length_le_commaList Pr.variantCase cs c hc; omega))
    (fun c => by simp [Pr.variantCase]) hl

theorem fields_pr (n : Nat) (fs : List Field) (rest : Toks) (hne : fs ≠ [])
    (hw : ∀ f ∈ fs, Wf.ty f.ty = true) (hl : (commaList Pr.field fs).length < n) :
    braced (Parse.field n) n (sy '{' :: (commaList Pr.field fs ++ sy '}' :: rest)) =
      some (fs, rest) :=
  commaBraced _ _ fs n rest hne
    (fun f hf r hr => field_pr n f r hr (hw f hf)
      (by have := length_le_commaList Pr.field fs f hf; omega))
    (fun f => by simp [Pr.field]) hl

theorem cases_pr (n : Nat) (cs : List Case) (rest : Toks) (hne : cs ≠ [])
    (hl : (commaList Pr.case cs).length < n) :
    braced Parse.case n (sy '{' :: (commaList Pr.case cs ++ sy '}' :: rest)) = some (cs, rest) :=
  commaBraced _ _ cs n rest hne (fun c _ r _ => case_pr c r) (fun c => by simp [Pr.case]) hl

theorem alias_pr (n : Nat) (ds : Docs) (id : String) (k : AliasKind) (rest : Toks)
    (hw : (match k with | .func f => Wf.funcType f | .type t => Wf.ty t) = true)
    (hl : (Pr.typeDecl (.alias ds id k)).length < n) :
    Parse.typeDecl n (Pr.typeDecl (.alias ds id k) ++ rest) = some (.alias ds id k, rest) := by
  cases k with
  | func f =>
    have h := funcType_pr n f (sy ';' :: rest) hw (by simp [Pr.typeDecl] at hl; omega)
      (by simp) (by simp)
    obtain ⟨a, ps, r⟩ := f
    cases a <;> simp_all [Pr.typeDecl, Parse.typeDecl, Pr.funcType, docsOf, Pr.first]
  | type t =>
    have h := ty_pr n t (sy ';' :: rest) hw (by simp [Pr.typeDecl] at hl; omega) (by simp)
    simp [Pr.typeDecl, Parse.typeDecl, docsOf, Pr.first, isTok_ty_kw t _ .async (.inl rfl),
      isTok_ty_kw t _ .func (.inr rfl), h]

theorem typeDecl_pr (n : Nat) (d : TypeDecl) (rest : Toks) (hw : Wf.typeDecl d = true)
    (hl : (Pr.typeDecl d).length < n) :
    Parse.typeDecl n (Pr.typeDecl d ++ rest) = some (d, rest) := by
  cases d <;> simp only [Wf.typeDecl, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at hw
  case variant ds id cs =>
    have h := variantCases_pr n cs rest hw.1.2 (fun c hc => (hw.2 c hc).2)
      (by simp [Pr.typeDecl] at hl; omega)
    simp [Pr.typeDecl, Parse.typeDecl, docsOf, Pr.first, h]
  case record ds id fs =>
    have h := fields_pr n fs rest hw.1.2 (fun f hf => (hw.2 f hf).2)
      (by simp [Pr.typeDecl] at hl; omega)
    simp [Pr.typeDecl, Parse.typeDecl, docsOf, Pr.first, h]
  case flags ds id cs | enum ds id cs =>
    have h := cases_pr n cs rest hw.1.2 (by simp [Pr.typeDecl] at hl; omega)
    simp [Pr.typeDecl, Parse.typeDecl, docsOf, Pr.first, h]
  case alias ds id k => exact alias_pr n ds id k rest hw.2 hl

end Silmaril.Wasm.Wac.Text
