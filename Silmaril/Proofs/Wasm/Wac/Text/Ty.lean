module

public import Silmaril.Proofs.Wasm.Wac.Text.Basic

/-!
# WAC text: types read back

`ty_pr`: the type parser reads a printed well-formed type back, when the next token is
not `<` and the fuel exceeds the printed length.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

theorem Pr.tys_eq : ∀ ts : List Ty, Pr.tys ts = commaList Pr.ty ts
  | [] => rfl
  | [_] => rfl
  | t :: u :: r => by rw [Pr.tys, Pr.tys_eq (u :: r)]; rfl

/-- A printed type starts with a keyword or an identifier, without docs. -/
theorem Pr.ty_cons (t : Ty) : ∃ x l, Pr.ty t = ⟨[], x⟩ :: l ∧ (∀ c, x ≠ .sym c) ∧
    x ≠ .kw .async ∧ x ≠ .kw .func := by
  cases t with
  | result o e => cases o <;> cases e <;> simp [Pr.ty]
  | stream o => cases o <;> simp [Pr.ty]
  | future o => cases o <;> simp [Pr.ty]
  | _ => simp [Pr.ty]

/-- A printed type does not start with `async` or `func`. -/
theorem isTok_ty_kw (t : Ty) (r : Toks) (k : Kw) (hk : k = .async ∨ k = .func) :
    isTok (.kw k) (Pr.ty t ++ r) = false := by
  apply isTok_of_ne
  obtain ⟨x, l, h, -, h1, h2⟩ := Pr.ty_cons t
  rcases hk with rfl | rfl <;> simp [h, h1, h2]

theorem Pr.ty_ne_nil (t : Ty) : Pr.ty t ≠ [] := by
  obtain ⟨x, l, h, -⟩ := Pr.ty_cons t; simp [h]

theorem hd?_ty_ne (t : Ty) (r : Toks) (c : Char) : hd? (Pr.ty t ++ r) ≠ some (.sym c) := by
  obtain ⟨x, l, h, hx, -⟩ := Pr.ty_cons t; simp [h, hx]

theorem isTok_ty (t : Ty) (r : Toks) (c : Char) : isTok (.sym c) (Pr.ty t ++ r) = false :=
  isTok_of_ne (hd?_ty_ne t r c)

theorem sym_ty (t : Ty) (r : Toks) (c : Char) : sym c (Pr.ty t ++ r) = none :=
  sym_of_ne (hd?_ty_ne t r c)

/-- The induction hypothesis of `ty_pr` at fuel `n`. -/
def TyIH (n : Nat) : Prop :=
  ∀ t rest, Wf.ty t = true → (Pr.ty t).length < n → hd? rest ≠ some (.sym '<') →
    Parse.ty n (Pr.ty t ++ rest) = some (t, rest)

theorem ty_angle {n : Nat} (ih : TyIH n) (t : Ty) (rest : Toks) (hw : Wf.ty t = true)
    (hl : (Pr.ty t).length < n) :
    angle (Parse.ty n) (sy '<' :: (Pr.ty t ++ sy '>' :: rest)) = some (t, rest) := by
  have h := ih t (sy '>' :: rest) hw hl (by simp)
  simp [angle, h]

theorem optTy_some {n : Nat} (ih : TyIH n) (t : Ty) (rest : Toks) (hw : Wf.ty t = true)
    (hl : (Pr.ty t).length < n) (hr : hd? rest ≠ some (.sym '<')) :
    optTy (Parse.ty n) (Pr.ty t ++ rest) = some (some t, rest) := by
  simp [optTy, isTok_ty, ih t rest hw hl hr]

theorem Wf.tys_iff : ∀ ts : List Ty, Wf.tys ts = true ↔ ∀ t ∈ ts, Wf.ty t = true
  | [] => by simp [Wf.tys]
  | t :: ts => by simp [Wf.tys, Wf.tys_iff ts]

theorem ty_tuple {n : Nat} (ih : TyIH n) (ts : List Ty) (rest : Toks)
    (hw : Wf.ty (.tuple ts) = true) (hl : (Pr.ty (.tuple ts)).length < n + 1) :
    Parse.ty (n + 1) (Pr.ty (.tuple ts) ++ rest) = some (.tuple ts, rest) := by
  have hne : ts ≠ [] := by intro h; simp [h, Wf.ty] at hw
  have hall : ∀ t ∈ ts, Wf.ty t = true := (Wf.tys_iff ts).mp (by simp [Wf.ty] at hw; exact hw.2)
  have hl' : (commaList Pr.ty ts).length + 3 ≤ n + 1 := by
    simp [Pr.ty, Pr.tys_eq] at hl; omega
  have hd : delim (Parse.ty n) '>' true n (commaList Pr.ty ts ++ sy '>' :: rest) =
      some (ts, sy '>' :: rest) :=
    delim_commaList _ Pr.ty '>' (by decide) ts n rest
      (fun t ht r hr => ih t r (hall t ht)
        (by have := length_le_commaList Pr.ty ts t ht; omega)
        (by rcases hr with h | h <;> simp [h]))
      (fun t _ => ⟨Pr.ty_ne_nil t, hd?_ty_ne t [] '>' |> fun h => by simpa using h⟩)
      (by have := length_le_commaList' Pr.ty Pr.ty_ne_nil ts; omega)
  obtain ⟨t, ts', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hi : isTok (.sym '>') (commaList Pr.ty (t :: ts') ++ sy '>' :: rest) = false :=
    isTok_of_ne (by rw [hd?_commaList _ _ _ _ (Pr.ty_ne_nil t)]; simpa using hd?_ty_ne t [] '>')
  simp only [Pr.ty, Pr.tys_eq, List.cons_append, List.append_assoc]
  simp [Parse.ty, primOf, hi, hd]

theorem ty_result_some {n : Nat} (ih : TyIH n) (o : Ty) (e : Option Ty) (rest : Toks)
    (hw : Wf.ty (.result (some o) e) = true) (hl : (Pr.ty (.result (some o) e)).length < n + 1) :
    Parse.ty (n + 1) (Pr.ty (.result (some o) e) ++ rest) = some (.result (some o) e, rest) := by
  have ho : Wf.ty o = true := by cases e <;> simp_all [Wf.ty]
  cases e with
  | none =>
    have hl' : (Pr.ty o).length < n := by simp [Pr.ty] at hl; omega
    simp [Pr.ty, Parse.ty, primOf, optTy, isTok_ty, ih o (sy '>' :: rest) ho hl' (by simp)]
  | some e =>
    have he : Wf.ty e = true := by simp_all [Wf.ty]
    have hl1 : (Pr.ty o).length < n := by simp [Pr.ty] at hl; omega
    have hl2 : (Pr.ty e).length < n := by simp [Pr.ty] at hl; omega
    simp [Pr.ty, Parse.ty, primOf, optTy, isTok_ty,
      ih o (sy ',' :: (Pr.ty e ++ sy '>' :: rest)) ho hl1 (by simp),
      ih e (sy '>' :: rest) he hl2 (by simp)]

theorem ty_result {n : Nat} (ih : TyIH n) (o e : Option Ty) (rest : Toks)
    (hw : Wf.ty (.result o e) = true) (hl : (Pr.ty (.result o e)).length < n + 1)
    (hr : hd? rest ≠ some (.sym '<')) :
    Parse.ty (n + 1) (Pr.ty (.result o e) ++ rest) = some (.result o e, rest) := by
  cases o with
  | none =>
    cases e with
    | none => simp [Pr.ty, Parse.ty, primOf, sym_of_ne hr]
    | some e =>
      have he : Wf.ty e = true := by simpa [Wf.ty] using hw
      have hl' : (Pr.ty e).length < n := by simp [Pr.ty] at hl; omega
      simp [Pr.ty, Parse.ty, primOf, optTy, isTok_ty, ih e (sy '>' :: rest) he hl' (by simp)]
  | some o => exact ty_result_some ih o e rest hw hl

theorem ty_pr : ∀ n, TyIH n
  | 0 => by intro _ _ _ hl _; exact absurd hl (Nat.not_lt_zero _)
  | n + 1 => by
    intro t rest hw hl hr
    have ih := ty_pr n
    cases t with
    | tuple ts => exact ty_tuple ih ts rest hw hl
    | result o e => exact ty_result ih o e rest hw hl hr
    | stream o | future o =>
      cases o with
      | none => simp [Pr.ty, Parse.ty, primOf, sym_of_ne hr]
      | some t =>
        have hl' : (Pr.ty t).length < n := by simp [Pr.ty] at hl; omega
        simp [Pr.ty, Parse.ty, primOf, ty_angle ih t rest (by simpa [Wf.ty] using hw) hl']
    | list t | option t =>
      have hl' : (Pr.ty t).length < n := by simp [Pr.ty] at hl; omega
      simp [Pr.ty, Parse.ty, primOf, ty_angle ih t rest (by simpa [Wf.ty] using hw) hl']
    | _ => simp [Pr.ty, Parse.ty, primOf, angle]

end Silmaril.Wasm.Wac.Text
