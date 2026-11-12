module

public import Silmaril.Proofs.Wasm.Wac.Text.Ty

/-!
# WAC text: named types and function types read back
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

theorem namedType_pr (n : Nat) (a : NamedType) (rest : Toks) (hw : Wf.namedType a = true)
    (hl : (Pr.namedType a).length < n) (hr : hd? rest ≠ some (.sym '<')) :
    Parse.namedType n (Pr.namedType a ++ rest) = some (a, rest) := by
  have h1 : Wf.ty a.ty = true := by simp [Wf.namedType] at hw; exact hw.2
  have h2 : (Pr.ty a.ty).length < n := by simp [Pr.namedType] at hl; omega
  simp [Pr.namedType, Parse.namedType, ty_pr n a.ty rest h1 h2 hr]

theorem Pr.namedType_ne (a : NamedType) (r : Toks) (c : Char) :
    Pr.namedType a ≠ [] ∧ hd? (Pr.namedType a ++ r) ≠ some (.sym c) := by
  simp [Pr.namedType]

/-- A comma list of named types followed by `c` (`)` for parameters). -/
theorem namedTypes_pr (n : Nat) (ps : List NamedType) (rest : Toks)
    (hw : ∀ a ∈ ps, Wf.namedType a = true)
    (hl : (commaList Pr.namedType ps).length < n) :
    delim (Parse.namedType n) ')' true n (commaList Pr.namedType ps ++ sy ')' :: rest) =
      some (ps, sy ')' :: rest) :=
  delim_commaList _ Pr.namedType ')' (by decide) ps n rest
    (fun a ha r hr => namedType_pr n a r (hw a ha)
      (by have := length_le_commaList Pr.namedType ps a ha; omega)
      (by rcases hr with h | h <;> simp [h]))
    (fun a _ => ⟨(Pr.namedType_ne a [] ')').1, by simpa using (Pr.namedType_ne a [] ')').2⟩)
    (by have := length_le_commaList' Pr.namedType (fun a => (Pr.namedType_ne a [] ')').1) ps
        omega)

theorem funcType_params_len (f : FuncType) :
    (commaList Pr.namedType f.params).length + 3 ≤ (Pr.funcType f).length := by
  cases f with
  | mk a ps r => cases a <;> cases r <;> simp [Pr.funcType] <;> omega

theorem funcType_pr (n : Nat) (f : FuncType) (rest : Toks) (hw : Wf.funcType f = true)
    (hl : (Pr.funcType f).length < n) (ha : hd? rest ≠ some .arrow)
    (hr : hd? rest ≠ some (.sym '<')) :
    Parse.funcType n (Pr.funcType f ++ rest) = some (f, rest) := by
  obtain ⟨as, ps, res⟩ := f
  have hp : ∀ a ∈ ps, Wf.namedType a = true := by
    simp [Wf.funcType] at hw; exact hw.1
  have hlp := funcType_params_len ⟨as, ps, res⟩
  have hd := fun rest => namedTypes_pr n ps rest hp (by simp at hlp; omega)
  cases res with
  | empty =>
    have hi : isTok .arrow rest = false := isTok_of_ne ha
    cases as <;> simp [Pr.funcType, Parse.funcType, hd, hi]
  | scalar t =>
    have ht : Wf.ty t = true := by simp [Wf.funcType] at hw; exact hw.2
    have hlt : (Pr.ty t).length < n := by
      simp [Pr.funcType] at hl; cases as <;> simp at hl <;> omega
    have hty := ty_pr n t rest ht hlt hr
    cases as <;> simp [Pr.funcType, Parse.funcType, hd, hty]

theorem Pr.funcType_cons (f : FuncType) :
    ∃ l, Pr.funcType f = kw .async :: l ∨ Pr.funcType f = kw .func :: l := by
  cases f with
  | mk a ps r => cases a <;> simp [Pr.funcType]

end Silmaril.Wasm.Wac.Text
