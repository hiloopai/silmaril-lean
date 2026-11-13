module

public import Silmaril.Proofs.Wasm.Wac.Text.World

/-!
# WAC text: expressions read back

Expressions, primary expressions and instantiation arguments are read back together by
induction on the fuel (`exprIH`): an expression of `k` tokens needs fuel above `3k + 2`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

/-- The next token does not continue an expression (`.` or `[`). -/
abbrev NoPost (r : Toks) : Prop := hd? r ≠ some (.sym '.') ∧ hd? r ≠ some (.sym '[')

theorem postfixes_stop (r : Toks) (h : NoPost r) : postfixes r = some ([], r) := by
  match r with
  | [] => rfl
  | ⟨ds, t⟩ :: r =>
    obtain ⟨h1, h2⟩ := h
    simp at h1 h2
    unfold postfixes
    split <;> simp_all

theorem postfixes_pr (post : List Postfix) (rest : Toks) (h : NoPost rest) :
    postfixes (post.flatMap Pr.postfixT ++ rest) = some (post, rest) := by
  induction post with
  | nil => exact postfixes_stop rest h
  | cons p ps ih =>
    cases p <;> simp [Pr.postfixT, postfixes, ih]

theorem Pr.args_eq : ∀ as : List Arg, Pr.args as = commaList Pr.arg as
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by rw [Pr.args, Pr.args_eq (b :: r)]; rfl

theorem Pr.arg_ne (a : Arg) : Pr.arg a ≠ [] ∧ hd? (Pr.arg a) ≠ some (.sym '}') := by
  cases a with
  | named nm e => cases nm <;> simp [Pr.arg, Pr.externName]
  | _ => simp [Pr.arg]

theorem Wf.args_iff : ∀ as : List Arg, Wf.args as = true ↔ ∀ a ∈ as, Wf.arg a = true
  | [] => by simp [Wf.args]
  | a :: as => by simp [Wf.args, Wf.args_iff as]

/-- The induction hypothesis of the expression parsers at fuel `n`. -/
def ExprIH (n : Nat) : Prop :=
  (∀ e rest, Wf.expr e = true → 3 * (Pr.expr e).length + 2 < n → NoPost rest →
    Parse.expr n (Pr.expr e ++ rest) = some (e, rest)) ∧
  (∀ p rest, Wf.primary p = true → 3 * (Pr.primary p).length + 1 < n →
    Parse.primary n (Pr.primary p ++ rest) = some (p, rest)) ∧
  (∀ a rest, Wf.arg a = true → CommaOr '}' rest → 3 * (Pr.arg a).length < n →
    Parse.arg n (Pr.arg a ++ rest) = some (a, rest))

theorem args_pr {n : Nat} (ih : ExprIH n) (as : List Arg) (rest : Toks)
    (hw : ∀ a ∈ as, Wf.arg a = true) (hl : 3 * (commaList Pr.arg as).length < n) :
    delim (Parse.arg n) '}' true n (commaList Pr.arg as ++ sy '}' :: rest) =
      some (as, sy '}' :: rest) :=
  delim_commaList _ Pr.arg '}' (by decide) as n rest
    (fun a ha r hr => ih.2.2 a r (hw a ha) hr
      (by have := length_le_commaList Pr.arg as a ha; omega))
    (fun a _ => Pr.arg_ne a)
    (by have := length_le_commaList' Pr.arg (fun a => (Pr.arg_ne a).1) as; omega)

theorem expr_step_expr {n : Nat} (ih : ExprIH n) (e : Expr) (rest : Toks) (hw : Wf.expr e = true)
    (hl : 3 * (Pr.expr e).length + 2 < n + 1) (hr : NoPost rest) :
    Parse.expr (n + 1) (Pr.expr e ++ rest) = some (e, rest) := by
  obtain ⟨p, post⟩ := e
  have hw' : Wf.primary p = true ∧ post.all Wf.postfixOk = true := by simpa [Wf.expr] using hw
  have hp := ih.2.1 p (post.flatMap Pr.postfixT ++ rest) hw'.1
    (by simp only [Pr.expr, List.length_append] at hl; omega)
  simp only [Pr.expr, List.append_assoc]
  simp [Parse.expr, hp, postfixes_pr post rest hr]

theorem expr_step_primary {n : Nat} (ih : ExprIH n) (p : Primary) (rest : Toks)
    (hw : Wf.primary p = true) (hl : 3 * (Pr.primary p).length + 1 < n + 1) :
    Parse.primary (n + 1) (Pr.primary p ++ rest) = some (p, rest) := by
  cases p with
  | new pkg as =>
    have hw' : pkgNameOk pkg = true ∧ Wf.args as = true := by simpa [Wf.primary] using hw
    have ha := args_pr ih as rest ((Wf.args_iff as).mp hw'.2)
      (by simp only [Pr.primary, Pr.args_eq, List.length_cons, List.length_append] at hl; omega)
    simp only [Pr.primary, Pr.args_eq, List.cons_append, List.append_assoc]
    simp [Parse.primary, pkgName_pr pkg _ hw'.1, ha]
  | nested e =>
    have he := ih.1 e (sy ')' :: rest) (by simpa [Wf.primary] using hw)
      (by simp only [Pr.primary, List.length_cons, List.length_append] at hl; omega)
      ⟨by simp, by simp⟩
    simp [Pr.primary, Parse.primary, he]
  | ident id => simp [Pr.primary, Parse.primary]

theorem expr_step_arg' {n : Nat} (ih : ExprIH n) (a : Arg) (c : Char) (ds : Docs) (r : Toks)
    (hc : c = ',' ∨ c = '}') (hw : Wf.arg a = true) (hl : 3 * (Pr.arg a).length < n + 1) :
    Parse.arg (n + 1) (Pr.arg a ++ ⟨ds, .sym c⟩ :: r) = some (a, ⟨ds, .sym c⟩ :: r) := by
  cases a with
  | named nm e =>
    have he := ih.1 e (⟨ds, .sym c⟩ :: r) (by simp [Wf.arg] at hw; exact hw.2)
      (by simp only [Pr.arg, List.length_cons] at hl; omega)
      ⟨by rcases hc with rfl | rfl <;> simp, by rcases hc with rfl | rfl <;> simp⟩
    cases nm <;> simp [Pr.arg, Pr.externName, Parse.arg, he]
  | _ => rcases hc with rfl | rfl <;> simp [Pr.arg, Parse.arg]

theorem expr_step_arg {n : Nat} (ih : ExprIH n) (a : Arg) (rest : Toks) (hw : Wf.arg a = true)
    (hr : CommaOr '}' rest) (hl : 3 * (Pr.arg a).length < n + 1) :
    Parse.arg (n + 1) (Pr.arg a ++ rest) = some (a, rest) := by
  match rest, hr with
  | [], hr => simp [CommaOr] at hr
  | ⟨ds, t⟩ :: r, hr =>
    have ht : t = .sym ',' ∨ t = .sym '}' := by simpa [CommaOr] using hr
    rcases ht with rfl | rfl
    · exact expr_step_arg' ih a ',' ds r (.inl rfl) hw hl
    · exact expr_step_arg' ih a '}' ds r (.inr rfl) hw hl

theorem exprIH : ∀ n, ExprIH n
  | 0 => ⟨fun _ _ _ h _ => absurd h (by omega), fun _ _ _ h => absurd h (by omega),
      fun _ _ _ _ h => absurd h (by omega)⟩
  | n + 1 => ⟨expr_step_expr (exprIH n), expr_step_primary (exprIH n), expr_step_arg (exprIH n)⟩

end Silmaril.Wasm.Wac.Text
