module

public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Silmaril.Proofs.Wasm.Wit.Text.Lex
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# WIT text: types read back

`ty n (toks (prTy t) ++ rest) = some (t, rest)` when the fuel `n` is at least the
number of printed tokens and `rest` does not start with `<` (which would extend
`result`, `future` and `stream`); `tys` reads back comma-separated types up to `>`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open _root_.Silmaril.Wasm.Wit.Text.Parse
open Silmaril.Wasm.Component.Wat (natChars parseNat parseNat_natChars)

/-- `rest` does not start with `<`. -/
abbrev NotLt (r : List Tok) : Prop := r.head? ≠ some (.sym '<')

/-- The head of a printed type is a keyword other than `_`, or an identifier. -/
def TyHead (t : Tok) : Prop := (∃ s, t = .id s) ∨ (∃ w, t = .kw w ∧ w ≠ .underscore)

theorem prTy_head (t : Ty) : ∃ x xs, toks (prTy t) = x :: xs ∧ TyHead x := by
  cases t <;> simp [prTy, TyHead]

theorem prTy_length_pos (t : Ty) : 0 < (prTy t).length := by
  obtain ⟨x, xs, h, -⟩ := prTy_head t
  have := congrArg List.length h
  simp at this; omega

theorem head_prTy_append (t : Ty) (r : List Tok) :
    (∀ c, (toks (prTy t) ++ r).head? ≠ some (.sym c)) ∧
      (toks (prTy t) ++ r).head? ≠ some (.kw .underscore) := by
  obtain ⟨x, xs, h, hx⟩ := prTy_head t
  rw [h]
  rcases hx with ⟨s, rfl⟩ | ⟨w, rfl, hw⟩ <;> simp_all

macro "unfold_pr" : tactic =>
  `(tactic| simp only [prTy, prOpt, prArg, prTys, toks_append, toks_cons, toks_nil,
      List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, List.length_nil] at *)

mutual
theorem ty_prTy : (t : Ty) → ∀ n rest, (prTy t).length ≤ n → NotLt rest →
    ty n (toks (prTy t) ++ rest) = some (t, rest)
  | .named s, n, rest, h, _ => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, ty]
  | .list a, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ty, ty_prTy a m _ (by omega) (by simp)]
    rfl
  | .fixedList a q, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ty, ty_prTy a m _ (by omega) (by simp)]
    simp [String.toList_ofList, parseNat_natChars]
  | .map a b, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ty, ty_prTy a m _ (by omega) (by simp)]
    simp only
    rw [ty_prTy b m _ (by omega) (by simp)]
    rfl
  | .tuple ts, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ty, tys_prTys ts m _ (by omega) (by simp)]
    rfl
  | .option a, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ty, ty_prTy a m _ (by omega) (by simp)]
    rfl
  | .result none none, n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, ty, hr]
  | .result (some a) none, n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hd := (head_prTy_append a (.sym '>' :: rest)).2
    simp only [ty, List.head?_cons, List.tail_cons, ite_true, hd, ite_false]
    rw [ty_prTy a m _ (by omega) (by simp)]
    rfl
  | .result none (some e), n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ty, List.head?_cons, List.tail_cons, ite_true]
    rw [ty_prTy e m _ (by omega) (by simp)]
    rfl
  | .result (some a) (some e), n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hd := (head_prTy_append a (.sym ',' :: (toks (prTy e) ++ Tok.sym '>' :: rest))).2
    simp only [ty, List.head?_cons, List.tail_cons, ite_true, hd, ite_false]
    rw [ty_prTy a m _ (by omega) (by simp)]
    simp only
    rw [ty_prTy e m _ (by omega) (by simp)]
    rfl
  | .own s, n, rest, h, _ => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, ty]
  | .borrow s, n, rest, h, _ => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, ty]
  | .future none, n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, prArg, ty, hr]
  | .future (some a), n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ty, List.head?_cons, List.tail_cons, ite_true]
    rw [ty_prTy a m _ (by omega) (by simp)]
    rfl
  | .stream none, n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, prArg, ty, hr]
  | .stream (some a), n, rest, h, _ => by
    unfold_pr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ty, List.head?_cons, List.tail_cons, ite_true]
    rw [ty_prTy a m _ (by omega) (by simp)]
    rfl
  | .bool, n, rest, h, _ | .s8, n, rest, h, _ | .s16, n, rest, h, _ | .s32, n, rest, h, _
  | .s64, n, rest, h, _ | .u8, n, rest, h, _ | .u16, n, rest, h, _ | .u32, n, rest, h, _
  | .u64, n, rest, h, _ | .f32, n, rest, h, _ | .f64, n, rest, h, _ | .char, n, rest, h, _
  | .string, n, rest, h, _ | .errorContext, n, rest, h, _ => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [prTy] at h; omega⟩
    simp [prTy, ty, primOf]

theorem tys_prTys : (ts : List Ty) → ∀ n rest, (prTys ts).length + 1 ≤ n →
    rest.head? = some (.sym '>') → tys n (toks (prTys ts) ++ rest) = some (ts, rest)
  | [], n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [prTys, tys, hr]
  | [t], n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hd := (head_prTy_append t rest).1 '>'
    simp only [prTys] at h ⊢
    rw [tys]; simp only [hd, ite_false]; rw [ty_prTy t m rest (by omega) (by simp [hr])]
    simp [hr]
  | t :: t' :: ts, n, rest, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hp := prTy_length_pos t
    simp only [prTys, toks_append, toks_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.length_append, List.length_cons] at h ⊢
    have hd := (head_prTy_append t (.sym ',' :: (toks (prTys (t' :: ts)) ++ rest))).1 '>'
    rw [tys]; simp only [hd, ite_false]; rw [ty_prTy t m _ (by omega) (by simp)]
    simp only [List.head?_cons, List.tail_cons, ite_true]
    rw [tys_prTys (t' :: ts) m rest (by omega) hr]
    rfl
end

end Silmaril.Wasm.Wit.Text
