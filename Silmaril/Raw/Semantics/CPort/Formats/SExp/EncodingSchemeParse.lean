module

public import Silmaril.Semantics.CPort.Formats.SExp.EncodingSchemeDefs.Defs

/-!
# Scheme S-expression text: the datum grammar is unambiguous

Prefix uniqueness for `Datum`, `Skip` (datum comments) and `Data`, by strong
induction on the length of the token list, giving `docRel_functional`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Scheme

open Silmaril

/-- Tokens that can start a datum. -/
def DStart : Tok → Prop
  | .lp | .quote _ | .atom _ => True
  | _ => False

/-- The next token (if any) is not a datum comment. -/
def NoDC (r : List Tok) : Prop := ∀ t, r.head? = some t → t ≠ .datumComment

/-- The next token (if any) ends a sequence of data: `)` or `.`. -/
def DStop (r : List Tok) : Prop := ∀ t, r.head? = some t → t = .rp ∨ t = .dot

theorem Datum.head {d : List Tok} {x : SExp} (h : Datum d x) :
    ∃ t d₀, d = t :: d₀ ∧ DStart t := by
  cases h with
  | atom a => exact ⟨_, _, rfl, trivial⟩
  | list => exact ⟨_, _, rfl, trivial⟩
  | dotted => exact ⟨_, _, rfl, trivial⟩
  | quote => exact ⟨_, _, rfl, trivial⟩

theorem Skip.head {s : List Tok} (h : Skip s) :
    s = [] ∨ ∃ s₀, s = .datumComment :: s₀ := by
  cases h with
  | nil => exact Or.inl rfl
  | cons => exact Or.inr ⟨_, rfl⟩

theorem noDC_datum {d r : List Tok} {x : SExp} (h : Datum d x) : NoDC (d ++ r) := by
  obtain ⟨t, d₀, rfl, ht⟩ := h.head
  intro t' h'
  simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h'
  subst h'
  rintro rfl
  exact ht

theorem noDC_of_dstop {r : List Tok} (h : DStop r) : NoDC r := by
  intro t ht e
  rcases h t ht with rfl | rfl <;> cases e

theorem not_dstop_datum {d r : List Tok} {x : SExp} (h : Datum d x) : ¬ DStop (d ++ r) := by
  obtain ⟨t, d₀, rfl, ht⟩ := h.head
  intro hs
  rcases hs t rfl with rfl | rfl <;> exact ht

theorem not_noDC_dc {r : List Tok} : ¬ NoDC (.datumComment :: r) :=
  fun h => h _ rfl rfl

/-- The combined induction statement for token lists of length `≤ n`. -/
def ParseUnique (n : Nat) : Prop :=
  (∀ d d' r r' x x', d.length ≤ n → Datum d x → Datum d' x' → d ++ r = d' ++ r' →
      d = d' ∧ x = x') ∧
  (∀ s s' r r', s.length ≤ n → Skip s → Skip s' → s ++ r = s' ++ r' → NoDC r → NoDC r' →
      s = s') ∧
  (∀ a a' b b' r r' xs xs', (a ++ b).length ≤ n → Data a xs → Data a' xs' → Skip b →
      Skip b' → a ++ (b ++ r) = a' ++ (b' ++ r') → DStop r → DStop r' →
      a = a' ∧ xs = xs' ∧ b = b')

theorem skip_step (n : Nat) (ih : ∀ m < n, ParseUnique m) :
    ∀ s s' r r', s.length ≤ n → Skip s → Skip s' → s ++ r = s' ++ r' → NoDC r → NoDC r' →
      s = s' := by
  intro s s' r r' hn hs hs' he hr hr'
  cases hs with
  | nil =>
    cases hs' with
    | nil => rfl
    | cons =>
      simp only [List.nil_append, List.cons_append] at he
      subst he; exact absurd hr not_noDC_dc
  | @cons s₀ d rest x h₀ hd hrest =>
    cases hs' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at he
      subst he; exact absurd hr' not_noDC_dc
    | @cons s₀' d' rest' x' h₀' hd' hrest' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      simp only [List.length_cons, List.length_append] at hn
      have hs0 : s₀ = s₀' := (ih s₀.length (by omega)).2.1
        s₀ s₀' _ _ le_rfl h₀ h₀' he (noDC_datum hd) (noDC_datum hd')
      subst hs0
      have he1 := List.append_cancel_left he
      obtain ⟨rfl, -⟩ := (ih d.length (by omega)).1 d d' _ _ x x' le_rfl hd hd' he1
      have he2 := List.append_cancel_left he1
      obtain rfl := (ih rest.length (by omega)).2.1 rest rest' r r' le_rfl
        hrest hrest' he2 hr hr'
      rfl

theorem Datum.length_pos {d : List Tok} {x : SExp} (h : Datum d x) : 0 < d.length := by
  obtain ⟨t, d₀, rfl, -⟩ := h.head
  simp

theorem datum_step (n : Nat) (ih : ∀ m < n, ParseUnique m) :
    ∀ d d' r r' x x', d.length ≤ n → Datum d x → Datum d' x' → d ++ r = d' ++ r' →
      d = d' ∧ x = x' := by
  intro d d' r r' x x' hn hd hd' he
  cases hd with
  | atom a =>
    cases hd' with
    | atom a' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, Tok.atom.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact ⟨rfl, rfl⟩
    | _ => simp at he
  | @list ts s xs hts hs =>
    simp only [List.length_cons, List.length_append] at hn
    cases hd' with
    | @list ts' s' xs' hts' hs' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain ⟨rfl, rfl, rfl⟩ := (ih (ts ++ s).length (by simp; omega)).2.2 ts ts' s s' _ _ xs xs'
        le_rfl hts hts' hs hs' he (by simp [DStop]) (by simp [DStop])
      exact ⟨rfl, rfl⟩
    | @dotted ts' s₁ d₀ s₂ xs' tail hts' hne hs₁ hd₀ hs₂ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      have he' : ts ++ (s ++ (Tok.rp :: r)) =
          ts' ++ ([] ++ (Tok.dot :: (s₁ ++ (d₀ ++ (s₂ ++ (Tok.rp :: r')))))) := by
        simpa using he
      obtain ⟨rfl, rfl, rfl⟩ := (ih (ts ++ s).length (by simp; omega)).2.2 ts ts' s [] _ _ xs xs'
        le_rfl hts hts' hs .nil he' (by simp [DStop]) (by simp [DStop])
      simp at he
    | _ => simp at he
  | @dotted ts s₁ d₀ s₂ xs tail hts hne hs₁ hd₀ hs₂ =>
    simp only [List.length_cons, List.length_append] at hn
    cases hd' with
    | @list ts' s' xs' hts' hs' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      have he' : ts ++ ([] ++ (Tok.dot :: (s₁ ++ (d₀ ++ (s₂ ++ (Tok.rp :: r)))))) =
          ts' ++ (s' ++ (Tok.rp :: r')) := by
        simpa using he
      obtain ⟨rfl, rfl, h⟩ := (ih ts.length (by omega)).2.2 ts ts' [] s' _ _ xs xs'
        (by simp) hts hts' .nil hs' he' (by simp [DStop]) (by simp [DStop])
      subst h
      simp at he
    | @dotted ts' s₁' d₀' s₂' xs' tail' hts' hne' hs₁' hd₀' hs₂' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      have he' : ts ++ ([] ++ (Tok.dot :: (s₁ ++ (d₀ ++ (s₂ ++ (Tok.rp :: r)))))) =
          ts' ++ ([] ++ (Tok.dot :: (s₁' ++ (d₀' ++ (s₂' ++ (Tok.rp :: r')))))) := by
        simpa using he
      obtain ⟨rfl, rfl, -⟩ := (ih ts.length (by omega)).2.2 ts ts' [] [] _ _ xs xs'
        (by simp) hts hts' .nil .nil he' (by simp [DStop]) (by simp [DStop])
      have he1 := List.append_cancel_left he
      simp only [List.cons.injEq, true_and] at he1
      obtain rfl := (ih s₁.length (by omega)).2.1 s₁ s₁' _ _ le_rfl hs₁ hs₁' he1
        (noDC_datum hd₀) (noDC_datum hd₀')
      have he2 := List.append_cancel_left he1
      obtain ⟨rfl, rfl⟩ := (ih d₀.length (by omega)).1 d₀ d₀' _ _ tail tail' le_rfl hd₀ hd₀' he2
      have he3 := List.append_cancel_left he2
      obtain rfl := (ih s₂.length (by omega)).2.1 s₂ s₂' _ _ le_rfl hs₂ hs₂' he3
        (by simp [NoDC]) (by simp [NoDC])
      exact ⟨rfl, rfl⟩
    | _ => simp at he
  | @quote name s d₀ x₀ hs hd₀ =>
    simp only [List.length_cons, List.length_append] at hn
    cases hd' with
    | @quote name' s' d₀' x₀' hs' hd₀' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, Tok.quote.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain rfl := (ih s.length (by omega)).2.1 s s' _ _ le_rfl hs hs' he
        (noDC_datum hd₀) (noDC_datum hd₀')
      have he1 := List.append_cancel_left he
      obtain ⟨rfl, rfl⟩ := (ih d₀.length (by omega)).1 d₀ d₀' _ _ x₀ x₀' le_rfl hd₀ hd₀' he1
      exact ⟨rfl, rfl⟩
    | _ => simp at he

theorem data_step (n : Nat) (ih : ∀ m < n, ParseUnique m)
    (hS : ∀ s s' r r', s.length ≤ n → Skip s → Skip s' → s ++ r = s' ++ r' → NoDC r →
      NoDC r' → s = s')
    (hD : ∀ d d' r r' x x', d.length ≤ n → Datum d x → Datum d' x' → d ++ r = d' ++ r' →
      d = d' ∧ x = x') :
    ∀ a a' b b' r r' xs xs', (a ++ b).length ≤ n → Data a xs → Data a' xs' → Skip b →
      Skip b' → a ++ (b ++ r) = a' ++ (b' ++ r') → DStop r → DStop r' →
      a = a' ∧ xs = xs' ∧ b = b' := by
  intro a a' b b' r r' xs xs' hn ha ha' hb hb' he hr hr'
  cases ha with
  | nil =>
    cases ha' with
    | nil =>
      simp only [List.nil_append] at he hn
      exact ⟨rfl, rfl, hS b b' r r' hn hb hb' he (noDC_of_dstop hr) (noDC_of_dstop hr')⟩
    | @cons s' d' rest' x' xs₀' hs' hd' hrest' =>
      simp only [List.nil_append, List.append_assoc] at he hn
      obtain rfl := hS b s' r _ hn hb hs' he (noDC_of_dstop hr) (noDC_datum hd')
      have := List.append_cancel_left he
      subst this
      exact absurd hr (not_dstop_datum hd')
  | @cons s d rest x xs₀ hs hd hrest =>
    simp only [List.append_assoc, List.length_append] at he hn
    have hpos := hd.length_pos
    cases ha' with
    | nil =>
      simp only [List.nil_append] at he
      obtain rfl := hS s b' _ r' (by omega) hs hb' he (noDC_datum hd) (noDC_of_dstop hr')
      have := List.append_cancel_left he
      subst this
      exact absurd hr' (not_dstop_datum hd)
    | @cons s' d' rest' x' xs₀' hs' hd' hrest' =>
      simp only [List.append_assoc] at he
      obtain rfl := hS s s' _ _ (by omega) hs hs' he (noDC_datum hd) (noDC_datum hd')
      have he1 := List.append_cancel_left he
      obtain ⟨rfl, rfl⟩ := hD d d' _ _ x x' (by omega) hd hd' he1
      have he2 := List.append_cancel_left he1
      obtain ⟨rfl, rfl, rfl⟩ := (ih (rest ++ b).length (by simp; omega)).2.2 rest rest' b b' r r'
        xs₀ xs₀' le_rfl hrest hrest' hb hb' he2 hr hr'
      exact ⟨rfl, rfl, rfl⟩

theorem parseUnique (n : Nat) : ParseUnique n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hS := skip_step n ih
    have hD := datum_step n ih
    exact ⟨hD, hS, data_step n ih hS hD⟩

theorem docRel_unique : docRel.Functional := by
  rintro ts x x' ⟨a, b, xs, rfl, ha, hb, rfl⟩ ⟨a', b', xs', he, ha', hb', rfl⟩
  have he' : a ++ (b ++ []) = a' ++ (b' ++ []) := by simpa using he
  obtain ⟨-, rfl, -⟩ := (parseUnique (a ++ b).length).2.2 a a' b b' [] [] xs xs' le_rfl
    ha ha' hb hb' he' (by simp [DStop]) (by simp [DStop])
  rfl

/-! ## Helpers for example spellings -/

theorem data_one {d : List Tok} {x : SExp} (h : Datum d x) : Data d [x] := by
  simpa using Data.cons Skip.nil h Data.nil

theorem docRel_one {d : List Tok} {x : SExp} (h : Datum d x) : docRel d (doc [x]) :=
  ⟨d, [], [x], by simp, data_one h, .nil, rfl⟩

end Silmaril.Formats.SExpEncoding.Scheme
