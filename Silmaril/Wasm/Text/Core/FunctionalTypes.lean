module

public import Silmaril.Wasm.Text.Core.Instructions

/-!
# Core 3.0 text format: functionality of values and types

Uniqueness lemmas for the value and type grammars (`Text/Values.lean`,
`Core/Types.lean`): for a fixed identifier context whose type names are
distinct, the items of a numeral, index, value type, type definition, type
use, limits, … determine what they denote.

* Generic list lemmas: `munch` (two splittings `a ++ r = a' ++ r'` of the same
  list into a maximal run of `P`-items and a rest not starting with a `P`-item
  coincide) and functionality of `List.Forall₂`.
* Numerals (`Num`, `HexNum`, `UN`, `SN`, `IN`) and float literals (`FMag`,
  `FN`): lexical uniqueness at the character level.
* Types: `HeapTypeT` … `RecTypeT`, `TypeUseT`, `ExternTypeT`.
* Congruence of the type grammars along contexts that resolve type
  identifiers in the same way (`TypesEq`), used to compare readings of one
  module field in two candidate module contexts.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat Silmaril.Wasm

/-! ## Generic list lemmas -/

/-- Maximal munch: a list split into a run of `P`-items followed by a rest that
does not start with a `P`-item is split uniquely. -/
theorem munch {α : Type} {P : α → Prop} :
    ∀ {a a' r r' : List α}, (∀ x ∈ a, P x) → (∀ x ∈ a', P x) →
      (∀ x ∈ r.head?, ¬ P x) → (∀ x ∈ r'.head?, ¬ P x) → a ++ r = a' ++ r' →
      a = a' ∧ r = r'
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], y :: a', r, r', _, ha', hr, _, h => by
      subst h; exact absurd (ha' y (by simp)) (hr y (by simp))
  | x :: a, [], r, r', ha, _, _, hr', h => by
      subst h; exact absurd (ha x (by simp)) (hr' x (by simp))
  | x :: a, y :: a', r, r', ha, ha', hr, hr', h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := munch (fun z hz => ha z (by simp [hz]))
        (fun z hz => ha' z (by simp [hz])) hr hr' h
      exact ⟨rfl, rfl⟩

/-- `munch` when the rests are not given as lists starting with a non-`P` item
but are known to be empty or to start with a non-`P` item. -/
theorem munch_left {α : Type} {P : α → Prop} {a a' r r' : List α}
    (ha : ∀ x ∈ a, P x) (ha' : ∀ x ∈ a', P x) (hr : ∀ x ∈ r.head?, ¬ P x)
    (hr' : ∀ x ∈ r'.head?, ¬ P x) (h : a ++ r = a' ++ r') : a = a' :=
  (munch ha ha' hr hr' h).1

theorem forall₂_functional {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b b', R a b → R a b' → b = b') :
    ∀ {as : List α} {bs bs' : List β}, List.Forall₂ R as bs → List.Forall₂ R as bs' → bs = bs'
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h hs, .cons h' hs' => by
      rw [hR _ _ _ h h', forall₂_functional hR hs hs']

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {P : α → Prop}
    (hR : ∀ a b, R a b → P a) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ x ∈ as, P x
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hR _ _ h
      · exact forall₂_mem_left hR hs x hx

theorem forall₂_length_eq {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : as.length = bs.length := h.length_eq

/-- Keys of a list without duplicates determine their values. -/
theorem lookup_unique {α β : Type} :
    ∀ {l : List (α × β)} {a : α} {b b' : β}, (l.map Prod.fst).Nodup → (a, b) ∈ l →
      (a, b') ∈ l → b = b'
  | [], _, _, _, _, h, _ => by simp at h
  | (c, d) :: l, a, b, b', hn, h, h' => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      simp only [List.mem_cons, Prod.mk.injEq] at h h'
      rcases h with ⟨rfl, rfl⟩ | h <;> rcases h' with ⟨h1, rfl⟩ | h'
      · rfl
      · exact absurd ⟨(a, b'), h', rfl⟩ hn.1
      · exact absurd ⟨(a, b), h, h1 ▸ rfl⟩ hn.1
      · exact lookup_unique hn.2 h h'

/-- A single item and a list item spelled with `L` are different. -/
@[simp] theorem K_ne_L (s : String) (xs : List SExp) (y : SExp) : K s ≠ L (y :: xs) := by
  simp [K, L, kw, listOf]

@[simp] theorem L_ne_K (s : String) (xs : List SExp) (y : SExp) : L (y :: xs) ≠ K s := by
  simp [K, L, kw, listOf]

@[simp] theorem K_inj (s t : String) : K s = K t ↔ s = t := by simp [K, kw]

@[simp] theorem id_ne_K (n s : String) : (Formats.SExp2.atom (Atom.id n) : SExp) ≠ K s := by simp [K, kw]

@[simp] theorem K_ne_id (n s : String) : K s ≠ (Formats.SExp2.atom (Atom.id n) : SExp) := by simp [K, kw]

@[simp] theorem id_ne_L (n : String) (xs : List SExp) (y : SExp) :
    (Formats.SExp2.atom (Atom.id n) : SExp) ≠ L (y :: xs) := by simp [L, listOf]

@[simp] theorem L_inj (xs ys : List SExp) : L xs = L ys ↔ xs = ys :=
  ⟨fun h => listOf_injective h, fun h => h ▸ rfl⟩

/-! ## Numerals -/

def IsDigit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

instance (c : Char) : Decidable (IsDigit c) := by unfold IsDigit; infer_instance

theorem num_chars {cs : Chars} {n : Nat} (h : Num cs n) : ∀ c ∈ cs, IsDigit c ∨ c = '_' := by
  induction h with
  | one hd => intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact .inl hd
  | snoc _ hd ih =>
      intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ih c hc
      · exact .inl hd
  | snocSep _ hd ih =>
      intro c hc; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact ih c hc
      · exact .inr rfl
      · exact .inl hd

theorem num_head {cs : Chars} {n : Nat} (h : Num cs n) : ∃ c t, cs = c :: t ∧ IsDigit c := by
  induction h with
  | one hd => exact ⟨_, [], rfl, hd⟩
  | snoc _ _ ih => obtain ⟨c, t, rfl, hc⟩ := ih; exact ⟨c, _, rfl, hc⟩
  | snocSep _ _ ih => obtain ⟨c, t, rfl, hc⟩ := ih; exact ⟨c, _, rfl, hc⟩

theorem num_last {cs : Chars} {n : Nat} (h : Num cs n) : ∃ t c, cs = t ++ [c] ∧ IsDigit c := by
  cases h with
  | one hd => exact ⟨[], _, rfl, hd⟩
  | snoc _ hd => exact ⟨_, _, rfl, hd⟩
  | @snocSep ds _ _ _ hd => exact ⟨ds ++ ['_'], _, by simp, hd⟩

theorem num_functional {cs : Chars} {n m : Nat} (h : Num cs n) (h' : Num cs m) : n = m := by
  induction h generalizing m with
  | @one d hd =>
      generalize e : [d] = cs at h'
      cases h' with
      | one => simp only [List.cons.injEq, and_true] at e; subst e; rfl
      | @snoc ds' n' d' h₁ hd' =>
          obtain ⟨c, t, rfl, _⟩ := num_head h₁
          have := congrArg List.length e; simp at this
      | snocSep h₁ _ => have := congrArg List.length e; simp at this
  | @snoc ds n d h₀ hd ih =>
      generalize e : ds ++ [d] = cs at h'
      cases h' with
      | one =>
          obtain ⟨c, t, rfl, _⟩ := num_head h₀
          have := congrArg List.length e; simp at this
      | @snoc ds' n' d' h₁ hd' =>
          obtain ⟨rfl, h2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, and_true] at h2; subst h2
          rw [ih h₁]
      | @snocSep ds' n' d' h₁ hd' =>
          have e' : ds ++ [d] = (ds' ++ ['_']) ++ [d'] := by simpa using e
          obtain ⟨rfl, -⟩ := List.append_inj' e' rfl
          obtain ⟨t, c, ht, hc⟩ := num_last h₀
          obtain ⟨rfl, h3⟩ := List.append_inj' ht rfl
          simp only [List.cons.injEq, and_true] at h3; subst h3
          simp [IsDigit] at hc
  | @snocSep ds n d h₀ hd ih =>
      generalize e : ds ++ ['_', d] = cs at h'
      cases h' with
      | one => have := congrArg List.length e; simp at this
      | @snoc ds' n' d' h₁ hd' =>
          have e' : (ds ++ ['_']) ++ [d] = ds' ++ [d'] := by simpa using e
          obtain ⟨rfl, -⟩ := List.append_inj' e' rfl
          obtain ⟨t, c, ht, hc⟩ := num_last h₁
          obtain ⟨rfl, h3⟩ := List.append_inj' ht rfl
          simp only [List.cons.injEq, and_true] at h3; subst h3
          simp [IsDigit] at hc
      | @snocSep ds' n' d' h₁ hd' =>
          obtain ⟨rfl, h2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, and_true, true_and] at h2
          subst h2
          rw [ih h₁]

theorem hexNum_chars {cs : Chars} {n : Nat} (h : HexNum cs n) :
    ∀ c ∈ cs, IsHexDigit c ∨ c = '_' := by
  induction h with
  | one hd => intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact .inl hd
  | snoc _ hd ih =>
      intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ih c hc
      · exact .inl hd
  | snocSep _ hd ih =>
      intro c hc; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact ih c hc
      · exact .inr rfl
      · exact .inl hd

theorem hexNum_head {cs : Chars} {n : Nat} (h : HexNum cs n) :
    ∃ c t, cs = c :: t ∧ IsHexDigit c := by
  induction h with
  | one hd => exact ⟨_, [], rfl, hd⟩
  | snoc _ _ ih => obtain ⟨c, t, rfl, hc⟩ := ih; exact ⟨c, _, rfl, hc⟩
  | snocSep _ _ ih => obtain ⟨c, t, rfl, hc⟩ := ih; exact ⟨c, _, rfl, hc⟩

theorem hexNum_last {cs : Chars} {n : Nat} (h : HexNum cs n) :
    ∃ t c, cs = t ++ [c] ∧ IsHexDigit c := by
  cases h with
  | one hd => exact ⟨[], _, rfl, hd⟩
  | snoc _ hd => exact ⟨_, _, rfl, hd⟩
  | @snocSep ds _ _ _ hd => exact ⟨ds ++ ['_'], _, by simp, hd⟩

theorem hexNum_functional {cs : Chars} {n m : Nat} (h : HexNum cs n) (h' : HexNum cs m) : n = m := by
  induction h generalizing m with
  | @one d hd =>
      generalize e : [d] = cs at h'
      cases h' with
      | one => simp only [List.cons.injEq, and_true] at e; subst e; rfl
      | @snoc ds' n' d' h₁ hd' =>
          obtain ⟨c, t, rfl, _⟩ := hexNum_head h₁
          have := congrArg List.length e; simp at this
      | snocSep h₁ _ => have := congrArg List.length e; simp at this
  | @snoc ds n d h₀ hd ih =>
      generalize e : ds ++ [d] = cs at h'
      cases h' with
      | one =>
          obtain ⟨c, t, rfl, _⟩ := hexNum_head h₀
          have := congrArg List.length e; simp at this
      | @snoc ds' n' d' h₁ hd' =>
          obtain ⟨rfl, h2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, and_true] at h2; subst h2
          rw [ih h₁]
      | @snocSep ds' n' d' h₁ hd' =>
          have e' : ds ++ [d] = (ds' ++ ['_']) ++ [d'] := by simpa using e
          obtain ⟨rfl, -⟩ := List.append_inj' e' rfl
          obtain ⟨t, c, ht, hc⟩ := hexNum_last h₀
          obtain ⟨rfl, h3⟩ := List.append_inj' ht rfl
          simp only [List.cons.injEq, and_true] at h3; subst h3
          simp [IsHexDigit] at hc
  | @snocSep ds n d h₀ hd ih =>
      generalize e : ds ++ ['_', d] = cs at h'
      cases h' with
      | one => have := congrArg List.length e; simp at this
      | @snoc ds' n' d' h₁ hd' =>
          have e' : (ds ++ ['_']) ++ [d] = ds' ++ [d'] := by simpa using e
          obtain ⟨rfl, -⟩ := List.append_inj' e' rfl
          obtain ⟨t, c, ht, hc⟩ := hexNum_last h₁
          obtain ⟨rfl, h3⟩ := List.append_inj' ht rfl
          simp only [List.cons.injEq, and_true] at h3; subst h3
          simp [IsHexDigit] at hc
      | @snocSep ds' n' d' h₁ hd' =>
          obtain ⟨rfl, h2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, and_true, true_and] at h2
          subst h2
          rw [ih h₁]

theorem un_head {N : Nat} {cs : Chars} {n : Nat} (h : UN N cs n) :
    ∃ c t, cs = c :: t ∧ IsDigit c := by
  rcases h with ⟨h | ⟨ds, rfl, _⟩, _⟩
  · exact num_head h
  · exact ⟨'0', _, rfl, by decide⟩

theorem un_functional {N M : Nat} {cs : Chars} {n m : Nat} (h : UN N cs n) (h' : UN M cs m) :
    n = m := by
  rcases h with ⟨h | ⟨ds, rfl, h⟩, _⟩ <;> rcases h' with ⟨h' | ⟨ds', e, h'⟩, _⟩
  · exact num_functional h h'
  · subst e; have := num_chars h 'x' (by simp); simp [IsDigit] at this
  · have := num_chars h' 'x' (by simp); simp [IsDigit] at this
  · simp only [List.cons.injEq, true_and] at e; subst e; exact hexNum_functional h h'

theorem signChars_cases {cs : Chars} {s : Int} (h : SignChars cs s) :
    (cs = [] ∧ s = 1) ∨ (cs = ['+'] ∧ s = 1) ∨ (cs = ['-'] ∧ s = -1) := h

/-- Sign splitting: a sign followed by a digit-initial rest. -/
theorem sign_split {sc rest sc' rest' : Chars} {s s' : Int} (h : SignChars sc s)
    (h' : SignChars sc' s') (hr : ∀ c ∈ rest.head?, c ≠ '+' ∧ c ≠ '-')
    (hr' : ∀ c ∈ rest'.head?, c ≠ '+' ∧ c ≠ '-') (e : sc ++ rest = sc' ++ rest') :
    sc = sc' ∧ s = s' ∧ rest = rest' := by
  have key := munch (P := fun c => c = '+' ∨ c = '-') (a := sc) (a' := sc') (r := rest)
    (r' := rest')
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | exact ⟨rfl, rfl, by simpa using e⟩
      | (exfalso
         have := key (by simp) (by simp) (fun c hc => by have := hr c hc; tauto)
           (fun c hc => by have := hr' c hc; tauto) e
         simp at this)

theorem un_head_nosign {N : Nat} {cs : Chars} {n : Nat} (h : UN N cs n) :
    ∀ c ∈ cs.head?, c ≠ '+' ∧ c ≠ '-' := by
  obtain ⟨c, t, rfl, hc⟩ := un_head h
  intro c' hc'; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'; subst hc'
  constructor <;> (rintro rfl; simp [IsDigit] at hc)

theorem sn_functional {N M : Nat} {cs : Chars} {i j : Int} (h : SN N cs i) (h' : SN M cs j) :
    i = j := by
  obtain ⟨sc, rest, s, n, rfl, hs, hu, rfl, _⟩ := h
  obtain ⟨sc', rest', s', n', e, hs', hu', rfl, _⟩ := h'
  obtain ⟨rfl, rfl, rfl⟩ := sign_split hs hs' (un_head_nosign hu) (un_head_nosign hu') e
  rw [un_functional hu hu']

theorem in_functional {N : Nat} {cs : Chars} {b b' : BitVec N} (h : IN N cs b) (h' : IN N cs b') :
    b = b' := by
  have mixed : ∀ {n : Nat} {i : Int}, UN N cs n → SN N cs i → (i : Int) = n := by
    intro n i hu hs
    obtain ⟨sc, rest, s, n', rfl, hsc, hu', rfl, _⟩ := hs
    rcases hsc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.nil_append] at hu; rw [un_functional hu' hu]; simp
    · obtain ⟨c, t, e, hc⟩ := un_head hu; simp at e; obtain ⟨rfl, -⟩ := e; simp [IsDigit] at hc
    · obtain ⟨c, t, e, hc⟩ := un_head hu; simp at e; obtain ⟨rfl, -⟩ := e; simp [IsDigit] at hc
  rcases h with ⟨n, hu, rfl⟩ | ⟨i, hs, rfl⟩ <;> rcases h' with ⟨n', hu', rfl⟩ | ⟨i', hs', rfl⟩
  · rw [un_functional hu hu']
  · rw [mixed hu hs']; simp
  · rw [mixed hu' hs]; simp
  · rw [sn_functional hs hs']

theorem atomU_functional {N M : Nat} {x : SExp} {n m : Nat} (h : AtomU N x n) (h' : AtomU M x m) :
    n = m := by
  obtain ⟨t, rfl, h⟩ := h
  obtain ⟨t', e, h'⟩ := h'
  simp only [K_inj] at e; subst e
  exact un_functional h h'

theorem atomI_functional {N : Nat} {x : SExp} {b b' : BitVec N} (h : AtomI N x b)
    (h' : AtomI N x b') : b = b' := by
  obtain ⟨t, rfl, h⟩ := h
  obtain ⟨t', e, h'⟩ := h'
  simp only [K_inj] at e; subst e
  exact in_functional h h'

theorem atomU32_functional {x : SExp} {n m : Fin (2 ^ 32)} (h : AtomU32 x n) (h' : AtomU32 x m) :
    n = m := Fin.ext (atomU_functional h h')

theorem atomU64_functional {x : SExp} {n m : Fin (2 ^ 64)} (h : AtomU64 x n) (h' : AtomU64 x m) :
    n = m := Fin.ext (atomU_functional h h')

/-! ## Float literals -/

theorem mant_aux {R : Chars → Nat → Prop} {radix : Nat}
    (hf : ∀ {cs n m}, R cs n → R cs m → n = m) (hc : ∀ {cs n}, R cs n → '.' ∉ cs)
    (hne : ∀ {n}, ¬ R [] n) {cs : Chars} {m k m' k' : Nat}
    (h : (R cs m ∧ k = 0) ∨ (∃ p, cs = p ++ ['.'] ∧ R p m ∧ k = 0) ∨
      ∃ p f n v, cs = p ++ '.' :: f ∧ R p n ∧ R f v ∧ k = digitCount f ∧ m = n * radix ^ k + v)
    (h' : (R cs m' ∧ k' = 0) ∨ (∃ p, cs = p ++ ['.'] ∧ R p m' ∧ k' = 0) ∨
      ∃ p f n v, cs = p ++ '.' :: f ∧ R p n ∧ R f v ∧ k' = digitCount f ∧
        m' = n * radix ^ k' + v) :
    m = m' ∧ k = k' := by
  have split : ∀ {p p' f f' : Chars} {n n' : Nat}, R p n → R p' n' → p ++ '.' :: f = p' ++ '.' :: f' →
      p = p' ∧ f = f' := by
    intro p p' f f' n n' hp hp' e
    have := munch (P := fun c => c ≠ '.') (fun c hc' => by rintro rfl; exact hc hp hc')
      (fun c hc' => by rintro rfl; exact hc hp' hc') (by simp) (by simp) e
    simpa using this
  rcases h with ⟨h, rfl⟩ | ⟨p, rfl, h, rfl⟩ | ⟨p, f, n, v, rfl, hp, hfv, rfl, rfl⟩ <;>
    rcases h' with ⟨h', rfl⟩ | ⟨p', e, h', rfl⟩ | ⟨p', f', n', v', e, hp', hfv', rfl, rfl⟩
  · exact ⟨hf h h', rfl⟩
  · subst e; exact absurd (by simp) (hc h)
  · subst e; exact absurd (by simp) (hc h)
  · exact absurd (by simp) (hc h')
  · obtain ⟨rfl, -⟩ := List.append_inj' e rfl; exact ⟨hf h h', rfl⟩
  · obtain ⟨rfl, rfl⟩ := split h hp' e; exact absurd hfv' hne
  · exact absurd (by simp) (hc h')
  · obtain ⟨rfl, rfl⟩ := split hp h' e; exact absurd hfv hne
  · obtain ⟨rfl, rfl⟩ := split hp hp' e
    rw [hf hp hp', hf hfv hfv']; exact ⟨rfl, rfl⟩

theorem num_nodot {cs : Chars} {n : Nat} (h : Num cs n) : '.' ∉ cs := fun hc => by
  have := num_chars h '.' hc; simp [IsDigit] at this

theorem hexNum_nodot {cs : Chars} {n : Nat} (h : HexNum cs n) : '.' ∉ cs := fun hc => by
  have := hexNum_chars h '.' hc; simp [IsHexDigit] at this

theorem num_ne_nil {n : Nat} : ¬ Num [] n := fun h => by obtain ⟨c, t, h, _⟩ := num_head h; simp at h

theorem hexNum_ne_nil {n : Nat} : ¬ HexNum [] n := fun h => by
  obtain ⟨c, t, h, _⟩ := hexNum_head h; simp at h

theorem mant_functional {hex : Bool} {cs : Chars} {m k m' k' : Nat} (h : Mant hex cs m k)
    (h' : Mant hex cs m' k') : m = m' ∧ k = k' := by
  cases hex
  · exact mant_aux (R := Num) num_functional num_nodot num_ne_nil (by simpa [Mant] using h)
      (by simpa [Mant] using h')
  · exact mant_aux (R := HexNum) hexNum_functional hexNum_nodot hexNum_ne_nil
      (by simpa [Mant] using h) (by simpa [Mant] using h')

/-- Characters of a mantissa (digits of the radix, `_` and `.`). -/
def MantChar (hex : Bool) (c : Char) : Prop :=
  (if hex then IsHexDigit c else IsDigit c) ∨ c = '_' ∨ c = '.'

theorem mant_chars {hex : Bool} {cs : Chars} {m k : Nat} (h : Mant hex cs m k) :
    ∀ c ∈ cs, MantChar hex c := by
  have hR : ∀ {cs n}, (if hex then HexNum else Num) cs n → ∀ c ∈ cs, MantChar hex c := by
    intro cs n hr c hc
    cases hex
    · simpa [MantChar] using (num_chars (by simpa using hr) c hc).imp_right Or.inl
    · simpa [MantChar] using (hexNum_chars (by simpa using hr) c hc).imp_right Or.inl
  unfold Mant at h
  rcases h with ⟨h, -⟩ | ⟨p, rfl, h, -⟩ | ⟨p, f, n, v, rfl, hp, hf, -, -⟩
  · exact hR h
  · intro c hc; simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hR h c hc
    · simp [MantChar]
  · intro c hc; simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact hR hp c hc
    · simp [MantChar]
    · exact hR hf c hc

theorem mant_head {hex : Bool} {cs : Chars} {m k : Nat} (h : Mant hex cs m k) :
    ∃ c t, cs = c :: t ∧ (if hex then IsHexDigit c else IsDigit c) := by
  have hR : ∀ {cs n}, (if hex then HexNum else Num) cs n →
      ∃ c t, cs = c :: t ∧ (if hex then IsHexDigit c else IsDigit c) := by
    intro cs n hr
    cases hex
    · simpa using num_head (by simpa using hr)
    · simpa using hexNum_head (by simpa using hr)
  unfold Mant at h
  rcases h with ⟨h, -⟩ | ⟨p, rfl, h, -⟩ | ⟨p, f, n, v, rfl, hp, hf, -, -⟩
  · exact hR h
  · obtain ⟨c, t, rfl, hc⟩ := hR h; exact ⟨c, _, rfl, hc⟩
  · obtain ⟨c, t, rfl, hc⟩ := hR hp; exact ⟨c, _, rfl, hc⟩

theorem expPart_functional {hex : Bool} {cs : Chars} {e e' : Int} (h : ExpPart hex cs e)
    (h' : ExpPart hex cs e') : e = e' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨mark, sc, ds, s, n, rfl, -, hs, hn, rfl⟩ <;>
    rcases h' with ⟨e1, rfl⟩ | ⟨mark', sc', ds', s', n', e1, -, hs', hn', rfl⟩
  · rfl
  · simp at e1
  · simp at e1
  · simp only [List.cons.injEq] at e1
    obtain ⟨rfl, e1⟩ := e1
    have nosign : ∀ {ds : Chars} {n : Nat}, Num ds n → ∀ c ∈ ds.head?, c ≠ '+' ∧ c ≠ '-' := by
      intro ds n hn c hc
      obtain ⟨c', t, rfl, hc'⟩ := num_head hn
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc; subst hc
      constructor <;> (rintro rfl; simp [IsDigit] at hc')
    obtain ⟨rfl, rfl, rfl⟩ := sign_split hs hs' (nosign hn) (nosign hn') e1
    rw [num_functional hn hn']

/-- Characters of an exponent part. -/
theorem expPart_chars {hex : Bool} {cs : Chars} {e : Int} (h : ExpPart hex cs e) :
    ∀ c ∈ cs, c = 'e' ∨ c = 'E' ∨ c = 'p' ∨ c = 'P' ∨ c = '+' ∨ c = '-' ∨ IsDigit c ∨ c = '_' := by
  rcases h with ⟨rfl, -⟩ | ⟨mark, sc, ds, s, n, rfl, hm, hs, hn, -⟩
  · simp
  · intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc
    · cases hex <;> simp at hm <;> rcases hm with rfl | rfl <;> simp
    · rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hc <;> subst hc <;> simp
    · rcases num_chars hn c hc with h | h <;> simp [h]

theorem expPart_head {hex : Bool} {cs : Chars} {e : Int} (h : ExpPart hex cs e) :
    ∀ c ∈ cs.head?, if hex then c = 'p' ∨ c = 'P' else c = 'e' ∨ c = 'E' := by
  rcases h with ⟨rfl, -⟩ | ⟨mark, sc, ds, s, n, rfl, hm, -, -, -⟩
  · simp
  · intro c hc; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
    subst hc; exact hm

theorem fmag_functional {cs : Chars} {v v' : FloatMag} (h : FMag cs v) (h' : FMag cs v') :
    v = v' := by
  -- characters of the decimal form
  have decChars : ∀ {mc ec : Chars} {m k : Nat} {e : Int}, Mant false mc m k →
      ExpPart false ec e → ∀ c ∈ mc ++ ec, c ≠ 'x' ∧ c ≠ 'i' ∧ c ≠ 'n' := by
    intro mc ec m k e hm he c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · have := mant_chars hm c hc
      simp only [MantChar, Bool.false_eq_true, ↓reduceIte, IsDigit] at this
      rcases this with ⟨h1, h2⟩ | rfl | rfl
      · refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert h2; decide)
      · decide
      · decide
    · rcases expPart_chars he c hc with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ | rfl
      all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert h2; decide))
  have splitP : ∀ {hex : Bool} {mc ec mc' ec' : Chars} {m k m' k' : Nat} {e e' : Int},
      Mant hex mc m k → ExpPart hex ec e → Mant hex mc' m' k' → ExpPart hex ec' e' →
      mc ++ ec = mc' ++ ec' → mc = mc' ∧ ec = ec' := by
    intro hex mc ec mc' ec' m k m' k' e e' hm he hm' he' eq
    refine munch (P := MantChar hex) (mant_chars hm) (mant_chars hm') ?_ ?_ eq
    · intro c hc
      have := expPart_head he c hc
      cases hex <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;>
        rcases this with rfl | rfl <;> simp [MantChar, IsDigit, IsHexDigit]
    · intro c hc
      have := expPart_head he' c hc
      cases hex <;> simp only [Bool.false_eq_true, ↓reduceIte] at this <;>
        rcases this with rfl | rfl <;> simp [MantChar, IsDigit, IsHexDigit]
  rcases h with ⟨mc, ec, m, k, e, rfl, hm, he, rfl⟩ | ⟨mc, ec, m, k, e, rfl, hm, he, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ds, n, rfl, hn, rfl⟩ <;>
    rcases h' with ⟨mc', ec', m', k', e', eq, hm', he', rfl⟩ |
      ⟨mc', ec', m', k', e', eq, hm', he', rfl⟩ | ⟨eq, rfl⟩ | ⟨eq, rfl⟩ | ⟨ds', n', eq, hn', rfl⟩
  all_goals
    have l_inf : "inf".toList = ['i', 'n', 'f'] := by decide
    have l_nan : "nan".toList = ['n', 'a', 'n'] := by decide
    have l_nanp : "nan:0x".toList = ['n', 'a', 'n', ':', '0', 'x'] := by decide
  -- dec/*
  · obtain ⟨rfl, rfl⟩ := splitP hm he hm' he' eq
    obtain ⟨rfl, rfl⟩ := mant_functional hm hm'
    rw [expPart_functional he he']
  · have hx : 'x' ∈ mc ++ ec := by rw [eq]; simp
    exact False.elim <| (decChars hm he 'x' hx).1 rfl
  · have hx : 'i' ∈ mc ++ ec := by rw [eq, l_inf]; simp
    exact False.elim <| (decChars hm he 'i' hx).2.1 rfl
  · have hx : 'n' ∈ mc ++ ec := by rw [eq, l_nan]; simp
    exact False.elim <| (decChars hm he 'n' hx).2.2 rfl
  · have hx : 'n' ∈ mc ++ ec := by rw [eq, l_nanp]; simp
    exact False.elim <| (decChars hm he 'n' hx).2.2 rfl
  -- hex/*
  · have hx : 'x' ∈ mc' ++ ec' := by rw [← eq]; simp
    exact False.elim <| (decChars hm' he' 'x' hx).1 rfl
  · simp only [List.cons.injEq, true_and] at eq
    obtain ⟨rfl, rfl⟩ := splitP hm he hm' he' eq
    obtain ⟨rfl, rfl⟩ := mant_functional hm hm'
    rw [expPart_functional he he']
  · rw [l_inf] at eq; simp at eq
  · rw [l_nan] at eq; simp at eq
  · rw [l_nanp] at eq; simp at eq
  -- inf/*
  · have hx : 'i' ∈ mc' ++ ec' := by rw [← eq, l_inf]; simp
    exact False.elim <| (decChars hm' he' 'i' hx).2.1 rfl
  · rw [l_inf] at eq; simp at eq
  · rfl
  · rw [l_inf, l_nan] at eq; simp at eq
  · rw [l_inf, l_nanp] at eq; simp at eq
  -- nan/*
  · have hx : 'n' ∈ mc' ++ ec' := by rw [← eq, l_nan]; simp
    exact False.elim <| (decChars hm' he' 'n' hx).2.2 rfl
  · rw [l_nan] at eq; simp at eq
  · rw [l_inf, l_nan] at eq; simp at eq
  · rfl
  · rw [l_nan, l_nanp] at eq; simp at eq
  -- nan:0x/*
  · have hx : 'n' ∈ mc' ++ ec' := by rw [← eq, l_nanp]; simp
    exact False.elim <| (decChars hm' he' 'n' hx).2.2 rfl
  · rw [l_nanp] at eq; simp at eq
  · rw [l_inf, l_nanp] at eq; simp at eq
  · rw [l_nan, l_nanp] at eq; simp at eq
  · simp only [List.append_cancel_left_eq] at eq
    subst eq; rw [hexNum_functional hn hn']


theorem fmag_head_nosign {cs : Chars} {v : FloatMag} (h : FMag cs v) :
    ∀ c ∈ cs.head?, c ≠ '+' ∧ c ≠ '-' := by
  rcases h with ⟨mc, ec, m, k, e, rfl, hm, -, -⟩ | ⟨mc, ec, m, k, e, rfl, -, -, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨ds, n, rfl, -, -⟩
  · obtain ⟨c, t, rfl, hc⟩ := mant_head hm
    intro c' hc'; simp only [List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hc'; subst hc'
    simp only [Bool.false_eq_true, ↓reduceIte, IsDigit] at hc
    constructor <;> (rintro rfl; revert hc; decide)
  all_goals (intro c hc; simp at hc; subst hc; decide)

theorem fn_functional {t : FloatType} {cs : Chars} {b b' : BitVec t.width} (h : FN t cs b)
    (h' : FN t cs b') : b = b' := by
  obtain ⟨sc, mc, s, v, n, rfl, hs, hv, hn, rfl⟩ := h
  obtain ⟨sc', mc', s', v', n', e, hs', hv', hn', rfl⟩ := h'
  obtain ⟨rfl, rfl, rfl⟩ := sign_split hs hs' (fmag_head_nosign hv) (fmag_head_nosign hv') e
  obtain rfl := fmag_functional hv hv'
  rw [hn] at hn'; cases hn'; rfl

theorem atomF_functional {t : FloatType} {x : SExp} {b b' : BitVec t.width} (h : AtomF t x b)
    (h' : AtomF t x b') : b = b' := by
  obtain ⟨s, rfl, h⟩ := h
  obtain ⟨s', e, h'⟩ := h'
  simp only [K_inj] at e; subst e
  exact fn_functional h h'

/-! ## Names and indices -/

theorem name_functional {x : SExp} {n n' : String} (h : Name x n) (h' : Name x n') : n = n' := by
  obtain ⟨bs, rfl, h⟩ := h
  obtain ⟨bs', e, h'⟩ := h'
  simp only [Formats.SExp2.atom.injEq, Atom.str.injEq] at e; subst e
  rw [h] at h'; cases h'; rfl

theorem idOpt_functional {xs : List SExp} {id id' : Option String} (h : IdOpt xs id)
    (h' : IdOpt xs id') : id = id' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨n, rfl, rfl⟩ <;> rcases h' with ⟨e, rfl⟩ | ⟨n', e, rfl⟩
  · rfl
  · simp at e
  · simp at e
  · simp at e; rw [e]

theorem distinct_lookup_unique :
    ∀ {names : List (Option String)} {n : String} {i j : Nat}, Distinct names →
      names[i]? = some (some n) → names[j]? = some (some n) → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | a :: names, n, i, j, hd, hi, hj => by
      unfold Distinct at hd
      cases i <;> cases j
      · rfl
      · rename_i j
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hi
        simp only [List.filterMap_cons, id_eq, List.nodup_cons, List.mem_filterMap] at hd
        exact absurd ⟨_, List.mem_of_getElem? hj, rfl⟩ hd.1
      · rename_i i
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hj
        simp only [List.filterMap_cons, id_eq, List.nodup_cons, List.mem_filterMap] at hd
        exact absurd ⟨_, List.mem_of_getElem? hi, rfl⟩ hd.1
      · rename_i i j
        simp only [List.getElem?_cons_succ] at hi hj
        have hd' : Distinct names := by
          unfold Distinct
          cases a <;> simp_all
        rw [distinct_lookup_unique hd' hi hj]

theorem idxIn_functional {names : List (Option String)} (hd : Distinct names) {x : SExp}
    {i j : Nat} (h : IdxIn names x i) (h' : IdxIn names x j) : i = j := by
  rcases h with h | ⟨n, rfl, hi⟩ <;> rcases h' with h' | ⟨n', e, hj⟩
  · exact atomU_functional h h'
  · obtain ⟨t, e', -⟩ := h; rw [e'] at e; simp at e
  · obtain ⟨t, e', -⟩ := h'; simp at e'
  · simp only [Formats.SExp2.atom.injEq, Atom.id.injEq] at e; subst e
    exact distinct_lookup_unique hd hi hj

theorem idx_functional {names : List (Option String)} (hd : Distinct names) {k : IndexKind}
    {x : SExp} {i j : Wasm.Idx k} (h : Idx names x i) (h' : Idx names x j) : i = j :=
  Wasm.Idx.toNat_injective (idxIn_functional hd h h')

theorem optIdx_functional {names : List (Option String)} (hd : Distinct names) {k : IndexKind}
    {xs : List SExp} {i j : Wasm.Idx k} (h : OptIdx names xs i) (h' : OptIdx names xs j) :
    i = j := by
  rcases h with ⟨rfl, hi⟩ | ⟨x, rfl, hi⟩ <;> rcases h' with ⟨e, hj⟩ | ⟨y, e, hj⟩
  · exact Wasm.Idx.toNat_injective (hi.trans hj.symm)
  · simp at e
  · simp at e
  · simp only [List.cons.injEq, and_true] at e; subst e; exact idx_functional hd hi hj

/-! ## Item shapes -/

/-- A bare token starting with a decimal digit (numerals). -/
def NumTok (x : SExp) : Prop := ∃ t, x = K t ∧ ∃ c ∈ t.toList.head?, IsDigit c

/-- An identifier atom. -/
def IdAtom (x : SExp) : Prop := ∃ n, x = .atom (.id n)

/-- A keyword not starting with a digit. -/
def AlphaKw (s : String) : Prop :=
  match s.toList with
  | [] => True
  | c :: _ => ¬ IsDigit c

instance (s : String) : Decidable (AlphaKw s) := by
  unfold AlphaKw; split <;> infer_instance

theorem atomU_numTok {N : Nat} {x : SExp} {n : Nat} (h : AtomU N x n) : NumTok x := by
  obtain ⟨t, rfl, h⟩ := h
  obtain ⟨c, r, e, hc⟩ := un_head h
  exact ⟨t, rfl, c, by simp [e], hc⟩

theorem idxIn_shape {names : List (Option String)} {x : SExp} {i : Nat} (h : IdxIn names x i) :
    NumTok x ∨ IdAtom x := by
  rcases h with h | ⟨n, rfl, -⟩
  · exact .inl (atomU_numTok h)
  · exact .inr ⟨n, rfl⟩

theorem idx_shape {names : List (Option String)} {k : IndexKind} {x : SExp} {i : Wasm.Idx k}
    (h : Idx names x i) : NumTok x ∨ IdAtom x := idxIn_shape h

theorem not_numTok_K {s : String} (hs : AlphaKw s) : ¬ NumTok (K s) := by
  rintro ⟨t, e, c, hc, hd⟩
  simp only [K_inj] at e; subst e
  unfold AlphaKw at hs
  revert hs hc
  generalize s.toList = l
  cases l with
  | nil => simp
  | cons c' l =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq]
      intro h1 h2; subst h2; exact h1 hd

@[simp] theorem not_idAtom_K {s : String} : ¬ IdAtom (K s) := by
  rintro ⟨n, e⟩; simp [K, kw] at e

@[simp] theorem not_idAtom_L {y : SExp} {ys : List SExp} : ¬ IdAtom (L (y :: ys)) := by
  rintro ⟨n, e⟩; simp [L, listOf] at e

@[simp] theorem not_numTok_L {y : SExp} {ys : List SExp} : ¬ NumTok (L (y :: ys)) := by
  rintro ⟨t, e, -⟩; simp [L, listOf, K, kw] at e

@[simp] theorem not_numTok_id {n : String} : ¬ NumTok (Formats.SExp2.atom (Atom.id n)) := by
  rintro ⟨t, e, -⟩; simp [K, kw] at e

theorem not_idxIn_K {names : List (Option String)} {s : String} {i : Nat} (hs : AlphaKw s) :
    ¬ IdxIn names (K s) i := by
  intro h; rcases idxIn_shape h with h | h
  · exact not_numTok_K hs h
  · exact not_idAtom_K h

theorem not_idx_K {names : List (Option String)} {k : IndexKind} {s : String} {i : Wasm.Idx k}
    (hs : AlphaKw s) : ¬ Idx names (K s) i := not_idxIn_K hs

theorem not_idxIn_L {names : List (Option String)} {y : SExp} {ys : List SExp} {i : Nat} :
    ¬ IdxIn names (L (y :: ys)) i := by
  intro h; rcases idxIn_shape h with h | h
  · exact not_numTok_L h
  · exact not_idAtom_L h

theorem not_idx_L {names : List (Option String)} {k : IndexKind} {y : SExp} {ys : List SExp}
    {i : Wasm.Idx k} : ¬ Idx names (L (y :: ys)) i := not_idxIn_L

/-- A list item with a given head keyword. -/
def HeadKw (s : String) (x : SExp) : Prop := ∃ ys, x = L (K s :: ys)

theorem headKw_ne {s t : String} {x : SExp} (hst : s ≠ t) (hs : HeadKw s x) : ¬ HeadKw t x := by
  rintro ⟨ys', rfl⟩
  obtain ⟨ys, e⟩ := hs
  simp only [L_inj, List.cons.injEq, K_inj] at e
  exact hst e.1.symm

@[simp] theorem headKw_K {s t : String} : ¬ HeadKw s (K t) := by
  rintro ⟨ys, e⟩; simp at e

@[simp] theorem headKw_id {s n : String} : ¬ HeadKw s (Formats.SExp2.atom (Atom.id n)) := by
  rintro ⟨ys, e⟩; simp [L, listOf] at e

theorem headKw_L_iff {s t : String} {ys : List SExp} : HeadKw s (L (K t :: ys)) ↔ s = t := by
  constructor
  · rintro ⟨zs, e⟩; simp only [L_inj, List.cons.injEq, K_inj] at e; exact e.1.symm
  · rintro rfl; exact ⟨ys, rfl⟩

theorem not_numTok_of_headKw {s : String} {x : SExp} (h : HeadKw s x) : ¬ NumTok x := by
  obtain ⟨ys, rfl⟩ := h; exact not_numTok_L

theorem not_idAtom_of_headKw {s : String} {x : SExp} (h : HeadKw s x) : ¬ IdAtom x := by
  obtain ⟨ys, rfl⟩ := h; exact not_idAtom_L

/-! ## Value types -/

def numKws : List String := ["i32", "i64", "f32", "f64"]

def heapKws : List String :=
  ["any", "eq", "i31", "struct", "array", "none", "func", "nofunc", "exn", "noexn", "extern",
    "noextern"]

def refAbbrevKws : List String :=
  ["anyref", "eqref", "i31ref", "structref", "arrayref", "nullref", "funcref", "nullfuncref",
    "exnref", "nullexnref", "externref", "nullexternref"]

theorem numTypeKw_mem {s : String} {n : NumType} (h : numTypeKw s = some n) : s ∈ numKws := by
  unfold numTypeKw at h
  split at h <;> simp_all [numKws]

theorem absHeapKw_mem {s : String} {a : AbsHeapType} (h : absHeapKw s = some a) : s ∈ heapKws := by
  unfold absHeapKw at h
  split at h <;> simp_all [heapKws]

theorem refAbbrevKw_mem {s : String} {a : AbsHeapType} (h : refAbbrevKw s = some a) :
    s ∈ refAbbrevKws := by
  unfold refAbbrevKw at h
  split at h <;> simp_all [refAbbrevKws]

theorem heapKws_alpha : ∀ s ∈ heapKws, AlphaKw s := by decide

theorem heapTypeT_K {I : IdCtx} {s : String} {h : HeapType} (hh : HeapTypeT I (K s) h) :
    s ∈ heapKws ∨ ¬ AlphaKw s := by
  rcases hh with ⟨s', a, e, ha, -⟩ | ⟨i, hi, -⟩
  · simp only [K_inj] at e; subst e; exact .inl (absHeapKw_mem ha)
  · exact .inr fun hs => not_idxIn_K hs hi

theorem heapTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {h h' : HeapType}
    (hh : HeapTypeT I x h) (hh' : HeapTypeT I x h') : h = h' := by
  rcases hh with ⟨s, a, rfl, ha, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases hh' with ⟨s', a', e, ha', rfl⟩ | ⟨i', hi', rfl⟩
  · simp only [K_inj] at e; subst e; rw [ha] at ha'; cases ha'; rfl
  · exact absurd hi' (not_idx_K (heapKws_alpha _ (absHeapKw_mem ha)))
  · subst e; exact absurd hi (not_idx_K (heapKws_alpha _ (absHeapKw_mem ha')))
  · rw [idx_functional hT hi hi']

theorem refTypeT_shape {I : IdCtx} {x : SExp} {r : RefType} (h : RefTypeT I x r) :
    HeadKw "ref" x ∨ ∃ s, x = K s ∧ s ∈ refAbbrevKws := by
  rcases h with ⟨ht, h, rfl, -, -⟩ | ⟨ht, h, rfl, -, -⟩ | ⟨s, a, rfl, ha, -⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨s, rfl, refAbbrevKw_mem ha⟩

theorem refTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {r r' : RefType}
    (h : RefTypeT I x r) (h' : RefTypeT I x r') : r = r' := by
  rcases h with ⟨ht, h, rfl, hh, rfl⟩ | ⟨ht, h, rfl, hh, rfl⟩ | ⟨s, a, rfl, ha, rfl⟩ <;>
    rcases h' with ⟨ht', h', e, hh', rfl⟩ | ⟨ht', h', e, hh', rfl⟩ | ⟨s', a', e, ha', rfl⟩
  all_goals simp at e
  · subst e; rw [heapTypeT_functional hT hh hh']
  · subst e; rw [heapTypeT_functional hT hh hh']
  · subst e; rw [ha] at ha'; cases ha'; rfl

theorem valTypeT_shape {I : IdCtx} {x : SExp} {t : ValType} (h : ValTypeT I x t) :
    HeadKw "ref" x ∨ ∃ s, x = K s ∧ (s ∈ numKws ∨ s = "v128" ∨ s ∈ refAbbrevKws) := by
  rcases h with ⟨s, n, rfl, hn, -⟩ | ⟨rfl, -⟩ | ⟨r, hr, -⟩
  · exact .inr ⟨s, rfl, .inl (numTypeKw_mem hn)⟩
  · exact .inr ⟨_, rfl, .inr (.inl rfl)⟩
  · rcases refTypeT_shape hr with h | ⟨s, rfl, hs⟩
    · exact .inl h
    · exact .inr ⟨s, rfl, .inr (.inr hs)⟩

theorem valTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {t t' : ValType}
    (h : ValTypeT I x t) (h' : ValTypeT I x t') : t = t' := by
  have hNR : ∀ s ∈ numKws, s ∉ refAbbrevKws := by decide
  have hVR : "v128" ∉ refAbbrevKws := by decide
  rcases h with ⟨s, n, rfl, hn, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r, hr, rfl⟩ <;>
    rcases h' with ⟨s', n', e, hn', rfl⟩ | ⟨e, rfl⟩ | ⟨r', hr', rfl⟩
  · simp only [K_inj] at e; subst e; rw [hn] at hn'; cases hn'; rfl
  · simp only [K_inj] at e; subst e; simp [numTypeKw] at hn
  · rcases refTypeT_shape hr' with ⟨ys, e⟩ | ⟨s', e, hs'⟩
    · simp at e
    · simp only [K_inj] at e; subst e; exact absurd hs' (hNR _ (numTypeKw_mem hn))
  · simp only [K_inj] at e; subst e; simp [numTypeKw] at hn'
  · rfl
  · rcases refTypeT_shape hr' with ⟨ys, e⟩ | ⟨s', e, hs'⟩
    · simp at e
    · simp only [K_inj] at e; subst e; exact absurd hs' hVR
  · subst e
    rcases refTypeT_shape hr with h | ⟨s'', e, hs'⟩
    · exact absurd h headKw_K
    · simp only [K_inj] at e; subst e; exact absurd hs' (hNR _ (numTypeKw_mem hn'))
  · subst e
    rcases refTypeT_shape hr with h | ⟨s'', e, hs'⟩
    · exact absurd h headKw_K
    · simp only [K_inj] at e; subst e; exact absurd hs' hVR
  · rw [refTypeT_functional hT hr hr']

theorem not_valTypeT_id {I : IdCtx} {n : String} {t : ValType} :
    ¬ ValTypeT I (Formats.SExp2.atom (Atom.id n)) t := by
  intro h
  rcases valTypeT_shape h with h | ⟨s, e, -⟩
  · exact headKw_id h
  · simp [K, kw] at e

/-! ## Type definitions -/

theorem storageTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {z z' : StorageType} (h : StorageTypeT I x z) (h' : StorageTypeT I x z') : z = z' := by
  have notVal : ∀ {s : String} {t : ValType}, s = "i8" ∨ s = "i16" → ¬ ValTypeT I (K s) t := by
    intro s t hs hv
    rcases valTypeT_shape hv with h | ⟨s', e, hs'⟩
    · exact headKw_K h
    · simp only [K_inj] at e; subst e; rcases hs with rfl | rfl <;> revert hs' <;> decide
  rcases h with ⟨t, ht, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨t', ht', rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
  · rw [valTypeT_functional hT ht ht']
  · subst e; exact absurd ht (notVal (.inl rfl))
  · subst e; exact absurd ht (notVal (.inr rfl))
  · exact absurd ht' (notVal (.inl rfl))
  · rfl
  · simp at e
  · exact absurd ht' (notVal (.inr rfl))
  · simp at e
  · rfl

theorem storageTypeT_shape {I : IdCtx} {x : SExp} {z : StorageType} (h : StorageTypeT I x z) :
    HeadKw "ref" x ∨ ∃ s, x = K s := by
  rcases h with ⟨t, ht, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rcases valTypeT_shape ht with h | ⟨s, rfl, -⟩
    · exact .inl h
    · exact .inr ⟨s, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem fieldTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {f f' : FieldType}
    (h : FieldTypeT I x f) (h' : FieldTypeT I x f') : f = f' := by
  rcases h with ⟨z, hz, rfl⟩ | ⟨zx, z, rfl, hz, rfl⟩ <;>
    rcases h' with ⟨z', hz', rfl⟩ | ⟨zx', z', e, hz', rfl⟩
  · rw [storageTypeT_functional hT hz hz']
  · subst e; rcases storageTypeT_shape hz with h | ⟨s, e⟩
    · exact absurd h (headKw_ne (by decide) ⟨_, rfl⟩)
    · simp at e
  · rcases storageTypeT_shape hz' with h | ⟨s, e⟩
    · exact absurd h (headKw_ne (by decide) ⟨_, rfl⟩)
    · simp at e
  · simp only [L_inj, List.cons.injEq, and_true, true_and] at e; subst e
    rw [storageTypeT_functional hT hz hz']

theorem not_fieldTypeT_id {I : IdCtx} {n : String} {f : FieldType} :
    ¬ FieldTypeT I (Formats.SExp2.atom (Atom.id n)) f := by
  rintro (⟨z, hz, -⟩ | ⟨zx, z, e, -⟩)
  · rcases storageTypeT_shape hz with h | ⟨s, e⟩
    · exact headKw_id h
    · simp [K, kw] at e
  · simp [L, listOf] at e

theorem fieldT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {fs fs' : List (FieldType × Option String)} (h : FieldT I x fs) (h' : FieldT I x fs') :
    fs = fs' := by
  rcases h with ⟨n, fx, f, rfl, hf, rfl⟩ | ⟨fxs, ts, rfl, hts, rfl⟩ <;>
    rcases h' with ⟨n', fx', f', e, hf', rfl⟩ | ⟨fxs', ts', e, hts', rfl⟩
  · simp only [L_inj, List.cons.injEq, Formats.SExp2.atom.injEq, Atom.id.injEq, and_true,
      true_and] at e
    obtain ⟨rfl, rfl⟩ := e; rw [fieldTypeT_functional hT hf hf']
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts' with | cons h _ => exact absurd h not_fieldTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts with | cons h _ => exact absurd h not_fieldTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    rw [forall₂_functional (R := FieldTypeT I) (fun _ _ _ h h' => fieldTypeT_functional hT h h') hts hts']

theorem paramT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {ps ps' : List (ValType × Option String)} (h : ParamT I x ps) (h' : ParamT I x ps') :
    ps = ps' := by
  rcases h with ⟨n, tx, t, rfl, ht, rfl⟩ | ⟨txs, ts, rfl, hts, rfl⟩ <;>
    rcases h' with ⟨n', tx', t', e, ht', rfl⟩ | ⟨txs', ts', e, hts', rfl⟩
  · simp only [L_inj, List.cons.injEq, Formats.SExp2.atom.injEq, Atom.id.injEq, and_true,
      true_and] at e
    obtain ⟨rfl, rfl⟩ := e; rw [valTypeT_functional hT ht ht']
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts' with | cons h _ => exact absurd h not_valTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts with | cons h _ => exact absurd h not_valTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    rw [forall₂_functional (R := ValTypeT I) (fun _ _ _ h h' => valTypeT_functional hT h h') hts hts']

theorem resultT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {ts ts' : List ValType}
    (h : ResultT I x ts) (h' : ResultT I x ts') : ts = ts' := by
  obtain ⟨txs, rfl, h⟩ := h
  obtain ⟨txs', e, h'⟩ := h'
  simp only [L_inj, List.cons.injEq, true_and] at e; subst e
  exact forall₂_functional (R := ValTypeT I) (fun _ _ _ h h' => valTypeT_functional hT h h') h h'

theorem concat_functional {α : Type} {R : SExp → List α → Prop}
    (hR : ∀ x a a', R x a → R x a' → a = a') {xs : List SExp} {as as' : List α}
    (h : Concat R xs as) (h' : Concat R xs as') : as = as' := by
  obtain ⟨ass, h, rfl, -⟩ := h
  obtain ⟨ass', h', rfl, -⟩ := h'
  rw [forall₂_functional hR h h']

theorem concat_mem {α : Type} {R : SExp → List α → Prop} {P : SExp → Prop}
    (hR : ∀ x a, R x a → P x) {xs : List SExp} {as : List α} (h : Concat R xs as) :
    ∀ x ∈ xs, P x := by
  obtain ⟨ass, h, -, -⟩ := h
  exact forall₂_mem_left hR h

theorem paramT_head {I : IdCtx} {x : SExp} {ps : List (ValType × Option String)}
    (h : ParamT I x ps) : HeadKw "param" x := by
  rcases h with ⟨n, tx, t, rfl, -, -⟩ | ⟨txs, ts, rfl, -, -⟩ <;> exact ⟨_, rfl⟩

theorem resultT_head {I : IdCtx} {x : SExp} {ts : List ValType} (h : ResultT I x ts) :
    HeadKw "result" x := by
  obtain ⟨txs, rfl, -⟩ := h; exact ⟨_, rfl⟩

/-- Params and results split uniquely. -/
theorem params_results_split {I I' : IdCtx} {pxs rxs pxs' rxs' : List SExp}
    {ps : List (ValType × Option String)} {rs : List ValType}
    {ps' : List (ValType × Option String)} {rs' : List ValType}
    (hp : Concat (ParamT I) pxs ps) (hr : Concat (ResultT I) rxs rs)
    (hp' : Concat (ParamT I') pxs' ps') (hr' : Concat (ResultT I') rxs' rs')
    (e : pxs ++ rxs = pxs' ++ rxs') : pxs = pxs' ∧ rxs = rxs' := by
  refine munch (P := HeadKw "param") (concat_mem (R := ParamT _) (fun _ _ h => paramT_head h) hp)
    (concat_mem (R := ParamT _) (fun _ _ h => paramT_head h) hp') ?_ ?_ e
  · intro x hx
    exact headKw_ne (by decide)
      (concat_mem (R := ResultT _) (fun _ _ h => resultT_head h) hr x (List.mem_of_mem_head? hx))
  · intro x hx
    exact headKw_ne (by decide)
      (concat_mem (R := ResultT _) (fun _ _ h => resultT_head h) hr' x (List.mem_of_mem_head? hx))

theorem compTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {ct ct' : CompositeType} {ns ns' : List (Option String)} (h : CompTypeT I x ct ns)
    (h' : CompTypeT I x ct' ns') : ct = ct' ∧ ns = ns' := by
  rcases h with ⟨fxs, fs, rfl, hfs, rfl, rfl⟩ | ⟨fx, f, rfl, hf, rfl, rfl⟩ |
      ⟨pxs, rxs, ps, rs, rfl, hp, hr, rfl, rfl⟩ <;>
    rcases h' with ⟨fxs', fs', e, hfs', rfl, rfl⟩ | ⟨fx', f', e, hf', rfl, rfl⟩ |
      ⟨pxs', rxs', ps', rs', e, hp', hr', rfl, rfl⟩
  all_goals simp at e
  · subst e; rw [concat_functional (R := FieldT I) (fun _ _ _ h h' => fieldT_functional hT h h') hfs hfs']; simp
  · subst e; rw [fieldTypeT_functional hT hf hf']; simp
  · obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    rw [concat_functional (R := ParamT I) (fun _ _ _ h h' => paramT_functional hT h h') hp hp',
      concat_functional (R := ResultT I) (fun _ _ _ h h' => resultT_functional hT h h') hr hr']
    simp

theorem compTypeT_head {I : IdCtx} {x : SExp} {ct : CompositeType} {ns : List (Option String)}
    (h : CompTypeT I x ct ns) : HeadKw "struct" x ∨ HeadKw "array" x ∨ HeadKw "func" x := by
  rcases h with ⟨fxs, fs, rfl, -⟩ | ⟨fx, f, rfl, -⟩ | ⟨pxs, rxs, ps, rs, rfl, -⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr ⟨_, rfl⟩)

theorem compTypeT_not_sub {I : IdCtx} {x : SExp} {ct : CompositeType} {ns : List (Option String)}
    (h : CompTypeT I x ct ns) : ¬ HeadKw "sub" x := by
  rcases compTypeT_head h with h | h | h <;> exact headKw_ne (by decide) h

theorem subTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {st st' : SubType}
    {ns ns' : List (Option String)} (h : SubTypeT I x st ns) (h' : SubTypeT I x st' ns') :
    st = st' ∧ ns = ns' := by
  have hidx : ∀ {xs : List SExp} {is : List TypeIdx}, List.Forall₂ (Idx I.types) xs is →
      ∀ x ∈ xs, NumTok x ∨ IdAtom x := fun h => forall₂_mem_left (fun _ _ h => idx_shape h) h
  have hf : ∀ {fin : List SExp}, (fin = [] ∨ fin = [K "final"]) → ∀ x ∈ fin, x = K "final" := by
    rintro fin (rfl | rfl) <;> simp
  have hnext : ∀ {xs : List SExp} {is : List TypeIdx} {cx : SExp} {ct : CompositeType}
      {ns : List (Option String)}, List.Forall₂ (Idx I.types) xs is → CompTypeT I cx ct ns →
      ∀ y ∈ (xs ++ [cx]).head?, ¬ y = K "final" := by
    intro xs is cx ct ns his hct y hy
    cases xs with
    | nil =>
        simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        rintro rfl
        rcases compTypeT_head hct with h | h | h <;> exact headKw_K h
    | cons z zs =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        rcases hidx his z (by simp) with h | h
        · rintro rfl; exact not_numTok_K (s := "final") (by decide) h
        · rintro rfl; exact not_idAtom_K h
  rcases h with ⟨fin, xs, cx, is, ct, rfl, hfin, his, -, hct, rfl⟩ | ⟨ct, hct, rfl⟩ <;>
    rcases h' with ⟨fin', xs', cx', is', ct', e, hfin', his', -, hct', rfl⟩ | ⟨ct', hct', rfl⟩
  · simp only [L_inj, List.cons.injEq, true_and] at e
    have e2 : fin ++ (xs ++ [cx]) = fin' ++ (xs' ++ [cx']) := by simpa using e
    obtain ⟨rfl, e3⟩ := munch (P := fun x => x = K "final") (hf hfin) (hf hfin')
      (hnext his hct) (hnext his' hct') e2
    obtain ⟨rfl, h4⟩ := List.append_inj' e3 rfl
    simp only [List.cons.injEq, and_true] at h4; subst h4
    obtain ⟨rfl, rfl⟩ := compTypeT_functional hT hct hct'
    rw [forall₂_functional (R := Idx I.types) (fun _ _ _ h h' => idx_functional hT h h') his his']
    exact ⟨rfl, rfl⟩
  · exact absurd ⟨_, rfl⟩ (compTypeT_not_sub hct')
  · subst e; exact absurd ⟨_, rfl⟩ (compTypeT_not_sub hct)
  · obtain ⟨rfl, rfl⟩ := compTypeT_functional hT hct hct'; exact ⟨rfl, rfl⟩

theorem typeDefT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {st st' : SubType}
    {id id' : Option String} {ns ns' : List (Option String)} (h : TypeDefT I x st id ns)
    (h' : TypeDefT I x st' id' ns') : st = st' ∧ id = id' ∧ ns = ns' := by
  obtain ⟨ix, sx, rfl, hix, hsx⟩ := h
  obtain ⟨ix', sx', e, hix', hsx'⟩ := h'
  simp only [L_inj, List.cons.injEq, true_and] at e
  obtain ⟨rfl, h2⟩ := List.append_inj' e rfl
  simp only [List.cons.injEq, and_true] at h2; subst h2
  obtain ⟨rfl, rfl⟩ := subTypeT_functional hT hsx hsx'
  exact ⟨rfl, idOpt_functional hix hix', rfl⟩

theorem typeDefT_head {I : IdCtx} {x : SExp} {st : SubType} {id : Option String}
    {ns : List (Option String)} (h : TypeDefT I x st id ns) : HeadKw "type" x := by
  obtain ⟨ix, sx, rfl, -⟩ := h; exact ⟨_, rfl⟩

theorem recTypeT_head {I : IdCtx} {x : SExp} {rt : RecType} {J : IdCtx} (h : RecTypeT I x rt J) :
    HeadKw "rec" x ∨ HeadKw "type" x := by
  rcases h with ⟨dxs, defs, rfl, -⟩ | ⟨st, id, ns, hd, -, -⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr (typeDefT_head hd)

theorem recTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp} {rt rt' : RecType}
    {J J' : IdCtx} (h : RecTypeT I x rt J) (h' : RecTypeT I x rt' J') : rt = rt' ∧ J = J' := by
  have defs_eq : ∀ {dxs : List SExp}
      {defs defs' : List (SubType × Option String × List (Option String))},
      List.Forall₂ (fun dx (d : SubType × Option String × List (Option String)) =>
        TypeDefT I dx d.1 d.2.1 d.2.2) dxs defs →
      List.Forall₂ (fun dx (d : SubType × Option String × List (Option String)) =>
        TypeDefT I dx d.1 d.2.1 d.2.2) dxs defs' → defs = defs' := by
    intro dxs defs defs' h h'
    refine forall₂_functional (fun dx d d' hd hd' => ?_) h h'
    obtain ⟨h1, h2, h3⟩ := typeDefT_functional hT hd hd'
    exact Prod.ext h1 (Prod.ext h2 h3)
  rcases h with ⟨dxs, defs, rfl, hd, -, rfl, rfl⟩ | ⟨st, id, ns, hd, rfl, rfl⟩ <;>
    rcases h' with ⟨dxs', defs', e, hd', -, rfl, rfl⟩ | ⟨st', id', ns', hd', rfl, rfl⟩
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    rw [defs_eq hd hd']; exact ⟨rfl, rfl⟩
  · exact absurd (typeDefT_head hd') (headKw_ne (by decide) ⟨_, rfl⟩)
  · subst e; exact absurd (typeDefT_head hd) (headKw_ne (by decide) ⟨_, rfl⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := typeDefT_functional hT hd hd'; exact ⟨rfl, rfl⟩


/-! ## External types -/

/-- An identifier-free head: the rest of an item list does not start with an
identifier. -/
def NotIdHead (xs : List SExp) : Prop := ∀ x ∈ xs.head?, ¬ IdAtom x

theorem idOpt_mem {xs : List SExp} {id : Option String} (h : IdOpt xs id) : ∀ x ∈ xs, IdAtom x := by
  rcases h with ⟨rfl, -⟩ | ⟨n, rfl, -⟩
  · simp
  · intro x hx; simp only [List.mem_singleton] at hx; exact ⟨n, hx⟩

/-- Splitting off an optional identifier. -/
theorem idOpt_split {ix ix' r r' : List SExp} {id id' : Option String} (h : IdOpt ix id)
    (h' : IdOpt ix' id') (hr : NotIdHead r) (hr' : NotIdHead r') (e : ix ++ r = ix' ++ r') :
    ix = ix' ∧ id = id' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := munch (idOpt_mem h) (idOpt_mem h') hr hr' e
  exact ⟨rfl, idOpt_functional h h', rfl⟩

theorem notIdHead_of_forall {xs : List SExp} (h : ∀ x ∈ xs, ¬ IdAtom x) : NotIdHead xs :=
  fun x hx => h x (List.mem_of_mem_head? hx)

theorem notIdHead_nil : NotIdHead [] := by simp [NotIdHead]

theorem notIdHead_cons {x : SExp} {xs : List SExp} (h : ¬ IdAtom x) : NotIdHead (x :: xs) := by
  intro y hy; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy; subst hy; exact h

theorem notIdHead_append {xs ys : List SExp} (h : ∀ x ∈ xs, ¬ IdAtom x) (h' : NotIdHead ys) :
    NotIdHead (xs ++ ys) := by
  cases xs with
  | nil => simpa using h'
  | cons x xs => exact notIdHead_cons (h x (by simp))

/-- Address type keywords. -/
def AddrTok (x : SExp) : Prop := x = K "i32" ∨ x = K "i64"

theorem addrTypeT_mem {xs : List SExp} {a : AddrType} (h : AddrTypeT xs a) : ∀ x ∈ xs, AddrTok x := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [AddrTok]

theorem addrTypeT_functional {xs : List SExp} {a a' : AddrType} (h : AddrTypeT xs a)
    (h' : AddrTypeT xs a') : a = a' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp_all

theorem limitsT_mem {xs : List SExp} {l : Limits} (h : LimitsT xs l) :
    xs ≠ [] ∧ ∀ x ∈ xs, NumTok x := by
  rcases h with ⟨nx, n, rfl, hn, -⟩ | ⟨nx, mx, n, m, rfl, hn, hm, -⟩
  · refine ⟨by simp, ?_⟩; intro x hx; simp at hx; subst hx; exact atomU_numTok hn
  · refine ⟨by simp, ?_⟩; intro x hx; simp at hx
    rcases hx with rfl | rfl
    · exact atomU_numTok hn
    · exact atomU_numTok hm

theorem limitsT_functional {xs : List SExp} {l l' : Limits} (h : LimitsT xs l)
    (h' : LimitsT xs l') : l = l' := by
  rcases h with ⟨nx, n, rfl, hn, rfl⟩ | ⟨nx, mx, n, m, rfl, hn, hm, rfl⟩ <;>
    rcases h' with ⟨nx', n', e, hn', rfl⟩ | ⟨nx', mx', n', m', e, hn', hm', rfl⟩
  · simp only [List.cons.injEq, and_true] at e; subst e; rw [atomU64_functional hn hn']
  · simp at e
  · simp at e
  · simp only [List.cons.injEq, and_true] at e; obtain ⟨rfl, rfl⟩ := e
    rw [atomU64_functional hn hn', atomU64_functional hm hm']

theorem not_addrTok_of_numTok {x : SExp} (h : NumTok x) : ¬ AddrTok x := by
  rintro (rfl | rfl)
  · exact not_numTok_K (s := "i32") (by decide) h
  · exact not_numTok_K (s := "i64") (by decide) h

theorem addr_limits_split {ax lx ax' lx' r r' : List SExp} {a a' : AddrType} {l l' : Limits}
    (ha : AddrTypeT ax a) (hl : LimitsT lx l) (ha' : AddrTypeT ax' a') (hl' : LimitsT lx' l')
    (e : ax ++ (lx ++ r) = ax' ++ (lx' ++ r')) : ax = ax' ∧ lx ++ r = lx' ++ r' := by
  refine munch (addrTypeT_mem ha) (addrTypeT_mem ha') ?_ ?_ e
  · obtain ⟨hne, hnum⟩ := limitsT_mem hl
    cases lx with
    | nil => exact absurd rfl hne
    | cons y ys =>
        intro x hx; simp only [List.cons_append, List.head?_cons, Option.mem_def,
          Option.some.injEq] at hx; subst hx
        exact not_addrTok_of_numTok (hnum _ (by simp))
  · obtain ⟨hne, hnum⟩ := limitsT_mem hl'
    cases lx' with
    | nil => exact absurd rfl hne
    | cons y ys =>
        intro x hx; simp only [List.cons_append, List.head?_cons, Option.mem_def,
          Option.some.injEq] at hx; subst hx
        exact not_addrTok_of_numTok (hnum _ (by simp))

theorem memTypeT_functional {xs : List SExp} {m m' : MemoryType} (h : MemTypeT xs m)
    (h' : MemTypeT xs m') : m = m' := by
  obtain ⟨ax, lx, a, l, rfl, ha, hl, rfl⟩ := h
  obtain ⟨ax', lx', a', l', e, ha', hl', rfl⟩ := h'
  obtain ⟨rfl, e2⟩ := addr_limits_split (r := []) (r' := []) ha hl ha' hl' (by simpa using e)
  simp only [List.append_nil] at e2; subst e2
  rw [addrTypeT_functional ha ha', limitsT_functional hl hl']

theorem memTypeT_mem {xs : List SExp} {m : MemoryType} (h : MemTypeT xs m) :
    ∀ x ∈ xs, ∃ s, x = K s := by
  obtain ⟨ax, lx, a, l, rfl, ha, hl, -⟩ := h
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases addrTypeT_mem ha x hx with rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨t, rfl, -⟩ := (limitsT_mem hl).2 x hx; exact ⟨t, rfl⟩

theorem tableTypeT_functional {I : IdCtx} (hT : Distinct I.types) {xs : List SExp}
    {t t' : TableType} (h : TableTypeT I xs t) (h' : TableTypeT I xs t') : t = t' := by
  obtain ⟨ax, lx, rx, a, l, r, rfl, ha, hl, hr, rfl⟩ := h
  obtain ⟨ax', lx', rx', a', l', r', e, ha', hl', hr', rfl⟩ := h'
  obtain ⟨rfl, e2⟩ := addr_limits_split ha hl ha' hl' (by simpa using e)
  obtain ⟨rfl, h3⟩ := List.append_inj' e2 rfl
  simp only [List.cons.injEq, and_true] at h3; subst h3
  rw [addrTypeT_functional ha ha', limitsT_functional hl hl', refTypeT_functional hT hr hr']

theorem tableTypeT_notId {I : IdCtx} {xs : List SExp} {t : TableType} (h : TableTypeT I xs t) :
    ∀ x ∈ xs, ¬ IdAtom x := by
  obtain ⟨ax, lx, rx, a, l, r, rfl, ha, hl, hr, -⟩ := h
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · rcases addrTypeT_mem ha x hx with rfl | rfl <;> simp
  · obtain ⟨t, rfl, -⟩ := (limitsT_mem hl).2 x hx; simp
  · rcases refTypeT_shape hr with h | ⟨s, rfl, -⟩
    · exact not_idAtom_of_headKw h
    · simp

theorem valTypeT_notId {I : IdCtx} {x : SExp} {t : ValType} (h : ValTypeT I x t) : ¬ IdAtom x := by
  rcases valTypeT_shape h with h | ⟨s, rfl, -⟩
  · exact not_idAtom_of_headKw h
  · simp

theorem globalTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {g g' : GlobalType} (h : GlobalTypeT I x g) (h' : GlobalTypeT I x g') : g = g' := by
  rcases h with ⟨t, ht, rfl⟩ | ⟨tx, t, rfl, ht, rfl⟩ <;>
    rcases h' with ⟨t', ht', rfl⟩ | ⟨tx', t', e, ht', rfl⟩
  · rw [valTypeT_functional hT ht ht']
  · subst e; rcases valTypeT_shape ht with h | ⟨s, e, -⟩
    · exact absurd h (headKw_ne (by decide) ⟨_, rfl⟩)
    · simp at e
  · rcases valTypeT_shape ht' with h | ⟨s, e, -⟩
    · exact absurd h (headKw_ne (by decide) ⟨_, rfl⟩)
    · simp at e
  · simp only [L_inj, List.cons.injEq, and_true, true_and] at e; subst e
    rw [valTypeT_functional hT ht ht']

theorem globalTypeT_shape {I : IdCtx} {x : SExp} {g : GlobalType} (h : GlobalTypeT I x g) :
    HeadKw "ref" x ∨ HeadKw "mut" x ∨ ∃ s, x = K s := by
  rcases h with ⟨t, ht, -⟩ | ⟨tx, t, rfl, -, -⟩
  · rcases valTypeT_shape ht with h | ⟨s, rfl, -⟩
    · exact .inl h
    · exact .inr (.inr ⟨s, rfl⟩)
  · exact .inr (.inl ⟨_, rfl⟩)

theorem globalTypeT_notId {I : IdCtx} {x : SExp} {g : GlobalType} (h : GlobalTypeT I x g) :
    ¬ IdAtom x := by
  rcases globalTypeT_shape h with h | h | ⟨s, rfl⟩
  · exact not_idAtom_of_headKw h
  · exact not_idAtom_of_headKw h
  · simp

/-! ## Type uses -/

/-- Items of a type use: `(type …)`, `(param …)` and `(result …)`. -/
def TUList (x : SExp) : Prop := HeadKw "type" x ∨ HeadKw "param" x ∨ HeadKw "result" x

theorem tuList_notId {x : SExp} (h : TUList x) : ¬ IdAtom x := by
  rcases h with h | h | h <;> exact not_idAtom_of_headKw h

theorem tuList_notNum {x : SExp} (h : TUList x) : ¬ NumTok x := by
  rcases h with h | h | h <;> exact not_numTok_of_headKw h

theorem concat_nil {α : Type} {R : SExp → List α → Prop} {as : List α} (h : Concat R [] as) :
    as = [] := by
  obtain ⟨ass, h, rfl, -⟩ := h
  cases h; rfl

theorem typeDefIsFunc_functional {I : IdCtx} {x : TypeIdx} {ft ft' : FuncType}
    (h : TypeDefIsFunc I x ft) (h' : TypeDefIsFunc I x ft') : ft = ft' := by
  obtain ⟨rt, i, fin, sups, h1, h2⟩ := h
  obtain ⟨rt', i', fin', sups', h1', h2'⟩ := h'
  rw [h1] at h1'; simp only [Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  rw [h2] at h2'; simp only [Option.some.injEq, SubType.mk.injEq, CompositeType.func.injEq] at h2'
  exact h2'.2.2

theorem params_results_mem {I : IdCtx} {pxs rxs : List SExp}
    {ps : List (ValType × Option String)} {rs : List ValType}
    (hp : Concat (ParamT I) pxs ps) (hr : Concat (ResultT I) rxs rs) :
    ∀ x ∈ pxs ++ rxs, HeadKw "param" x ∨ HeadKw "result" x := by
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · exact .inl (concat_mem (R := ParamT I) (fun _ _ h => paramT_head h) hp x hx)
  · exact .inr (concat_mem (R := ResultT I) (fun _ _ h => resultT_head h) hr x hx)

theorem typeUseT_mem {I : IdCtx} {xs : List SExp} {x : TypeIdx} {ls : List (Option String)}
    {u : List FuncType} (h : TypeUseT I xs x ls u) : ∀ y ∈ xs, TUList y := by
  rcases h with ⟨tx, pxs, rxs, ft, rfl, hp, hr, -⟩ | ⟨tx, pxs, rxs, ft, ps, rs, rfl, -, -, hp, hr, -⟩ |
      ⟨pxs, rxs, ps, rs, rfl, hp, hr, -⟩
  · intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .inl ⟨_, rfl⟩
    · exact .inr (params_results_mem hp hr y hy)
  · intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .inl ⟨_, rfl⟩
    · exact .inr (params_results_mem hp hr y hy)
  · intro y hy; exact .inr (params_results_mem hp hr y hy)

theorem first_index_unique {α : Type} {l : List α} {a : α} {i j : Nat} (hi : l[i]? = some a)
    (hmi : ∀ k < i, l[k]? ≠ some a) (hj : l[j]? = some a) (hmj : ∀ k < j, l[k]? ≠ some a) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd hi (hmj i h)
  · exact h
  · exact absurd hj (hmi j h)

theorem typeUseT_functional {I : IdCtx} (hT : Distinct I.types) {xs : List SExp}
    {x x' : TypeIdx} {ls ls' : List (Option String)} {u u' : List FuncType}
    (h : TypeUseT I xs x ls u) (h' : TypeUseT I xs x' ls' u') : x = x' ∧ ls = ls' ∧ u = u' := by
  have noType : ∀ {pxs rxs : List SExp} {ps : List (ValType × Option String)}
      {rs : List ValType} {tx : SExp} {rest : List SExp}, Concat (ParamT I) pxs ps →
      Concat (ResultT I) rxs rs → L [K "type", tx] :: rest = pxs ++ rxs → False := by
    intro pxs rxs ps rs tx rest hp hr e
    have := params_results_mem hp hr (L [K "type", tx]) (by rw [← e]; simp)
    rcases this with h | h <;> exact headKw_ne (by decide) ⟨[tx], rfl⟩ h
  rcases h with ⟨tx, pxs, rxs, ft, rfl, hp, hr, hx, hft, rfl, rfl⟩ |
      ⟨tx, pxs, rxs, ft, ps, rs, rfl, hx, hft, hp, hr, rfl, rfl, -, rfl⟩ |
      ⟨pxs, rxs, ps, rs, rfl, hp, hr, hd, hmin, rfl, -, rfl⟩ <;>
    rcases h' with ⟨tx', pxs', rxs', ft', e, hp', hr', hx', hft', rfl, rfl⟩ |
      ⟨tx', pxs', rxs', ft', ps', rs', e, hx', hft', hp', hr', rfl, rfl, -, rfl⟩ |
      ⟨pxs', rxs', ps', rs', e, hp', hr', hd', hmin', rfl, -, rfl⟩
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e
    obtain ⟨rfl, -⟩ := e
    obtain rfl := idx_functional hT hx hx'
    rw [typeDefIsFunc_functional hft hft']; exact ⟨rfl, rfl, rfl⟩
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    obtain rfl := idx_functional hT hx hx'
    obtain rfl := concat_functional (R := ParamT I)
      (fun _ _ _ h h' => paramT_functional hT h h') hp hp'
    obtain rfl := concat_functional (R := ResultT I)
      (fun _ _ _ h h' => resultT_functional hT h h') hr hr'
    rw [typeDefIsFunc_functional hft hft']; exact ⟨rfl, rfl, rfl⟩
  · exact (noType hp' hr' e).elim
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    obtain rfl := idx_functional hT hx hx'
    obtain rfl := concat_functional (R := ParamT I)
      (fun _ _ _ h h' => paramT_functional hT h h') hp hp'
    obtain rfl := concat_functional (R := ResultT I)
      (fun _ _ _ h h' => resultT_functional hT h h') hr hr'
    obtain rfl := typeDefIsFunc_functional hft hft'; simp
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    obtain rfl := idx_functional hT hx hx'
    rw [concat_functional (R := ParamT I) (fun _ _ _ h h' => paramT_functional hT h h') hp hp']
    exact ⟨rfl, rfl, rfl⟩
  · exact (noType hp' hr' e).elim
  · exact (noType hp hr e.symm).elim
  · exact (noType hp hr e.symm).elim
  · obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    obtain rfl := concat_functional (R := ParamT I)
      (fun _ _ _ h h' => paramT_functional hT h h') hp hp'
    obtain rfl := concat_functional (R := ResultT I)
      (fun _ _ _ h h' => resultT_functional hT h h') hr hr'
    obtain rfl := Wasm.Idx.toNat_injective (first_index_unique hd hmin hd' hmin')
    exact ⟨rfl, rfl, rfl⟩

theorem tagTypeT_functional {I : IdCtx} (hT : Distinct I.types) {xs : List SExp}
    {t t' : TagType} {u u' : List FuncType} (h : TagTypeT I xs t u) (h' : TagTypeT I xs t' u') :
    t = t' ∧ u = u' := by
  obtain ⟨ls, h⟩ := h
  obtain ⟨ls', h'⟩ := h'
  obtain ⟨rfl, -, rfl⟩ := typeUseT_functional hT h h'
  exact ⟨rfl, rfl⟩

theorem typeUseT_notId {I : IdCtx} {xs : List SExp} {x : TypeIdx} {ls : List (Option String)}
    {u : List FuncType} (h : TypeUseT I xs x ls u) : ∀ y ∈ xs, ¬ IdAtom y :=
  fun y hy => tuList_notId (typeUseT_mem h y hy)

theorem externTypeT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {et et' : ExternType} {J J' : IdCtx} {u u' : List FuncType} (h : ExternTypeT I x et J u)
    (h' : ExternTypeT I x et' J' u') : et = et' ∧ J = J' ∧ u = u' := by
  rcases h with ⟨ix, rest, id, t, rfl, hix, ht, rfl, rfl⟩ |
      ⟨ix, gx, id, g, rfl, hix, hg, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, m, rfl, hix, hm, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, t, rfl, hix, ht, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, t, ls, rfl, hix, ht, rfl, rfl⟩ <;>
    rcases h' with ⟨ix', rest', id', t', e, hix', ht', rfl, rfl⟩ |
      ⟨ix', gx', id', g', e, hix', hg', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', m', e, hix', hm', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', t', e, hix', ht', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', t', ls', e, hix', ht', rfl, rfl⟩
  all_goals simp only [L_inj, List.cons.injEq, K_inj] at e
  all_goals first | (exact absurd e.1 (by decide)) | obtain ⟨-, e⟩ := e
  · obtain ⟨t1, t2⟩ := ht; obtain ⟨t1', t2'⟩ := ht'
    obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (notIdHead_of_forall (typeUseT_notId t2))
      (notIdHead_of_forall (typeUseT_notId t2')) e
    obtain ⟨rfl, rfl⟩ := tagTypeT_functional hT ⟨t1, t2⟩ ⟨t1', t2'⟩
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, h3⟩ := idOpt_split hix hix' (notIdHead_cons (globalTypeT_notId hg))
      (notIdHead_cons (globalTypeT_notId hg')) e
    simp only [List.cons.injEq, and_true] at h3; subst h3
    rw [globalTypeT_functional hT hg hg']; exact ⟨rfl, rfl, rfl⟩
  · have nid : ∀ {rest : List SExp} {m : MemoryType}, MemTypeT rest m → NotIdHead rest := by
      intro rest m hm
      exact notIdHead_of_forall fun x hx => by obtain ⟨s, rfl⟩ := memTypeT_mem hm x hx; simp
    obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (nid hm) (nid hm') e
    rw [memTypeT_functional hm hm']; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (notIdHead_of_forall (tableTypeT_notId ht))
      (notIdHead_of_forall (tableTypeT_notId ht')) e
    rw [tableTypeT_functional hT ht ht']; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (notIdHead_of_forall (typeUseT_notId ht))
      (notIdHead_of_forall (typeUseT_notId ht')) e
    obtain ⟨rfl, -, rfl⟩ := typeUseT_functional hT ht ht'
    exact ⟨rfl, rfl, rfl⟩

/-! ## Congruence along contexts resolving type identifiers alike -/

/-- Two contexts resolve type indices in the same way. -/
def TypesEq (I I' : IdCtx) : Prop := ∀ (x : SExp) (i : Nat), IdxIn I.types x i ↔ IdxIn I'.types x i

theorem TypesEq.refl (I : IdCtx) : TypesEq I I := fun _ _ => Iff.rfl

theorem TypesEq.symm {I I' : IdCtx} (h : TypesEq I I') : TypesEq I' I := fun x i => (h x i).symm

theorem TypesEq.of_types {I I' : IdCtx} (h : I.types = I'.types) : TypesEq I I' := by
  intro x i; rw [h]

section congr

variable {I I' : IdCtx} (h : TypesEq I I')
include h

theorem idx_types_eq {k : IndexKind} : (Idx (k := k) I.types) = Idx I'.types := by
  funext x i; exact propext (h x i.toNat)

theorem heapTypeT_eq : HeapTypeT I = HeapTypeT I' := by
  funext x t; unfold HeapTypeT; rw [idx_types_eq h]

theorem refTypeT_eq : RefTypeT I = RefTypeT I' := by
  funext x t; unfold RefTypeT; rw [heapTypeT_eq h]

theorem valTypeT_eq : ValTypeT I = ValTypeT I' := by
  funext x t; unfold ValTypeT; rw [refTypeT_eq h]

theorem storageTypeT_eq : StorageTypeT I = StorageTypeT I' := by
  funext x t; unfold StorageTypeT; rw [valTypeT_eq h]

theorem fieldTypeT_eq : FieldTypeT I = FieldTypeT I' := by
  funext x t; unfold FieldTypeT; rw [storageTypeT_eq h]

theorem fieldT_eq : FieldT I = FieldT I' := by
  funext x t; unfold FieldT; rw [fieldTypeT_eq h]

theorem paramT_eq : ParamT I = ParamT I' := by
  funext x t; unfold ParamT; rw [valTypeT_eq h]

theorem resultT_eq : ResultT I = ResultT I' := by
  funext x t; unfold ResultT; rw [valTypeT_eq h]

theorem compTypeT_eq : CompTypeT I = CompTypeT I' := by
  funext x t ns; unfold CompTypeT; rw [fieldT_eq h, fieldTypeT_eq h, paramT_eq h, resultT_eq h]

theorem subTypeT_eq : SubTypeT I = SubTypeT I' := by
  funext x t ns; unfold SubTypeT; rw [idx_types_eq h, compTypeT_eq h]

theorem typeDefT_eq : TypeDefT I = TypeDefT I' := by
  funext x t id ns; unfold TypeDefT; rw [subTypeT_eq h]

theorem recTypeT_eq : RecTypeT I = RecTypeT I' := by
  funext x t J; unfold RecTypeT; rw [typeDefT_eq h]

theorem globalTypeT_eq : GlobalTypeT I = GlobalTypeT I' := by
  funext x t; unfold GlobalTypeT; rw [valTypeT_eq h]

theorem tableTypeT_eq : TableTypeT I = TableTypeT I' := by
  funext x t; unfold TableTypeT; rw [refTypeT_eq h]

end congr

/-- Functionality across two contexts resolving types alike: type uses yield
the same implicitly used function types. -/
theorem typeUseT_uses {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I') {xs : List SExp}
    {x x' : TypeIdx} {ls ls' : List (Option String)} {u u' : List FuncType}
    (h : TypeUseT I xs x ls u) (h' : TypeUseT I' xs x' ls' u') : u = u' := by
  have noType : ∀ {J : IdCtx} {pxs rxs : List SExp} {ps : List (ValType × Option String)}
      {rs : List ValType} {tx : SExp} {rest : List SExp}, Concat (ParamT J) pxs ps →
      Concat (ResultT J) rxs rs → L [K "type", tx] :: rest = pxs ++ rxs → False := by
    intro J pxs rxs ps rs tx rest hp hr e
    have := params_results_mem hp hr (L [K "type", tx]) (by rw [← e]; simp)
    rcases this with h | h <;> exact headKw_ne (by decide) ⟨[tx], rfl⟩ h
  rcases h with ⟨tx, pxs₀, rxs₀, ft, rfl, -, -, -, -, -, rfl⟩ |
      ⟨tx, pxs, rxs, ft, ps, rs, rfl, -, -, hp, hr, -, -, -, rfl⟩ |
      ⟨pxs, rxs, ps, rs, rfl, hp, hr, -, -, -, -, rfl⟩ <;>
    rcases h' with ⟨tx', pxs₀', rxs₀', ft', e, -, -, -, -, -, rfl⟩ |
      ⟨tx', pxs', rxs', ft', ps', rs', e, -, -, hp', hr', -, -, -, rfl⟩ |
      ⟨pxs', rxs', ps', rs', e, hp', hr', -, -, -, -, rfl⟩
  all_goals first | rfl | skip
  · exact (noType hp' hr' e).elim
  · exact (noType hp' hr' e).elim
  · exact (noType hp hr e.symm).elim
  · exact (noType hp hr e.symm).elim
  · rw [← paramT_eq hE] at hp'; rw [← resultT_eq hE] at hr'
    obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
    obtain rfl := concat_functional (R := ParamT I)
      (fun _ _ _ h h' => paramT_functional hT h h') hp hp'
    obtain rfl := concat_functional (R := ResultT I)
      (fun _ _ _ h h' => resultT_functional hT h h') hr hr'
    rfl

end Silmaril.Wasm.Text.Core
