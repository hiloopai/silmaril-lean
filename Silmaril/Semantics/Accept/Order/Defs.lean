module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Computability.Language

/-!
# Programs ordered by language inclusion

Given any carrier `X` of programs (or checkers, grammars, types …) and a language map
`lang : X → Set α`, programs are compared by the languages they accept:
`x ≤ y ↔ lang x ⊆ lang y`. This file packages that comparison in three ways.

* `LangPre lang`: a type synonym of `X` with the induced **preorder**. Different programs with
  the same language are equivalent (`AntisymmRel`), not equal.
* `LangQuot s lang`: the quotient of `X` by a *supplied* program equivalence `s` (for example
  syntactic or α-equivalence) that respects the language (`RespectsLang s lang`). The
  language descends, and the quotient is again only a **preorder**: `s` may identify fewer
  programs than “same language”.
* `LangEq lang`: the quotient by equality of languages (Mathlib's `Setoid.ker lang`), a
  **partial order**, order-isomorphic to the range of `lang` and to the antisymmetrization of
  `LangPre lang` (`Thms`).

## Mathlib languages

Mathlib's `Language α` (and so `Silmaril.Formats.Accept.ByteLang = Language UInt8`) is a
`def` equal to `Set (List α)`, not reducible. Type-class search does not unfold it, so
`LangPre lang` and `LangEq lang` for `lang : X → Language α` find no order instance. Wrap the
map with `toSets lang : X → Set (List α)`; the order is then that of `Language α`
(`LangPre.toSets_le_iff`, `LangEq.toSets_mk_eq_mk_iff`).

## Carriers and shapes

Programs of different shapes are compared by putting them in one carrier: for two carriers,
`Sum.elim lang₁ lang₂ : X ⊕ Y → Set α` (`langSum`); for a family, `langSigma`. The inclusions
`Sum.inl`, `Sum.inr`, `Sigma.mk i` and `Subtype.val` are order *embeddings* (`Thms`), and a
left program is below a right one iff its language is included. The two shapes are disjoint
as *programs*, but not up to the order: `inl x` and `inr y` are equivalent (and equal in
`LangEq`) exactly when `lang₁ x = lang₂ y` (`Thms`), so disjointness of shapes does not survive
the quotient by language.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

variable {X : Type u} {Y : Type w} {α : Type v}

/-! ## The language preorder -/

/-- The carrier `X`, preordered by inclusion of the languages `lang`. -/
def LangPre (_lang : X → Set α) : Type u := X

namespace LangPre

variable {lang : X → Set α}

/-- View a program in the language preorder. -/
def of (lang : X → Set α) (x : X) : LangPre lang := x

/-- The underlying program. -/
def val (x : LangPre lang) : X := x

/-- The language of an element of the preorder. -/
def toLang (x : LangPre lang) : Set α := lang x.val

instance : Preorder (LangPre lang) := Preorder.lift toLang

end LangPre

/-- The language of the left or right shape. -/
abbrev langSum (lang₁ : X → Set α) (lang₂ : Y → Set α) : X ⊕ Y → Set α := Sum.elim lang₁ lang₂

/-- The language of a family of shapes. -/
abbrev langSigma {ι : Type w} {X : ι → Type u} (lang : ∀ i, X i → Set α) :
    (Σ i, X i) → Set α := fun p => lang p.1 p.2

/-- A family of Mathlib languages as a family of sets of words, for `LangPre`, `LangQuot`
and `LangEq`. -/
abbrev toSets {β : Type v} (lang : X → Language β) : X → Set (List β) := fun x => lang x

/-! ## Quotients by a supplied equivalence -/

/-- A program equivalence respects the language map: equivalent programs accept the same
language. -/
class RespectsLang (s : Setoid X) (lang : X → Set α) : Prop where
  eq_of_rel : ∀ ⦃x y : X⦄, s x y → lang x = lang y

/-- Programs up to a supplied equivalence `s` respecting `lang`, preordered by language. -/
def LangQuot (s : Setoid X) (_lang : X → Set α) : Type u := Quotient s

namespace LangQuot

variable {s : Setoid X} {lang : X → Set α}

/-- The class of a program. -/
def mk (s : Setoid X) (lang : X → Set α) (x : X) : LangQuot s lang := Quotient.mk s x

/-- The language of a class: well defined because `s` respects `lang`. -/
def toLang [RespectsLang s lang] (q : LangQuot s lang) : Set α :=
  Quotient.lift (s := s) lang (fun _ _ h => RespectsLang.eq_of_rel h) q

instance [RespectsLang s lang] : Preorder (LangQuot s lang) := Preorder.lift toLang

end LangQuot

/-! ## The quotient by equal language -/

instance RespectsLang.ker (lang : X → Set α) : RespectsLang (Setoid.ker lang) lang :=
  ⟨fun _ _ h => Setoid.ker_def.1 h⟩

/-- Programs up to equality of language: the partial order of accepted languages. -/
def LangEq (lang : X → Set α) : Type u := LangQuot (Setoid.ker lang) lang

namespace LangEq

variable {lang : X → Set α}

/-- The class of a program. -/
def mk (lang : X → Set α) (x : X) : LangEq lang := LangQuot.mk _ lang x

/-- The language of a class. -/
def toLang (q : LangEq lang) : Set α := LangQuot.toLang (s := Setoid.ker lang) q

theorem toLang_injective : Function.Injective (toLang (lang := lang)) := by
  rintro ⟨x⟩ ⟨y⟩ h; exact Quotient.sound (Setoid.ker_def.2 h)

instance : PartialOrder (LangEq lang) := PartialOrder.lift toLang toLang_injective

end LangEq

end Silmaril.Accept
