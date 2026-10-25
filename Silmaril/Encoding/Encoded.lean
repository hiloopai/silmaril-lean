module

public import Silmaril.Encoding.Category

/-!
# Encoded values: the graph of an encoding

`Encoded E` packages a carrier value together with an abstract value it
spells: `⟨text, ast, valid⟩`.  It is the graph of the relation `E`, and its two
projections characterize the basic predicates:

* `Encoded.text` is injective iff `E` is functional (the text determines the
  syntax) — this is the property wanted of `WasmText`/`WasmBinary`-style
  "source together with its parse" types;
* `Encoded.ast` is injective iff `E` is deterministic.

For a functional `E`, `Encoded.textEmbedding hF : Encoded E ↪ σ` packages
the text projection as an injection.  `FunEncRel σ α` bundles a relation with
its functionality proof, so `FunEncRel.Encoded E` carries the injection
`E.textEmbedding` with no side condition.  This is the shape of the
"source together with its parse" types of `Silmaril.Encoding.Syntax`:
`WithText α` / `WithBinary α` are `FunEncRel.Encoded` of the relation
registered by a `TextSyntax α` / `BinarySyntax α` instance, and
`WasmText := WithText Wasm.Module`, `WasmBinary := WithBinary Wasm.Module`
(`Silmaril.Encoding.Wasm`).

`Encoded` is a functor `EncCat₂ ⥤ Type` (`functor₂`, mapping the text by the
carrier map), restricting along `ι σ` to `functor σ : EncCat σ ⥤ Type`; `text`
and `ast` are natural transformations to `carrierFunctor`/`astFunctor`.
Concrete named instances (`JsonText`, `CborBinary`, …) are abbreviations
`Encoded E` for a specific encoding `E`.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

/-- A carrier value `text` together with an abstract value `ast` it encodes. -/
@[ext]
structure Encoded {σ α : Type} (E : EncRel σ α) where
  /-- The concrete spelling. -/
  text : σ
  /-- The abstract value. -/
  ast : α
  /-- `text` is a valid spelling of `ast`. -/
  valid : E text ast

namespace Encoded

variable {σ σ' α β : Type} {E : EncRel σ α}

instance [DecidableEq σ] [DecidableEq α] : DecidableEq (Encoded E) := fun x y =>
  if h : x.text = y.text ∧ x.ast = y.ast then isTrue (Encoded.ext h.1 h.2)
  else isFalse fun e => h ⟨congrArg Encoded.text e, congrArg Encoded.ast e⟩

/-- **The projection to the text is injective exactly for functional
encodings.** -/
theorem text_injective_iff : Function.Injective (Encoded.text (E := E)) ↔ E.Functional := by
  constructor
  · intro h s a a' ha ha'
    exact congrArg Encoded.ast (@h ⟨s, a, ha⟩ ⟨s, a', ha'⟩ rfl)
  · intro hF x y hxy
    exact Encoded.ext hxy (hF x.valid (hxy ▸ y.valid))

theorem text_injective (hF : E.Functional) : Function.Injective (Encoded.text (E := E)) :=
  text_injective_iff.mpr hF

/-- For a functional encoding, the text projection as an embedding. -/
def textEmbedding (hF : E.Functional) : Encoded E ↪ σ :=
  ⟨Encoded.text, text_injective hF⟩

@[simp] theorem textEmbedding_apply (hF : E.Functional) (x : Encoded E) :
    textEmbedding hF x = x.text := rfl

/-- The projection to the syntax is injective exactly for deterministic
encodings. -/
theorem ast_injective_iff : Function.Injective (Encoded.ast (E := E)) ↔ E.Deterministic := by
  constructor
  · intro h s s' a hs hs'
    exact congrArg Encoded.text (@h ⟨s, a, hs⟩ ⟨s', a, hs'⟩ rfl)
  · intro hD x y hxy
    exact Encoded.ext (hD x.valid (hxy ▸ y.valid)) hxy

theorem text_range : Set.range (Encoded.text (E := E)) = E.domain := by
  ext s
  exact ⟨fun ⟨x, hx⟩ => hx ▸ ⟨x.ast, x.valid⟩, fun ⟨a, h⟩ => ⟨⟨s, a, h⟩, rfl⟩⟩

theorem ast_range : Set.range (Encoded.ast (E := E)) = E.image := by
  ext a
  exact ⟨fun ⟨x, hx⟩ => hx ▸ ⟨x.text, x.valid⟩, fun ⟨s, h⟩ => ⟨⟨s, a, h⟩, rfl⟩⟩

/-- For functional `E`, an encoded value is the same thing as an encodable
spelling. -/
noncomputable def equivDomain (hF : E.Functional) : Encoded E ≃ {s : σ // E.Encodable s} where
  toFun x := ⟨x.text, x.ast, x.valid⟩
  invFun s := ⟨s.1, s.2.choose, s.2.choose_spec⟩
  left_inv x := Encoded.ext rfl (hF (⟨x.ast, x.valid⟩ : E.Encodable x.text).choose_spec x.valid)
  right_inv _ := rfl

/-- For deterministic `E`, an encoded value is the same thing as an encodable
abstract value. -/
noncomputable def equivImage (hD : E.Deterministic) : Encoded E ≃ E.image where
  toFun x := ⟨x.ast, x.text, x.valid⟩
  invFun a := ⟨a.2.choose, a.1, a.2.choose_spec⟩
  left_inv x := Encoded.ext (hD (⟨x.text, x.valid⟩ : ∃ s, E s x.ast).choose_spec x.valid) rfl
  right_inv _ := rfl

/-- Monotonicity: `E ≤ F` includes `Encoded E` into `Encoded F`, preserving
both projections. -/
def ofLE {F : EncRel σ α} (h : E ≤ F) (x : Encoded E) : Encoded F :=
  ⟨x.text, x.ast, h _ _ x.valid⟩

theorem ofLE_injective {F : EncRel σ α} (h : E ≤ F) : Function.Injective (ofLE h) :=
  fun x y hxy => by
    have h₁ := congrArg Encoded.text hxy
    have h₂ := congrArg Encoded.ast hxy
    exact Encoded.ext h₁ h₂

/-! ## Carrier change -/

/-- Push an encoded value along a carrier map `g`. -/
def push (g : σ → σ') (x : Encoded E) : Encoded (E.push g) :=
  ⟨g x.text, x.ast, x.text, rfl, x.valid⟩

theorem push_surjective (g : σ → σ') : Function.Surjective (push (E := E) g) := by
  rintro ⟨_, a, s, rfl, h⟩
  exact ⟨⟨s, a, h⟩, rfl⟩

/-- Along an injective carrier map, pushing is an equivalence (mapping the
text by `g`). -/
noncomputable def pushEquiv {g : σ → σ'} (hg : Function.Injective g) :
    Encoded E ≃ Encoded (E.push g) :=
  Equiv.ofBijective (push g)
    ⟨fun x y h => by
        have h₁ := congrArg Encoded.text h
        have h₂ := congrArg Encoded.ast h
        exact Encoded.ext (hg h₁) h₂,
      push_surjective g⟩

@[simp] theorem pushEquiv_text {g : σ → σ'} (hg : Function.Injective g) (x : Encoded E) :
    (pushEquiv hg x).text = g x.text := rfl

/-- Pull an encoded value back: a spelling `s` with `E (g s) a`. -/
def ofPull {F : EncRel σ' α} (g : σ → σ') (x : Encoded (F.pull g)) : Encoded F :=
  ⟨g x.text, x.ast, x.valid⟩

/-! ## Functoriality -/

/-- `Encoded` as a functor on `EncCat σ`: a morphism maps the syntax and keeps
the text. -/
@[simps]
def functor (σ : Type) : EncCat σ ⥤ Type where
  obj X := Encoded X.rel
  map f := TypeCat.ofHom fun x => ⟨x.text, f.fn x.ast, f.preserves _ _ x.valid⟩

/-- `text` is natural: morphisms of `EncCat σ` preserve the spelling. -/
def textNat (σ : Type) : functor σ ⟶ (Functor.const (EncCat σ)).obj σ where
  app _ := TypeCat.ofHom Encoded.text
  naturality _ _ _ := rfl

/-- `ast` is natural: `Encoded ⟶ forget`. -/
def astNat (σ : Type) : functor σ ⟶ EncCat.forget σ where
  app _ := TypeCat.ofHom Encoded.ast
  naturality _ _ _ := rfl

/-- Pushing along `g` relates `Encoded` over `σ` to `Encoded` over `σ'`. -/
def pushNat (g : σ → σ') : functor σ ⟶ EncCat.pushFunctor g ⋙ functor σ' where
  app _ := TypeCat.ofHom (push g)
  naturality _ _ _ := rfl

/-- `Encoded` as a functor on `EncCat₂`: a morphism `(g, f)` maps the text by
`g` and the syntax by `f`. -/
@[simps]
def functor₂ : EncCat₂ ⥤ Type where
  obj X := Encoded X.rel
  map f := TypeCat.ofHom fun x => ⟨f.onCarrier x.text, f.fn x.ast, f.preserves _ _ x.valid⟩

/-- `functor σ` is the restriction of `functor₂` along `ι σ`. -/
theorem incl_comp_functor₂ (σ : Type) : EncCat.incl σ ⋙ functor₂ = functor σ := rfl

/-- `text` is natural on `EncCat₂`: `functor₂ ⟶ carrierFunctor`. -/
def textNat₂ : functor₂ ⟶ EncCat₂.carrierFunctor where
  app _ := TypeCat.ofHom Encoded.text
  naturality _ _ _ := rfl

/-- `ast` is natural on `EncCat₂`: `functor₂ ⟶ astFunctor`. -/
def astNat₂ : functor₂ ⟶ EncCat₂.astFunctor where
  app _ := TypeCat.ofHom Encoded.ast
  naturality _ _ _ := rfl

end Encoded

/-! ## Functional encodings, bundled -/

/-- An encoding bundled with its functionality: the text determines the
syntax.  `TextSyntax` / `BinarySyntax` (`Silmaril.Encoding.Syntax`) register
one per syntax type; their encoded values are `WithText` / `WithBinary`
(e.g. `WasmText`, `WasmBinary`). -/
structure FunEncRel (σ α : Type) where
  /-- The encoding relation. -/
  rel : EncRel σ α
  /-- Every spelling has at most one parse. -/
  functional : rel.Functional

namespace FunEncRel

variable {σ α : Type}

/-- Encoded values of a functional encoding (`WithText α` and `WithBinary α`
are instances). -/
abbrev Encoded (E : FunEncRel σ α) := Silmaril.Encoded E.rel

/-- The text projection of a bundled functional encoding is injective. -/
theorem text_injective (E : FunEncRel σ α) :
    Function.Injective (Silmaril.Encoded.text (E := E.rel)) :=
  Silmaril.Encoded.text_injective E.functional

/-- The text projection as an embedding. -/
def textEmbedding (E : FunEncRel σ α) : E.Encoded ↪ σ :=
  Silmaril.Encoded.textEmbedding E.functional

end FunEncRel

end Silmaril
