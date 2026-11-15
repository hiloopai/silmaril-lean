module

public import Silmaril.Semantics.Accept.Order.Defs

/-!
# Programs ordered by language inclusion: laws

* `LangPre`: `le_iff`, equivalence is equal language (`antisymmRel_iff`), monotone maps along
  language-preserving functions (`LangPre.map`) and order embeddings along injective ones
  (`LangPre.embed`): subtypes (`subtypeEmb`), the shapes of a sum (`inlEmb`, `inrEmb`) and
  of a family (`sigmaEmb`); cross-shape comparison (`inl_le_inr_iff`) and the identification
  of shapes up to the order (`inl_antisymmRel_inr_iff`).
* `LangQuot`: the language descends (`toLang_mk`), `mk_le_mk_iff`, the class map
  `LangQuot.mkHom` is monotone, reflects the order and is surjective, and the comparison with
  the language quotient `LangQuot.toLangEq` is monotone, reflects the order, is surjective,
  and is injective iff `s` identifies all programs with equal languages.
* `LangEq`: `mk_eq_mk_iff`, `mk_le_mk_iff`, the order embedding into `Set α`
  (`LangEq.toSetEmb`), and the order isomorphisms with the range of `lang`
  (`LangEq.rangeIso`) and with the antisymmetrization of `LangPre lang` (`LangEq.antisymmIso`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

variable {X : Type u} {Y : Type w} {α : Type v}

/-! ## The language preorder -/

namespace LangPre

variable {lang : X → Set α}

@[simp] theorem toLang_of (x : X) : (of lang x).toLang = lang x := rfl

@[simp] theorem val_of (x : X) : (of lang x).val = x := rfl

@[simp] theorem of_val (x : LangPre lang) : of lang x.val = x := rfl

theorem le_iff {x y : LangPre lang} : x ≤ y ↔ x.toLang ⊆ y.toLang := Iff.rfl

@[simp] theorem of_le_of {x y : X} : of lang x ≤ of lang y ↔ lang x ⊆ lang y := Iff.rfl

theorem lt_iff {x y : LangPre lang} : x < y ↔ x.toLang ⊂ y.toLang := Iff.rfl

/-- Two programs are equivalent in the preorder iff they accept the same language. -/
theorem antisymmRel_iff {x y : LangPre lang} :
    AntisymmRel (· ≤ ·) x y ↔ x.toLang = y.toLang :=
  ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- The language map as a monotone map into sets. -/
def toSetHom : LangPre lang →o Set α := ⟨toLang, fun _ _ h => h⟩

/-- A function between carriers that preserves languages is monotone. -/
def map {lang' : Y → Set α} (f : X → Y) (hf : ∀ x, lang' (f x) = lang x) :
    LangPre lang →o LangPre lang' where
  toFun x := of lang' (f x.val)
  monotone' x y h := by
    change lang' (f x.val) ⊆ lang' (f y.val); rw [hf, hf]; exact h

/-- An injective function between carriers that preserves languages is an order embedding. -/
def embed {lang' : Y → Set α} (f : X → Y) (hinj : Function.Injective f)
    (hf : ∀ x, lang' (f x) = lang x) : LangPre lang ↪o LangPre lang' where
  toFun x := of lang' (f x.val)
  inj' _ _ h := hinj h
  map_rel_iff' {x y} := by
    change lang' (f x.val) ⊆ lang' (f y.val) ↔ lang x.val ⊆ lang y.val; rw [hf, hf]

/-- Programs satisfying `p`, as a sub-preorder. -/
def subtypeEmb (p : X → Prop) : LangPre (fun x : Subtype p => lang x.val) ↪o LangPre lang :=
  embed Subtype.val Subtype.val_injective fun _ => rfl

end LangPre

section Shapes

variable {lang₁ : X → Set α} {lang₂ : Y → Set α}

/-- Left-shape programs embed in the sum of shapes. -/
def inlEmb : LangPre lang₁ ↪o LangPre (langSum lang₁ lang₂) :=
  LangPre.embed Sum.inl Sum.inl_injective fun _ => rfl

/-- Right-shape programs embed in the sum of shapes. -/
def inrEmb : LangPre lang₂ ↪o LangPre (langSum lang₁ lang₂) :=
  LangPre.embed Sum.inr Sum.inr_injective fun _ => rfl

/-- Across shapes, a left program is below a right one iff its language is included. -/
theorem inl_le_inr_iff {x : X} {y : Y} :
    LangPre.of (langSum lang₁ lang₂) (Sum.inl x) ≤ LangPre.of _ (Sum.inr y) ↔ lang₁ x ⊆ lang₂ y :=
  Iff.rfl

/-- Shapes are disjoint as programs, but a left and a right program are equivalent in the
preorder exactly when their languages agree. -/
theorem inl_antisymmRel_inr_iff {x : X} {y : Y} :
    AntisymmRel (· ≤ ·) (LangPre.of (langSum lang₁ lang₂) (Sum.inl x))
      (LangPre.of _ (Sum.inr y)) ↔ lang₁ x = lang₂ y :=
  LangPre.antisymmRel_iff

/-- One shape of a family embeds in the dependent sum of shapes. -/
def sigmaEmb {ι : Type w} {X : ι → Type u} (lang : ∀ i, X i → Set α) (i : ι) :
    LangPre (lang i) ↪o LangPre (langSigma lang) :=
  LangPre.embed (Sigma.mk i) sigma_mk_injective fun _ => rfl

end Shapes

/-! ## Quotients by a supplied equivalence -/

namespace LangQuot

variable {s : Setoid X} {lang : X → Set α}

theorem mk_eq_mk_iff {x y : X} : mk s lang x = mk s lang y ↔ s x y := Quotient.eq

@[elab_as_elim]
theorem ind {p : LangQuot s lang → Prop} (h : ∀ x, p (mk s lang x)) (q : LangQuot s lang) : p q :=
  Quotient.ind h q

theorem mk_surjective : Function.Surjective (mk s lang) := Quotient.mk_surjective

variable [RespectsLang s lang]

@[simp] theorem toLang_mk (x : X) : (mk s lang x).toLang = lang x := rfl

theorem le_iff {p q : LangQuot s lang} : p ≤ q ↔ p.toLang ⊆ q.toLang := Iff.rfl

@[simp] theorem mk_le_mk_iff {x y : X} : mk s lang x ≤ mk s lang y ↔ lang x ⊆ lang y := Iff.rfl

/-- The class map, from the language preorder of programs. -/
def mkHom : LangPre lang →o LangQuot s lang := ⟨fun x => mk s lang x.val, fun _ _ h => h⟩

theorem mkHom_le_iff {x y : LangPre lang} : mkHom (s := s) x ≤ mkHom y ↔ x ≤ y := Iff.rfl

/-- Two classes are equivalent in the preorder iff their languages agree. -/
theorem antisymmRel_iff {p q : LangQuot s lang} :
    AntisymmRel (· ≤ ·) p q ↔ p.toLang = q.toLang :=
  ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- Compare with the quotient by equal language: identify classes with the same language. -/
def toLangEq : LangQuot s lang →o LangEq lang :=
  ⟨Quotient.lift (s := s) (LangEq.mk lang) fun _ _ h =>
      Quotient.sound (Setoid.ker_def.2 (RespectsLang.eq_of_rel h)),
    fun p q => ind (fun _ => ind (fun _ h => h) q) p⟩

@[simp] theorem toLangEq_mk (x : X) : toLangEq (mk s lang x) = LangEq.mk lang x := rfl

theorem toLang_toLangEq (p : LangQuot s lang) : (toLangEq p).toLang = p.toLang :=
  ind (fun _ => rfl) p

theorem toLangEq_le_iff {p q : LangQuot s lang} : toLangEq p ≤ toLangEq q ↔ p ≤ q := by
  show (toLangEq p).toLang ⊆ (toLangEq q).toLang ↔ _; rw [toLang_toLangEq, toLang_toLangEq]; rfl

theorem toLangEq_surjective : Function.Surjective (toLangEq (s := s) (lang := lang)) :=
  fun q => Quotient.inductionOn q fun x => ⟨mk s lang x, rfl⟩

/-- The supplied equivalence is exactly equality of language iff the comparison is injective. -/
theorem toLangEq_injective_iff :
    Function.Injective (toLangEq (s := s) (lang := lang)) ↔ ∀ x y, lang x = lang y → s x y :=
  ⟨fun h _ _ hxy => mk_eq_mk_iff.1 (h (Quotient.sound (Setoid.ker_def.2 hxy))),
    fun h p q => ind (fun x => ind (fun y hxy => Quotient.sound
      (h x y (Setoid.ker_def.1 (Quotient.exact hxy)))) q) p⟩

end LangQuot

/-! ## The quotient by equal language -/

namespace LangEq

variable {lang : X → Set α}

@[simp] theorem toLang_mk (x : X) : (mk lang x).toLang = lang x := rfl

theorem le_iff {p q : LangEq lang} : p ≤ q ↔ p.toLang ⊆ q.toLang := Iff.rfl

@[simp] theorem mk_le_mk_iff {x y : X} : mk lang x ≤ mk lang y ↔ lang x ⊆ lang y := Iff.rfl

@[simp] theorem mk_eq_mk_iff {x y : X} : mk lang x = mk lang y ↔ lang x = lang y :=
  Quotient.eq.trans Setoid.ker_def

@[elab_as_elim]
theorem ind {p : LangEq lang → Prop} (h : ∀ x, p (mk lang x)) (q : LangEq lang) : p q :=
  Quotient.ind h q

/-- The partial order of languages embeds in the sets. -/
def toSetEmb : LangEq lang ↪o Set α := OrderEmbedding.ofMapLEIff toLang fun _ _ => Iff.rfl

/-- Classes of programs are exactly the languages some program accepts. -/
noncomputable def rangeIso : LangEq lang ≃o Set.range lang :=
  OrderIso.ofSurjective ⟨⟨fun q => ⟨q.toLang, ind (fun x => ⟨x, rfl⟩) q⟩,
    fun _ _ h => toLang_injective (congrArg Subtype.val h)⟩, Iff.rfl⟩
    fun ⟨_, x, hx⟩ => ⟨mk lang x, Subtype.ext hx⟩

/-- The quotient by equal language is the antisymmetrization of the language preorder. -/
def antisymmIso : Antisymmetrization (LangPre lang) (· ≤ ·) ≃o LangEq lang where
  toEquiv := Quotient.congr (Equiv.refl X) fun _ _ =>
    LangPre.antisymmRel_iff.trans Setoid.ker_def.symm
  map_rel_iff' {p q} := Quotient.inductionOn₂ p q fun _ _ => Iff.rfl

/-- Programs of different shapes with the same language become equal. -/
theorem mk_inl_eq_mk_inr_iff {Y : Type w} {lang₁ : X → Set α} {lang₂ : Y → Set α} {x : X}
    {y : Y} : mk (langSum lang₁ lang₂) (Sum.inl x) = mk _ (Sum.inr y) ↔ lang₁ x = lang₂ y :=
  mk_eq_mk_iff

end LangEq

end Silmaril.Accept
