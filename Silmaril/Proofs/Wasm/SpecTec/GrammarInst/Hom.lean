module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Least

/-!
# Changing the attribute algebra: homomorphisms and the comorphism they induce

An attribute-algebra homomorphism `f : AttrHom A B` maps attributes `α → β`. It preserves the
unit, the product and the attribute of each byte. It also comes with a translation of attribute
actions that commutes with `f` (`map_act`). Then:

* `mapSym f` translates grammar symbols over `α` into symbols over `β`, and interpretation
  commutes with taking images: `interp_map`.
* The least model of the translated grammar is the image of the least model
  (`leastModel_map`). So consequences correspond: `entails_map_iff` says
  `mapProds f P ⊨ derives (mapSym f g) bs Q ↔ P ⊨ derives g bs (Q ∘ f)`.
* **The comorphism.** The derivability assertions at a nonterminal (`Obs`) form a
  sub-institution `obsInst A D` of `inst A D` (`obsInclusion`). Any attribute map `f : α → β`
  induces an institution comorphism `obsCoHom f : CoHom (obsInst B D) (obsInst A D)`. Its
  signature functor is the identity, sentences go by precomposition (`Q ↦ Q ∘ f`), and models
  go by image (`Model.image f`). When `f` is a homomorphism, the comorphism is conservative
  between a grammar's theory and its translation (`obsCoHom_conservative`).

The comorphism is defined only on derivability assertions at nonterminals, not on all
sentences. Productions over `β` have no translation back to `α`. Also, for a non-surjective `f`,
the image model does not satisfy the translated productions in the reverse direction. So this is
not a comorphism of the full grammar institutions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory
open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

variable {N α β : Type}

/-! ## Homomorphisms of attribute algebras -/

/-- A homomorphism of attribute algebras, with a translation of attribute actions that commutes
with it. -/
structure AttrHom (A : Attr α) (B : Attr β) where
  /-- The map on attributes. -/
  toFun : α → β
  /-- The unit is preserved. -/
  map_nil : toFun A.nil = B.nil
  /-- Products are preserved. -/
  map_app : ∀ a b, toFun (A.app a b) = B.app (toFun a) (toFun b)
  /-- Terminal bytes contribute corresponding attributes. -/
  map_ofByte : ∀ b, toFun (A.ofByte b) = B.ofByte b
  /-- The translation of an attribute action. -/
  act : (α → Option α) → β → Option β
  /-- The translated action does on images what the action does. -/
  map_act : ∀ h a, act h (toFun a) = (h a).map toFun

namespace AttrHom

variable {A : Attr α} {B : Attr β}

/-- An injective map preserving unit, product and bytes is a homomorphism: an action is
translated by choosing the (unique) preimage. -/
noncomputable def ofInjective (g : α → β) (hg : Function.Injective g) (h₀ : g A.nil = B.nil)
    (h₁ : ∀ a b, g (A.app a b) = B.app (g a) (g b)) (h₂ : ∀ b, g (A.ofByte b) = B.ofByte b) :
    AttrHom A B where
  toFun := g
  map_nil := h₀
  map_app := h₁
  map_ofByte := h₂
  act h b := by
    classical
    exact if hb : ∃ a, g a = b then (h hb.choose).map g else none
  map_act h a := by
    classical
    split
    · next hb => rw [hg hb.choose_spec]
    · next hn => exact absurd ⟨a, rfl⟩ hn

variable (f : AttrHom A B)

/-- Literal byte strings contribute corresponding attributes. -/
theorem map_ofBytes (l : Bytes) : f.toFun (A.ofBytes l) = B.ofBytes l := by
  induction l with
  | nil => exact f.map_nil
  | cons b l ih => simp only [Attr.ofBytes_cons, f.map_app, f.map_ofByte, ih]

/-! ### The image of each combinator -/

theorem map_epsRel : EncRel.map f.toFun (epsRel A.nil) = epsRel B.nil := by
  ext bs b
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, f.map_nil⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨A.nil, ⟨rfl, rfl⟩, f.map_nil⟩

theorem map_byteRel (c : UInt8) : EncRel.map f.toFun (byteRel A c) = byteRel B c := by
  ext bs b
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, f.map_ofByte c⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨A.ofByte c, ⟨rfl, rfl⟩, f.map_ofByte c⟩

theorem map_rangeRel (lo hi : UInt8) :
    EncRel.map f.toFun (rangeRel A lo hi) = rangeRel B lo hi := by
  ext bs b
  constructor
  · rintro ⟨a, ⟨c, h₁, h₂, rfl, rfl⟩, rfl⟩
    exact ⟨c, h₁, h₂, rfl, f.map_ofByte c⟩
  · rintro ⟨c, h₁, h₂, rfl, rfl⟩
    exact ⟨A.ofByte c, ⟨c, h₁, h₂, rfl, rfl⟩, f.map_ofByte c⟩

theorem map_bytesRel (l : Bytes) : EncRel.map f.toFun (bytesRel A l) = bytesRel B l := by
  ext bs b
  constructor
  · rintro ⟨a, ⟨hbs, rfl⟩, rfl⟩
    exact ⟨hbs, f.map_ofBytes l⟩
  · rintro ⟨hbs, rfl⟩
    exact ⟨A.ofBytes l, ⟨hbs, rfl⟩, f.map_ofBytes l⟩

theorem map_appendRel (E F : EncRel Bytes α) :
    EncRel.map f.toFun (appendRel A E F) =
      appendRel B (EncRel.map f.toFun E) (EncRel.map f.toFun F) := by
  ext bs b
  constructor
  · rintro ⟨a, ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩, rfl⟩
    exact ⟨b₁, f.toFun a₁, b₂, f.toFun a₂, ⟨a₁, h₁, rfl⟩, ⟨a₂, h₂, rfl⟩, rfl, f.map_app a₁ a₂⟩
  · rintro ⟨b₁, _, b₂, _, ⟨a₁, h₁, rfl⟩, ⟨a₂, h₂, rfl⟩, rfl, rfl⟩
    exact ⟨A.app a₁ a₂, ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩, f.map_app a₁ a₂⟩

theorem map_appendAll (Es : List (EncRel Bytes α)) :
    EncRel.map f.toFun (appendAll A Es) = appendAll B (Es.map (EncRel.map f.toFun)) := by
  induction Es with
  | nil => exact f.map_epsRel
  | cons E Es ih =>
    show EncRel.map f.toFun (appendRel A E (appendAll A Es)) =
      appendRel B (EncRel.map f.toFun E) (appendAll B (Es.map (EncRel.map f.toFun)))
    rw [map_appendRel, ih]

theorem map_powRel (E : EncRel Bytes α) (k : Nat) :
    EncRel.map f.toFun (powRel A E k) = powRel B (EncRel.map f.toFun E) k := by
  induction k with
  | zero => exact f.map_epsRel
  | succ k ih =>
    show EncRel.map f.toFun (appendRel A E (powRel A E k)) =
      appendRel B (EncRel.map f.toFun E) (powRel B (EncRel.map f.toFun E) k)
    rw [map_appendRel, ih]

theorem map_kleene (E : EncRel Bytes α) :
    EncRel.map f.toFun (kleene A E) = kleene B (EncRel.map f.toFun E) := by
  ext bs b
  constructor
  · rintro ⟨a, hk, rfl⟩
    obtain ⟨k, hk⟩ := kleene_apply.mp hk
    refine kleene_apply.mpr ⟨k, ?_⟩
    rw [← map_powRel]
    exact ⟨a, hk, rfl⟩
  · intro hb
    obtain ⟨k, hk⟩ := kleene_apply.mp hb
    rw [← map_powRel] at hk
    obtain ⟨a, hk, rfl⟩ := hk
    exact ⟨a, kleene_apply.mpr ⟨k, hk⟩, rfl⟩

theorem map_mapPartial (h : α → Option α) (E : EncRel Bytes α) :
    EncRel.map f.toFun (EncRel.mapPartial h E) =
      EncRel.mapPartial (f.act h) (EncRel.map f.toFun E) := by
  ext bs b
  constructor
  · rintro ⟨a', ⟨a, hE, ha⟩, rfl⟩
    exact ⟨f.toFun a, ⟨a, hE, rfl⟩, by rw [f.map_act, ha]; rfl⟩
  · rintro ⟨_, ⟨a, hE, rfl⟩, hb⟩
    rw [f.map_act] at hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨a', ⟨a, hE, ha'⟩, rfl⟩

end AttrHom

/-- Images distribute over binary joins. -/
theorem EncRel.map_sup' {σ : Type} (g : α → β) (E F : EncRel σ α) :
    EncRel.map g (E ⊔ F) = EncRel.map g E ⊔ EncRel.map g F := by
  ext s b
  simp only [EncRel.map, EncRel.sup_apply]
  constructor
  · rintro ⟨a, h | h, rfl⟩
    · exact Or.inl ⟨a, h, rfl⟩
    · exact Or.inr ⟨a, h, rfl⟩
  · rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩)
    · exact ⟨a, Or.inl h, rfl⟩
    · exact ⟨a, Or.inr h, rfl⟩

/-- Images distribute over finite joins. -/
theorem EncRel.map_supList {σ : Type} (g : α → β) (Es : List (EncRel σ α)) :
    EncRel.map g (supList Es) = supList (Es.map (EncRel.map g)) := by
  induction Es with
  | nil =>
    ext s b
    simp [EncRel.map, supList]
  | cons E Es ih =>
    show EncRel.map g (E ⊔ supList Es) = EncRel.map g E ⊔ supList (Es.map (EncRel.map g))
    rw [EncRel.map_sup', ih]

/-- Images are monotone. -/
theorem EncRel.map_mono' {σ : Type} (g : α → β) {E F : EncRel σ α} (h : E ≤ F) :
    EncRel.map g E ≤ EncRel.map g F := by
  rintro s b ⟨a, ha, rfl⟩
  exact ⟨a, h s a ha, rfl⟩

/-! ## Translating symbols -/

section MapSym

variable {A : Attr α} {B : Attr β}

mutual

/-- Translate a symbol along an attribute-algebra homomorphism: only attribute actions change. -/
def mapSym (f : AttrHom A B) : Sym N α → Sym N β
  | .eps => .eps
  | .byte b => .byte b
  | .range lo hi => .range lo hi
  | .bytes l => .bytes l
  | .nt x => .nt x
  | .seq gs => .seq (mapSyms f gs)
  | .alt gs => .alt (mapSyms f gs)
  | .star g => .star (mapSym f g)
  | .plus g => .plus (mapSym f g)
  | .opt g => .opt (mapSym f g)
  | .count g k => .count (mapSym f g) k
  | .attr h g => .attr (f.act h) (mapSym f g)

/-- `mapSym` on lists. -/
def mapSyms (f : AttrHom A B) : List (Sym N α) → List (Sym N β)
  | [] => []
  | g :: gs => mapSym f g :: mapSyms f gs

end

/-- The translated production table. -/
def mapProds (f : AttrHom A B) (P : N → List (Sym N α)) : N → List (Sym N β) :=
  fun x => (P x).map (mapSym f)

mutual

/-- **Interpretation commutes with images**: interpreting a translated symbol in the image of a
model is the image of its interpretation. -/
theorem interp_map (f : AttrHom A B) (I : N → EncRel Bytes α) :
    ∀ g : Sym N α,
      interp B (fun x => EncRel.map f.toFun (I x)) (mapSym f g) =
        EncRel.map f.toFun (interp A I g)
  | .eps => f.map_epsRel.symm
  | .byte c => (f.map_byteRel c).symm
  | .range lo hi => (f.map_rangeRel lo hi).symm
  | .bytes l => (f.map_bytesRel l).symm
  | .nt _ => rfl
  | .seq gs => by
      show appendAll B (interps B _ (mapSyms f gs)) = EncRel.map f.toFun (appendAll A (interps A I gs))
      rw [f.map_appendAll, interps_map f I gs]
  | .alt gs => by
      show supList (interps B _ (mapSyms f gs)) = EncRel.map f.toFun (supList (interps A I gs))
      rw [EncRel.map_supList, interps_map f I gs]
  | .star g => by
      show kleene B (interp B _ (mapSym f g)) = EncRel.map f.toFun (kleene A (interp A I g))
      rw [f.map_kleene, interp_map f I g]
  | .plus g => by
      show appendRel B (interp B _ (mapSym f g)) (kleene B (interp B _ (mapSym f g))) =
        EncRel.map f.toFun (appendRel A (interp A I g) (kleene A (interp A I g)))
      rw [f.map_appendRel, f.map_kleene, interp_map f I g]
  | .opt g => by
      show epsRel B.nil ⊔ interp B _ (mapSym f g) =
        EncRel.map f.toFun (epsRel A.nil ⊔ interp A I g)
      rw [EncRel.map_sup', f.map_epsRel, interp_map f I g]
  | .count g k => by
      show powRel B (interp B _ (mapSym f g)) k = EncRel.map f.toFun (powRel A (interp A I g) k)
      rw [f.map_powRel, interp_map f I g]
  | .attr h g => by
      show EncRel.mapPartial (f.act h) (interp B _ (mapSym f g)) =
        EncRel.map f.toFun (EncRel.mapPartial h (interp A I g))
      rw [f.map_mapPartial, interp_map f I g]

/-- `interp_map` on lists. -/
theorem interps_map (f : AttrHom A B) (I : N → EncRel Bytes α) :
    ∀ gs : List (Sym N α),
      interps B (fun x => EncRel.map f.toFun (I x)) (mapSyms f gs) =
        (interps A I gs).map (EncRel.map f.toFun)
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (interp_map f I g) (interps_map f I gs)

end

/-- The image of a model along an attribute map. -/
def Model.image (g : α → β) : Model N α ⥤ Model N β where
  obj I := ⟨fun x => EncRel.map g (I.rel x)⟩
  map h := ⟨fun x => EncRel.map_mono' g (h.down x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The image of the least model is a model of the translated theory. -/
theorem image_leastModel_sat (f : AttrHom A B) (P : N → List (Sym N α)) :
    ∀ φ ∈ prodAxioms (mapProds f P),
      (room B N).Sat ((Model.image f.toFun).obj (leastModel ⟨A, P⟩)) φ := by
  refine (sat_prodAxioms_iff B _ _).mpr fun y g' hg' => ?_
  obtain ⟨g, hg, hgg⟩ : ∃ g ∈ P y, mapSym f g = g' := List.mem_map.mp hg'
  have hsat : interp A (leastModel ⟨A, P⟩).rel g ≤ (leastModel ⟨A, P⟩).rel y :=
    (sat_prodAxioms_iff A P _).mp (leastModel_sat A P) y g hg
  have himg : interp B (fun x => EncRel.map f.toFun ((leastModel ⟨A, P⟩).rel x)) (mapSym f g) =
      EncRel.map f.toFun (interp A (leastModel ⟨A, P⟩).rel g) :=
    interp_map f _ g
  rw [← hgg]
  show interp B (fun x => EncRel.map f.toFun ((leastModel ⟨A, P⟩).rel x)) (mapSym f g) ≤ _
  rw [himg]
  exact EncRel.map_mono' f.toFun hsat

/-- The preimage of the least model of the translated theory is a model of the original one. -/
theorem preimage_leastModel_sat (f : AttrHom A B) (P : N → List (Sym N α)) :
    ∀ φ ∈ prodAxioms P, (room A N).Sat
      (⟨fun y bs a => (leastModel ⟨B, mapProds f P⟩).rel y bs (f.toFun a)⟩ : Model N α) φ := by
  let J : Model N α := ⟨fun y bs a => (leastModel ⟨B, mapProds f P⟩).rel y bs (f.toFun a)⟩
  have hJ : ∀ y, EncRel.map f.toFun (J.rel y) ≤ (leastModel ⟨B, mapProds f P⟩).rel y := by
    rintro y bs _ ⟨a, ha, rfl⟩
    exact ha
  refine (sat_prodAxioms_iff A P J).mpr fun y g hg bs a ha => ?_
  have himg : interp B (fun x => EncRel.map f.toFun (J.rel x)) (mapSym f g) bs (f.toFun a) := by
    rw [interp_map]
    exact ⟨a, ha, rfl⟩
  have hle : interp B (leastModel ⟨B, mapProds f P⟩).rel (mapSym f g) bs (f.toFun a) :=
    interp_mono B hJ (mapSym f g) bs (f.toFun a) himg
  exact (sat_prodAxioms_iff B _ _).mp (leastModel_sat B (mapProds f P)) y (mapSym f g)
    (List.mem_map.mpr ⟨g, hg, rfl⟩) bs (f.toFun a) hle

/-- **The least model of the translated grammar is the image of the least model.** -/
theorem leastModel_map (f : AttrHom A B) (P : N → List (Sym N α)) (x : N) :
    (leastModel ⟨B, mapProds f P⟩).rel x = EncRel.map f.toFun ((leastModel ⟨A, P⟩).rel x) := by
  apply le_antisymm
  · exact leastModel_le B (mapProds f P) _ (image_leastModel_sat f P) x
  · rintro bs _ ⟨a, ha, rfl⟩
    exact leastModel_le A P _ (preimage_leastModel_sat f P) x bs a ha

/-- **Consequences correspond across a homomorphism**: the translated grammar entails a
derivability assertion about a translated symbol iff the original grammar entails it with the
predicate pulled back along `f`. -/
theorem entails_map_iff (f : AttrHom A B) (P : N → List (Sym N α)) (g : Sym N α) (bs : Bytes)
    (Q : β → Prop) :
    (room B N).Entails (prodAxioms (mapProds f P)) (.derives (mapSym f g) bs Q) ↔
      (room A N).Entails (prodAxioms P) (.derives g bs (Q ∘ f.toFun)) := by
  rw [entails_derives_iff, entails_derives_iff, ← interp_leastModel ⟨B, mapProds f P⟩,
    ← interp_leastModel ⟨A, P⟩]
  have hrel : (leastModel ⟨B, mapProds f P⟩).rel =
      fun x => EncRel.map f.toFun ((leastModel ⟨A, P⟩).rel x) :=
    funext (leastModel_map f P)
  show (∃ b, interp B (leastModel ⟨B, mapProds f P⟩).rel (mapSym f g) bs b ∧ Q b) ↔
    ∃ a, interp A (leastModel ⟨A, P⟩).rel g bs a ∧ Q (f.toFun a)
  rw [hrel, interp_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hQ⟩
    exact ⟨a, ha, hQ⟩
  · rintro ⟨a, ha, hQ⟩
    exact ⟨f.toFun a, ⟨a, ha, rfl⟩, hQ⟩

end MapSym

/-! ## The institution of derivability assertions, and the comorphism -/

/-- A derivability assertion at a nonterminal: `x` derives `bs` with an attribute satisfying
`Q`. -/
structure Obs (N α : Type) : Type where
  /-- The nonterminal. -/
  x : N
  /-- The bytes. -/
  bs : Bytes
  /-- The property of the attribute. -/
  Q : α → Prop

namespace Obs

variable {N' : Type}

/-- The sentence of the grammar institution an assertion stands for. -/
def toSen (o : Obs N α) : Sen N α := .derives (.nt o.x) o.bs o.Q

/-- Renaming the nonterminal. -/
def rename (f : N → N') (o : Obs N α) : Obs N' α := ⟨f o.x, o.bs, o.Q⟩

/-- Pulling the property back along an attribute map. -/
def comap (g : α → β) (o : Obs N β) : Obs N α := ⟨o.x, o.bs, o.Q ∘ g⟩

end Obs

section ObsInstitution

variable (A : Attr α) (D : Type)

/-- The room of derivability assertions over the nonterminals `N`. Models are those of the
grammar institution. -/
def obsRoom (N : Type) : Room.{0, 0, 0} :=
  ⟨Obs N α, Cat.of (Model N α), fun M o => o.toSen.Holds A M.rel⟩

/-- The institution of derivability assertions at nonterminals: a sub-institution of `inst A D`
that shares its signatures and models. -/
def obsFunctor : Sig D ⥤ Room.{0, 0, 0} where
  obj S := obsRoom A S.N
  map σ := ⟨Obs.rename σ.map, Model.reduct σ.map, fun _ _ => Iff.rfl⟩
  map_id _ := Room.hom_ext rfl rfl
  map_comp _ _ := Room.hom_ext rfl rfl

/-- The institution of derivability assertions, bundled. -/
def obsInst : Inst.{1, 0, 0, 0, 0} := ⟨Sig D, obsFunctor A D⟩

/-- **The inclusion of derivability assertions into the grammar institution**: sentences embed
by `Obs.toSen`, models are shared. -/
def obsInclusion : obsFunctor A D ⟶ functor A D where
  app _ := ⟨Obs.toSen, 𝟭 _, fun _ _ => Iff.rfl⟩
  naturality _ _ _ := Room.hom_ext rfl rfl

/-- Satisfaction of an assertion, unfolded. -/
theorem obsRoom_sat {N : Type} (M : Model N α) (o : Obs N α) :
    (obsRoom A N).Sat M o ↔ ∃ a, M.rel o.x o.bs a ∧ o.Q a := Iff.rfl

end ObsInstitution

section CoHom

variable {A : Attr α} {B : Attr β} (D : Type)

/-- **The comorphism induced by an attribute map** `g : α → β`, from the assertions over `B` to
the assertions over `A`. Signatures are unchanged. A property `Q` of `β`-attributes becomes
`Q ∘ g`. An `α`-model becomes its image. The satisfaction condition holds for every `g`. -/
def obsCoHom (g : α → β) : Inst.CoHom (obsInst B D) (obsInst A D) where
  Φ := 𝟭 _
  ρ :=
    { app _ := ⟨Obs.comap g, Model.image g, fun M o => by
        show (∃ a, M.rel o.x o.bs a ∧ o.Q (g a)) ↔ ∃ b, (∃ a, M.rel o.x o.bs a ∧ g a = b) ∧ o.Q b
        constructor
        · rintro ⟨a, ha, hQ⟩
          exact ⟨g a, ⟨a, ha, rfl⟩, hQ⟩
        · rintro ⟨_, ⟨a, ha, rfl⟩, hQ⟩
          exact ⟨a, ha, hQ⟩⟩
      naturality _ _ _ := Room.hom_ext rfl rfl }

/-- **The comorphism of a homomorphism is conservative between a grammar's theory and its
translation**: the translated grammar entails an assertion iff the original grammar entails the
assertion's translation. -/
theorem obsCoHom_conservative (f : AttrHom A B) (P : N → List (Sym N α)) (o : Obs N β) :
    (room B N).Entails (prodAxioms (mapProds f P)) o.toSen ↔
      (room A N).Entails (prodAxioms P) (o.comap f.toFun).toSen :=
  entails_map_iff f P (.nt o.x) o.bs o.Q

end CoHom

end Silmaril.Wasm.SpecTec.GrammarInst
