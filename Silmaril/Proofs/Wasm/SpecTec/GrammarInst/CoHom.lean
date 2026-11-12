module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.LebHom
public import Silmaril.Logic.Institution.Borrowing

/-!
# The full comorphism of grammar institutions along an attribute homomorphism

`Hom.lean` translates grammars along an attribute-algebra homomorphism `f : AttrHom A B` and gives
a comorphism only of the sub-institutions of derivability assertions (`obsCoHom`). Here the
translation covers **every sentence, productions included**.

* **Every homomorphism is injective** (`AttrHom.injective`). `map_act` must hold for every
  partial action, and an action that separates two attributes with the same image would have
  two different translations at that image.
* **Sentences** go by `mapSen f`. A production `x ::= g` goes to `x ::= mapSym f g`. An
  assertion `derives g bs P` goes to `derives (mapSym f g) bs (f '' P)`. The translation commutes
  with renamings (`mapSen_rename`).
* **Models** go by preimage (`Model.comap f`): an `A`-model reads `x` at `a` as the target model
  reads `x` at `f a`.
* **The target** is `instIn f D`, the sub-institution of `inst B D` whose models are supported on
  the image of `f` (`Supported`): sentences and satisfaction are those of `inst B D`. Reducts keep
  support, so this is an institution.
* **The satisfaction condition** is `holds_mapSen_iff`: on a supported model `I'`,
  `(mapSen f φ).Holds B I' ↔ φ.Holds A (comap I')`, for productions and assertions alike.
  `fullCoHom f : Inst.CoHom (inst A D) (instIn f D)` packages it.
* **Borrowing.** The comorphism is model-expansive (`fullCoHom_modelExpansive`: the image of an
  `A`-model is supported and its preimage is the model again), so it preserves and reflects
  consequence (`fullCoHom_entails_iff`).
* **Into the whole of `inst B D`.** The same translation is a comorphism into `inst B D` exactly
  when `f` is surjective: `fullCoHomSurj` when it is, and `surjective_of_prod_satisfaction` for
  the converse (a model with an attribute outside the image breaks the satisfaction condition at
  the production `x ::= x x`). With injectivity, such an `f` is a bijection.

`lebHom : AttrHom lebAlg actAlg` is not surjective (`lebHom_not_surjective`). Its full comorphism
`lebCoHom` therefore lands in the actions-emitting-numerals part of `inst actAlg` (`instIn`), not
in `inst actAlg` itself.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory
open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

variable {N α β : Type}

/-! ## Homomorphisms are injective -/

/-- **Every attribute-algebra homomorphism is injective.** Two attributes with the same image are
separated by the action that keeps the first and rejects everything else; `map_act` would give
that action two different translations at the common image. -/
theorem AttrHom.injective {A : Attr α} {B : Attr β} (f : AttrHom A B) :
    Function.Injective f.toFun := by
  classical
  intro a a' h
  let k : α → Option α := fun x => if x = a then some x else none
  have h₁ : f.act k (f.toFun a) = some (f.toFun a) := by
    rw [f.map_act]
    simp [k]
  have h₂ : f.act k (f.toFun a') = (k a').map f.toFun := f.map_act k a'
  rw [← h, h₁] at h₂
  by_contra hne
  have hk : k a' = none := by simp [k, Ne.symm hne]
  rw [hk] at h₂
  exact absurd h₂ (by simp)

/-! ## Sentence translation -/

section MapSen

variable {A : Attr α} {B : Attr β} (f : AttrHom A B)

/-- The image of a property of attributes. -/
def imageP (P : α → Prop) : β → Prop := fun b => ∃ a, f.toFun a = b ∧ P a

/-- **Sentence translation along a homomorphism**: productions by `mapSym`, assertions by
`mapSym` and the image of the property. -/
def mapSen : Sen N α → Sen N β
  | .prod x g => .prod x (mapSym f g)
  | .derives g bs P => .derives (mapSym f g) bs (imageP f P)

variable {N' : Type}

mutual

/-- Translating attributes commutes with renaming nonterminals. -/
theorem mapSym_rename (σ : N → N') :
    ∀ g : Sym N α, mapSym f (renameSym σ g) = renameSym σ (mapSym f g)
  | .eps => rfl
  | .byte _ => rfl
  | .range _ _ => rfl
  | .bytes _ => rfl
  | .nt _ => rfl
  | .seq gs => congrArg Sym.seq (mapSyms_rename σ gs)
  | .alt gs => congrArg Sym.alt (mapSyms_rename σ gs)
  | .star g => congrArg Sym.star (mapSym_rename σ g)
  | .plus g => congrArg Sym.plus (mapSym_rename σ g)
  | .opt g => congrArg Sym.opt (mapSym_rename σ g)
  | .count g k => congrArg (Sym.count · k) (mapSym_rename σ g)
  | .attr h g => congrArg (Sym.attr (f.act h)) (mapSym_rename σ g)

/-- `mapSym_rename` on lists. -/
theorem mapSyms_rename (σ : N → N') :
    ∀ gs : List (Sym N α), mapSyms f (renameSyms σ gs) = renameSyms σ (mapSyms f gs)
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (mapSym_rename σ g) (mapSyms_rename σ gs)

end

/-- **Sentence translation is natural** in renamings of nonterminals. -/
theorem mapSen_rename (σ : N → N') (φ : Sen N α) :
    mapSen f (φ.rename σ) = (mapSen f φ).rename σ := by
  cases φ with
  | prod x g => exact congrArg (Sen.prod (σ x)) (mapSym_rename f σ g)
  | derives g bs P => exact congrArg (Sen.derives · bs (imageP f P)) (mapSym_rename f σ g)

/-- The translated theory of a production table is the theory of the translated table. -/
theorem image_prodAxioms (P : N → List (Sym N α)) :
    mapSen f '' prodAxioms P = prodAxioms (mapProds f P) := by
  ext φ
  constructor
  · rintro ⟨_, ⟨x, g, hg, rfl⟩, rfl⟩
    exact ⟨x, mapSym f g, List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨x, g', hg', rfl⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨.prod x g, ⟨x, g, hg, rfl⟩, rfl⟩

end MapSen

/-! ## Models: preimages and supported models -/

section Models

/-- The preimage of an interpretation along an attribute map. -/
def comapRel (g : α → β) (I : N → EncRel Bytes β) : N → EncRel Bytes α :=
  fun x bs a => I x bs (g a)

/-- The preimage of a model, as a functor. -/
def Model.comap (g : α → β) : Model N β ⥤ Model N α where
  obj I := ⟨comapRel g I.rel⟩
  map h := ⟨fun x bs a hx => h.down x bs (g a) hx⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A model is **supported** on the image of `g` when every attribute it relates is an image. -/
def Supported (g : α → β) (I : Model N β) : Prop := ∀ x bs b, I.rel x bs b → ∃ a, g a = b

/-- The models supported on the image of `g`. -/
def SModel (g : α → β) (N : Type) : Type := {I : Model N β // Supported g I}

instance (g : α → β) (N : Type) : Category.{0} (SModel g N) where
  Hom I J := I.1 ⟶ J.1
  id I := 𝟙 I.1
  comp h k := h ≫ k
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct of a supported model along a renaming is supported. -/
def SModel.reduct (g : α → β) {N' : Type} (σ : N → N') : SModel g N' ⥤ SModel g N where
  obj I := ⟨(Model.reduct σ).obj I.1, fun x bs b h => I.2 (σ x) bs b h⟩
  map h := (Model.reduct σ).map h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The preimage of a supported model. -/
def SModel.comap (g : α → β) : SModel g N ⥤ Model N α where
  obj I := (Model.comap g).obj I.1
  map h := (Model.comap g).map h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The image of a model is supported. -/
def SModel.image (g : α → β) : Model N α ⥤ SModel g N where
  obj I := ⟨(Model.image g).obj I, fun _ _ _ ⟨a, _, ha⟩ => ⟨a, ha⟩⟩
  map h := (Model.image g).map h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A supported model is the image of its preimage.** -/
theorem image_comapRel {g : α → β} {I : N → EncRel Bytes β}
    (hI : ∀ x bs b, I x bs b → ∃ a, g a = b) :
    (fun x => EncRel.map g (comapRel g I x)) = I := by
  funext x
  ext bs b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hb
    obtain ⟨a, rfl⟩ := hI x bs b hb
    exact ⟨a, hb, rfl⟩

/-- **For an injective map the preimage of the image is the model.** -/
theorem comapRel_image {g : α → β} (hg : Function.Injective g) (I : N → EncRel Bytes α) :
    comapRel g (fun x => EncRel.map g (I x)) = I := by
  funext x
  ext bs a
  constructor
  · rintro ⟨a', ha', he⟩
    exact hg he ▸ ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

end Models

/-! ## The satisfaction condition -/

section Satisfaction

variable {A : Attr α} {B : Attr β} (f : AttrHom A B)

/-- On a supported model, interpreting a translated symbol is the image of interpreting the
symbol in the preimage. -/
theorem interp_mapSym_supported {I : N → EncRel Bytes β}
    (hI : ∀ x bs b, I x bs b → ∃ a, f.toFun a = b) (g : Sym N α) :
    interp B I (mapSym f g) = EncRel.map f.toFun (interp A (comapRel f.toFun I) g) := by
  conv_lhs => rw [← image_comapRel hI]
  exact interp_map f (comapRel f.toFun I) g

/-- A production translated along `f` holds in a supported model iff the production holds in the
preimage. -/
theorem holds_mapSen_prod_iff {I : N → EncRel Bytes β}
    (hI : ∀ x bs b, I x bs b → ∃ a, f.toFun a = b) (x : N) (g : Sym N α) :
    (mapSen f (.prod x g)).Holds B I ↔ (Sen.prod x g).Holds A (comapRel f.toFun I) := by
  show interp B I (mapSym f g) ≤ I x ↔ interp A (comapRel f.toFun I) g ≤ comapRel f.toFun I x
  rw [interp_mapSym_supported f hI]
  constructor
  · intro h bs a ha
    exact h bs (f.toFun a) ⟨a, ha, rfl⟩
  · rintro h bs _ ⟨a, ha, rfl⟩
    exact h bs a ha

/-- A derivability assertion translated along `f` holds in a supported model iff it holds in the
preimage. This direction uses injectivity. -/
theorem holds_mapSen_derives_iff {I : N → EncRel Bytes β}
    (hI : ∀ x bs b, I x bs b → ∃ a, f.toFun a = b) (g : Sym N α) (bs : Bytes) (P : α → Prop) :
    (mapSen f (.derives g bs P)).Holds B I ↔
      (Sen.derives g bs P).Holds A (comapRel f.toFun I) := by
  show (∃ b, interp B I (mapSym f g) bs b ∧ imageP f P b) ↔
    ∃ a, interp A (comapRel f.toFun I) g bs a ∧ P a
  rw [interp_mapSym_supported f hI]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, a', he, hP⟩
    exact ⟨a, ha, f.injective he ▸ hP⟩
  · rintro ⟨a, ha, hP⟩
    exact ⟨f.toFun a, ⟨a, ha, rfl⟩, a, rfl, hP⟩

/-- **The satisfaction condition of the full comorphism**: every sentence, production or
assertion, translated along `f`, holds in a supported model iff it holds in the preimage. -/
theorem holds_mapSen_iff {I : N → EncRel Bytes β}
    (hI : ∀ x bs b, I x bs b → ∃ a, f.toFun a = b) (φ : Sen N α) :
    (mapSen f φ).Holds B I ↔ φ.Holds A (comapRel f.toFun I) := by
  cases φ with
  | prod x g => exact holds_mapSen_prod_iff f hI x g
  | derives g bs P => exact holds_mapSen_derives_iff f hI g bs P

/-- **Every homomorphism is a semi-comorphism on productions into all of `inst B`**: if a model,
supported or not, satisfies the translated production, its preimage satisfies the production. -/
theorem holds_of_holds_mapSen_prod (I : N → EncRel Bytes β) (x : N) (g : Sym N α)
    (h : (mapSen f (.prod x g)).Holds B I) : (Sen.prod x g).Holds A (comapRel f.toFun I) := by
  intro bs a ha
  have himg : interp B (fun y => EncRel.map f.toFun (comapRel f.toFun I y)) (mapSym f g) bs
      (f.toFun a) := by
    rw [interp_map]
    exact ⟨a, ha, rfl⟩
  have hle : ∀ y, EncRel.map f.toFun (comapRel f.toFun I y) ≤ I y := by
    rintro y bs' _ ⟨a', ha', rfl⟩
    exact ha'
  exact h bs (f.toFun a) (interp_mono B hle (mapSym f g) bs (f.toFun a) himg)

end Satisfaction

/-! ## The institution of supported models and the comorphism -/

section Inst

variable {A : Attr α} {B : Attr β}

/-- The room of `B`-grammars over `N` with models supported on the image of `g`. -/
def sroom (B : Attr β) (g : α → β) (N : Type) : Room.{0, 0, 0} :=
  ⟨Sen N β, Cat.of (SModel g N), fun M φ => φ.Holds B M.1.rel⟩

/-- The corridor of a renaming in `sroom`. -/
def scorridor (B : Attr β) (g : α → β) {N N' : Type} (σ : N → N') :
    sroom B g N ⟶ sroom B g N' :=
  ⟨Sen.rename σ, SModel.reduct g σ, fun M φ => Sen.holds_rename B M.1.rel σ φ⟩

/-- **The sub-institution of `inst B D` with models supported on the image of `g`.** -/
def sfunctor (B : Attr β) (g : α → β) (D : Type) : Sig D ⥤ Room.{0, 0, 0} where
  obj S := sroom B g S.N
  map σ := scorridor B g σ.map
  map_id _ := Room.hom_ext Sen.rename_id rfl
  map_comp σ τ := Room.hom_ext (Sen.rename_comp σ.map τ.map) rfl

/-- `instIn B g D`, bundled. -/
def instIn (B : Attr β) (g : α → β) (D : Type) : Inst.{1, 0, 0, 0, 0} := ⟨Sig D, sfunctor B g D⟩

/-- `instIn B g D` is a sub-institution of `inst B D`: the institution morphism that keeps
sentences and forgets support. -/
def instInForget (B : Attr β) (g : α → β) (D : Type) : Inst.Hom (instIn B g D) (inst B D) where
  Φ := 𝟭 _
  η :=
    { app _ := ⟨id, { obj := fun M => M.1, map := fun h => h }, fun _ _ => Iff.rfl⟩
      naturality _ _ _ := Room.hom_ext rfl rfl }

variable (f : AttrHom A B) (D : Type)

/-- The corridor of the full comorphism at the nonterminals `N`. -/
def fullCorridor (N : Type) : room A N ⟶ sroom B f.toFun N :=
  ⟨mapSen f, SModel.comap f.toFun, fun M φ => holds_mapSen_iff f M.2 φ⟩

/-- **The full comorphism of grammar institutions along a homomorphism** `f : AttrHom A B`, into
the `B`-grammars with models supported on the image of `f`. Signatures are unchanged, every
sentence (productions included) is translated by `mapSen f`, and models go by preimage. -/
def fullCoHom : Inst.CoHom (inst A D) (instIn B f.toFun D) where
  Φ := 𝟭 _
  ρ :=
    { app S := fullCorridor f S.N
      naturality _ _ σ := Room.hom_ext (funext fun φ => mapSen_rename f σ.map φ) rfl }

/-- The satisfaction condition of `fullCoHom`, as the generic comorphism statement. -/
theorem fullCoHom_satisfaction (S : Sig D) (M : SModel f.toFun S.N) (φ : Sen S.N α) :
    (mapSen f φ).Holds B M.1.rel ↔ φ.Holds A (comapRel f.toFun M.1.rel) :=
  (fullCoHom f D).satisfaction S M φ

/-- **The full comorphism is model-expansive**: every `A`-model is the preimage of its image. -/
theorem fullCoHom_modelExpansive : (fullCoHom f D).ModelExpansive := by
  intro S M
  refine ⟨(SModel.image f.toFun).obj M, ?_⟩
  show (⟨comapRel f.toFun (fun x => EncRel.map f.toFun (M.rel x))⟩ : Model S.N α) = M
  rw [comapRel_image f.injective]
  rfl

/-- **Borrowing along the full comorphism**: a set of `A`-sentences entails a sentence iff their
translations do, over the models supported on the image of `f`. -/
theorem fullCoHom_entails_iff {N : Type} (Γ : Set (Sen N α)) (φ : Sen N α) :
    (room A N).Entails Γ φ ↔ (sroom B f.toFun N).Entails (mapSen f '' Γ) (mapSen f φ) :=
  (fullCoHom f Unit).entails_iff (fullCoHom_modelExpansive f Unit) ⟨N, fun _ => ()⟩ Γ φ

/-- Borrowing for a grammar's theory: `P ⊨ φ` iff the translated table entails the translated
sentence over supported models. -/
theorem fullCoHom_prodAxioms_iff {N : Type} (P : N → List (Sym N α)) (φ : Sen N α) :
    (room A N).Entails (prodAxioms P) φ ↔
      (sroom B f.toFun N).Entails (prodAxioms (mapProds f P)) (mapSen f φ) := by
  rw [fullCoHom_entails_iff f]
  erw [image_prodAxioms]

/-! ### Into the whole of `inst B D`: exactly for surjective homomorphisms -/

/-- With `f` surjective, the preimage functor on all `B`-models. -/
def fullCorridorSurj (hs : Function.Surjective f.toFun) (N : Type) : room A N ⟶ room B N :=
  ⟨mapSen f, Model.comap f.toFun, fun _ φ =>
    holds_mapSen_iff f (fun _ _ b _ => hs b) φ⟩

/-- **For a surjective (hence bijective) homomorphism, the full comorphism lands in `inst B D`.** -/
def fullCoHomSurj (hs : Function.Surjective f.toFun) : Inst.CoHom (inst A D) (inst B D) where
  Φ := 𝟭 _
  ρ :=
    { app S := fullCorridorSurj f hs S.N
      naturality _ _ σ := Room.hom_ext (funext fun φ => mapSen_rename f σ.map φ) rfl }

/-- **Surjectivity is necessary**: if the preimage satisfies the satisfaction condition for
`inst B` at every production, over some nonterminal, then `f` is surjective. A model relating `x`
only to `[0]` and an attribute `b` outside the image falsifies `x ::= x x`, while its preimage is
empty and satisfies it. -/
theorem surjective_of_prod_satisfaction (x : N)
    (h : ∀ (I : N → EncRel Bytes β) (y : N) (g : Sym N α),
      (mapSen f (.prod y g)).Holds B I ↔ (Sen.prod y g).Holds A (comapRel f.toFun I)) :
    Function.Surjective f.toFun := by
  intro b
  by_contra hb
  push Not at hb
  let I : N → EncRel Bytes β := fun _ bs b' => bs = [0] ∧ b' = b
  let g : Sym N α := .seq [.nt x, .nt x]
  have hsrc : (Sen.prod x g).Holds A (comapRel f.toFun I) := by
    rintro bs a ⟨b₁, a₁, _, _, ⟨_, ha₁⟩, _, _, _⟩
    exact (hb a₁ ha₁).elim
  have htgt : (mapSen f (.prod x g)).Holds B I := (h I x g).mpr hsrc
  have hmem : interp B I (mapSym f g) [0, 0] (B.app b (B.app b B.nil)) :=
    ⟨[0], b, [0], B.app b B.nil, ⟨rfl, rfl⟩,
      ⟨[0], b, [], B.nil, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
  have hx := htgt [0, 0] _ hmem
  exact absurd hx.1 (by decide)

end Inst

/-! ## The instance `lebHom` -/

open Silmaril.SpecTec.Sem in
/-- `lebHom` is not surjective: the empty action emits nothing, while every `lebAct l` emits
`l`. So `lebCoHom` lands in `instIn`, not in all of `inst actAlg`. -/
theorem lebHom_not_surjective : ¬ Function.Surjective lebHom.toFun := by
  intro hs
  obtain ⟨l, hl⟩ := hs (fun _ _ _ => False)
  have h : lebAct l VarEnv.empty (l.map Silmaril.SpecTec.Equiv.natV) VarEnv.empty := ⟨rfl, rfl⟩
  have h' : lebHom.toFun l = lebAct l := rfl
  rw [← h', hl] at h
  exact h

/-- **The full comorphism of `lebHom`**: the grammar institution over `lebAlg`, productions
included, into the `actAlg` grammars whose models only relate actions that emit numerals. -/
noncomputable def lebCoHom (D : Type) :
    Inst.CoHom (inst lebAlg D) (instIn Silmaril.SpecTec.Sem.actAlg lebHom.toFun D) :=
  fullCoHom lebHom D

end Silmaril.Wasm.SpecTec.GrammarInst
