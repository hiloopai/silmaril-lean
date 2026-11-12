module

public import Silmaril.Libc.Contract.Spec.Defs
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The category of library invariants, its separating product, and framed contracts

The concrete level: a library's state lives in a memory `Mem Addr Val := Addr → Val` (byte
addresses and bytes for an ELF; any addresses and values).

**An invariant object** `I : InvObj Addr Val` is a triple

* `G`: the ghost abstract state (the invariant interface a contract speaks about);
* `own g`: the **owned regions** in the abstract state `g` (the allocator's metadata and free
  memory, a `FILE`'s buffer), which no other code may touch;
* `inv g m`: the **invariant** relating the memory to the abstract state, which depends on the
  owned regions only (`frame`: memories that agree on `own g` satisfy the same invariant).

**A morphism** `I ⟶ J` (`InvObj.Hom`) is a refinement / projection `Inv_big ⊢ Inv_small ∗ Rest`: a
ghost map `proj : I.G → J.G` with `I.inv g m → J.inv (proj g) m` and `J.own (proj g) ⊆ I.own g`
(the rest of `I`'s regions is the frame `Rest`). Invariant objects and these morphisms form a
category.

**The separating product** `I ⊗ J` (`InvObj.tensor`) of the invariants of two disjoint modules: the
product of the ghost states, the union of the regions, both invariants and **disjoint owned
regions** (the separating conjunction, footprint-style). With the empty invariant `unit` and the
associators and unitors that reshuffle ghost pairs, it is a monoidal category
(`instMonoidalCategory`, Mathlib's `MonoidalCategory`); the unit is terminal (`toUnit`), so there
are projections `fst : I ⊗ J ⟶ I`, `snd : I ⊗ J ⟶ J` (semicartesian, not cartesian: two
morphisms into `I` and `J` do not pair unless their regions are disjoint).

**The setup obligation** `I.Establishes start g0`: every valid start memory satisfies the
invariant at the initial abstract state `g0`.

**A memory-level library** `CLib A F Addr Val` (the functions `F`): its valid start memories, the
**scratch** region of a call (its own stack: memory below the caller's stack pointer, which a call
may clobber), and the outcomes of each call on the memory. `CLib.HoldsIn L I C`: **the contract
`C` holds relative to the invariant object `I`, under the frame convention**: a call may change
only its own scratch and the regions the invariant owns before or after it
(`own g ∪ own g' ∪ scratch m`); any other memory, in particular the client's, is unchanged.
`Thms.HoldsIn.holds`: such a library, as a model (`CLib.toModel`), meets `C` in the institution;
`Thms.HoldsIn.tensor`: two libraries with disjoint functions whose invariants stay in disjoint
reserved regions (`D₁`, `D₂`) and whose scratch avoids the other's reservation together meet the
tensor contract relative to the separating product.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory MonoidalCategory

/-- Memory. -/
abbrev Mem (Addr Val : Type) : Type := Addr → Val

/-- Two address sets are apart. -/
def Sep {Addr : Type} (X Y : Set Addr) : Prop := ∀ a, a ∈ X → a ∉ Y

/-- **An invariant object**: a ghost state, the regions owned in each ghost state, an invariant
that depends on the owned regions only. -/
structure InvObj (Addr Val : Type) : Type 1 where
  /-- The ghost abstract state. -/
  G : Type
  /-- The owned regions in an abstract state. -/
  own : G → Set Addr
  /-- The invariant. -/
  inv : G → Mem Addr Val → Prop
  /-- The invariant depends on the owned regions only. -/
  frame : ∀ g m m', inv g m → (∀ a ∈ own g, m a = m' a) → inv g m'

namespace InvObj

variable {Addr Val : Type}

/-- **A morphism of invariants** `I ⟶ J`: `I ⊢ J ∗ Rest` along a ghost map. -/
structure Hom (I J : InvObj Addr Val) : Type where
  /-- The ghost map. -/
  proj : I.G → J.G
  /-- The bigger invariant entails the smaller one. -/
  entails : ∀ g m, I.inv g m → J.inv (proj g) m
  /-- The smaller invariant owns less. -/
  own_le : ∀ g, J.own (proj g) ⊆ I.own g

theorem Hom.ext' {I J : InvObj Addr Val} {f g : Hom I J} (h : f.proj = g.proj) : f = g := by
  cases f; cases g; cases h; rfl

/-- The identity morphism. -/
def Hom.id (I : InvObj Addr Val) : Hom I I := ⟨fun g => g, fun _ _ h => h, fun _ _ h => h⟩

/-- Composition. -/
def Hom.comp {I J K : InvObj Addr Val} (f : Hom I J) (g : Hom J K) : Hom I K :=
  ⟨fun x => g.proj (f.proj x), fun x m h => g.entails _ m (f.entails x m h),
    fun x _ ha => f.own_le x (g.own_le _ ha)⟩

instance : Category (InvObj Addr Val) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext' rfl
  comp_id _ := Hom.ext' rfl
  assoc _ _ _ := Hom.ext' rfl

/-- Morphisms of the category are determined by their ghost maps. -/
theorem hom_ext {I J : InvObj Addr Val} {f g : I ⟶ J} (h : Hom.proj f = Hom.proj g) : f = g :=
  Hom.ext' h

/-! ## The separating product -/

/-- **The separating product**: both invariants, on disjoint owned regions. -/
def tensor (I J : InvObj Addr Val) : InvObj Addr Val where
  G := I.G × J.G
  own g := I.own g.1 ∪ J.own g.2
  inv g m := I.inv g.1 m ∧ J.inv g.2 m ∧ Sep (I.own g.1) (J.own g.2)
  frame _ _ _ h he :=
    ⟨I.frame _ _ _ h.1 fun a ha => he a (Or.inl ha),
      J.frame _ _ _ h.2.1 fun a ha => he a (Or.inr ha), h.2.2⟩

/-- **The empty invariant**: no state, no region. -/
def unit : InvObj Addr Val := ⟨Unit, fun _ => ∅, fun _ _ => True, fun _ _ _ _ _ => trivial⟩

/-- The product of morphisms. -/
def tensorHom {I I' J J' : InvObj Addr Val} (f : Hom I I') (g : Hom J J') :
    Hom (tensor I J) (tensor I' J') :=
  ⟨fun x => (f.proj x.1, g.proj x.2),
    fun _ _ h => ⟨f.entails _ _ h.1, g.entails _ _ h.2.1,
      fun a ha hb => h.2.2 a (f.own_le _ ha) (g.own_le _ hb)⟩,
    fun _ _ ha => ha.elim (fun h => Or.inl (f.own_le _ h)) (fun h => Or.inr (g.own_le _ h))⟩

/-- The associator. -/
def assoc (I J K : InvObj Addr Val) : tensor (tensor I J) K ≅ tensor I (tensor J K) where
  hom := ⟨fun x => (x.1.1, (x.1.2, x.2)),
    fun _ _ h => ⟨h.1.1, ⟨h.1.2.1, h.2.1, fun a ha hb => h.2.2 a (Or.inr ha) hb⟩,
      fun a ha hb => hb.elim (fun hb => h.1.2.2 a ha hb) (fun hb => h.2.2 a (Or.inl ha) hb)⟩,
    fun _ _ ha => ha.elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr h))⟩
  inv := ⟨fun x => ((x.1, x.2.1), x.2.2),
    fun _ _ h => ⟨⟨h.1, h.2.1.1, fun a ha hb => h.2.2 a ha (Or.inl hb)⟩, h.2.1.2.1,
      fun a ha hb => ha.elim (fun ha => h.2.2 a ha (Or.inr hb)) (fun ha => h.2.1.2.2 a ha hb)⟩,
    fun _ _ ha => ha.elim (fun h => h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr h))⟩
  hom_inv_id := Hom.ext' rfl
  inv_hom_id := Hom.ext' rfl

/-- The left unitor. -/
def leftUnit (I : InvObj Addr Val) : tensor unit I ≅ I where
  hom := ⟨fun x => x.2, fun _ _ h => h.2.1, fun _ _ ha => Or.inr ha⟩
  inv := ⟨fun x => ((), x), fun _ _ h => ⟨trivial, h, fun _ ha => False.elim ha⟩,
    fun _ _ ha => ha.elim (fun h => False.elim h) id⟩
  hom_inv_id := Hom.ext' rfl
  inv_hom_id := Hom.ext' rfl

/-- The right unitor. -/
def rightUnit (I : InvObj Addr Val) : tensor I unit ≅ I where
  hom := ⟨fun x => x.1, fun _ _ h => h.1, fun _ _ ha => Or.inl ha⟩
  inv := ⟨fun x => (x, ()), fun _ _ h => ⟨h, trivial, fun _ _ hb => False.elim hb⟩,
    fun _ _ ha => ha.elim id (fun h => False.elim h)⟩
  hom_inv_id := Hom.ext' rfl
  inv_hom_id := Hom.ext' rfl

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (InvObj Addr Val) where
  tensorObj := tensor
  whiskerLeft I _ _ f := tensorHom (Hom.id I) f
  whiskerRight f J := tensorHom f (Hom.id J)
  tensorHom f g := tensorHom f g
  tensorUnit := unit
  associator := assoc
  leftUnitor := leftUnit
  rightUnitor := rightUnit

/-- **The separating product is monoidal.** -/
instance instMonoidalCategory : MonoidalCategory (InvObj Addr Val) where
  tensorHom_def _ _ := Hom.ext' rfl
  id_tensorHom_id _ _ := Hom.ext' rfl
  tensorHom_comp_tensorHom _ _ _ _ := Hom.ext' rfl
  whiskerLeft_id _ _ := Hom.ext' rfl
  id_whiskerRight _ _ := Hom.ext' rfl
  associator_naturality _ _ _ := Hom.ext' rfl
  leftUnitor_naturality _ := Hom.ext' rfl
  rightUnitor_naturality _ := Hom.ext' rfl
  pentagon _ _ _ _ := Hom.ext' rfl
  triangle _ _ := Hom.ext' rfl

/-- **The unit is terminal**: every invariant projects onto the empty one. -/
def toUnit (I : InvObj Addr Val) : I ⟶ 𝟙_ (InvObj Addr Val) :=
  (⟨fun _ => (), fun _ _ _ => trivial, fun _ _ ha => False.elim ha⟩ : Hom I unit)

/-- The first projection of a separating product. -/
def fst (I J : InvObj Addr Val) : I ⊗ J ⟶ I :=
  (⟨fun x => x.1, fun _ _ h => h.1, fun _ _ ha => Or.inl ha⟩ : Hom (tensor I J) I)

/-- The second projection of a separating product. -/
def snd (I J : InvObj Addr Val) : I ⊗ J ⟶ J :=
  (⟨fun x => x.2, fun _ _ h => h.2.1, fun _ _ ha => Or.inr ha⟩ : Hom (tensor I J) J)

/-! ## Setup -/

/-- **The setup obligation**: every valid start memory satisfies the invariant at `g0`. -/
def Establishes (I : InvObj Addr Val) (start : Mem Addr Val → Prop) (g0 : I.G) : Prop :=
  ∀ m, start m → I.inv g0 m

instance instNonemptyTensor (I J : InvObj Addr Val) [hI : Nonempty I.G] [hJ : Nonempty J.G] :
    Nonempty (tensor I J).G :=
  let ⟨g⟩ := hI; let ⟨h⟩ := hJ; ⟨(g, h)⟩

end InvObj

/-! ## Memory-level libraries and framed contracts -/

/-- **A memory-level library** with the functions `F`: valid start memories, the scratch region
of a call (its own stack), and the outcomes of each call on the memory. -/
structure CLib (A : Api) (F : Set A.Fn) (Addr Val : Type) : Type where
  /-- Valid start memories. -/
  start : Mem Addr Val → Prop
  /-- The memory a call may clobber besides the library's own regions (its stack). -/
  scratch : Mem Addr Val → Set Addr
  /-- The outcomes of a call (`none`: a crash). -/
  step : (f : A.Fn) → f ∈ F → Mem Addr Val → A.Arg f → Option (Mem Addr Val × A.Ret f) → Prop

namespace CLib

variable {A : Api} {F F₁ F₂ : Set A.Fn} {Addr Val : Type}

/-- The library as a model of the signature `(F, G)`. -/
def toModel (L : CLib A F Addr Val) (G : Type) [Nonempty G] : Model (Sig.mk' F G) :=
  ⟨Mem Addr Val, L.start, L.step⟩

/-- **The contract `C` holds for `L` relative to the invariant object `I`, under the frame
convention**: setup, safety, correctness and preservation of the invariant, and a call changes
only its scratch and the regions owned before or after it. -/
structure HoldsIn (L : CLib A F Addr Val) (I : InvObj Addr Val) [Nonempty I.G]
    (C : Contract (Sig.mk' F I.G)) : Prop where
  init : ∀ m, L.start m → ∃ g, C.init g ∧ I.inv g m
  safe : ∀ f hf g m a, I.inv g m → C.pre f hf g a → ¬ L.step f hf m a none
  post : ∀ f hf g m a m' r, I.inv g m → C.pre f hf g a → L.step f hf m a (some (m', r)) →
    ∃ g', I.inv g' m' ∧ C.post f hf g a r g' ∧
      ∀ x, x ∉ I.own g → x ∉ I.own g' → x ∉ L.scratch m → m' x = m x

/-- **A contract read through a ghost map** `p : G' → G` (along an invariant morphism): the
same claims about the projected abstract state. -/
def _root_.Silmaril.Libc.Contracts.Contract.pull {G G' : Type} [Nonempty G] [Nonempty G']
    (p : G' → G) (C : Contract (Sig.mk' F G)) : Contract (Sig.mk' F G') where
  init g := C.init (p g)
  pre f hf g a := C.pre f hf (p g) a
  post f hf g a r h := C.post f hf (p g) a r (p h)

/-- **Two libraries side by side** on one memory: both start conditions, both scratch regions, a
call of `F₁` runs the first, any other call of `F₂` the second. -/
def tensor (L₁ : CLib A F₁ Addr Val) (L₂ : CLib A F₂ Addr Val) : CLib A (F₁ ∪ F₂) Addr Val where
  start m := L₁.start m ∧ L₂.start m
  scratch m := L₁.scratch m ∪ L₂.scratch m
  step f _ m a o := (∃ h : f ∈ F₁, L₁.step f h m a o) ∨ (f ∉ F₁ ∧ ∃ h : f ∈ F₂, L₂.step f h m a o)

end CLib

end Silmaril.Libc.Contracts
