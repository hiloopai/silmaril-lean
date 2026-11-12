module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Set.Basic

/-!
# Library signatures: exported functions and an invariant interface

A library that keeps global state (the C allocator, `stdio`, any library with a module-level
state) is seen through a **signature**:

* an **API** (`Api`): a universe of exported functions `Fn`, each with the type of its
  arguments `Arg f` and of its result `Ret f`, abstracted from the calling convention (the
  System V reading is the concrete level's business);
* a **signature** `S : Sig A`: a set of exported functions `S.F` and an **invariant interface**
  `S.G`, the type of the library's *ghost abstract state* (the live blocks of an allocator, the
  bytes written to `stdout` and the unread bytes of `stdin`). Contracts speak about `S.G` only; an
  implementation relates its own state to it by an invariant it keeps to itself.

A **signature morphism** `σ : S ⟶ T` (`Sig.Hom`) says that `T` extends `S`: every function of `S`
is in `T` (`le`), and `T`'s ghost state projects onto `S`'s (`proj`, surjective: every abstract
state of the smaller interface is seen from the bigger one). With the identity and composition
of inclusions and projections, signatures form a category (`Thms`). Inclusions with the same
ghost (`Sig.incl`) give the allocator hierarchy
`{malloc, free} ⊂ {+calloc} ⊂ {+realloc} ⊂ {+aligned_alloc, posix_memalign, malloc_usable_size}`;
the **tensor** `S ⊗ T` (`Sig.tensor`: the union of the functions, the product of the ghost
states) puts two libraries side by side, with the injections `Sig.inl`, `Sig.inr`.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory

/-- **An API**: the exported functions a family of libraries may have, each with the type of its
arguments and of its result. -/
structure Api where
  /-- The exported functions. -/
  Fn : Type
  /-- The arguments of a call of `f`. -/
  Arg : Fn → Type
  /-- The result of a call of `f`. -/
  Ret : Fn → Type

/-- **A signature**: a set of exported functions and an invariant interface, the type of the
ghost abstract state the contracts speak about (nonempty). -/
structure Sig (A : Api) : Type 1 where
  /-- The exported functions. -/
  F : Set A.Fn
  /-- The ghost abstract state (the invariant interface). -/
  G : Type
  /-- Some abstract state exists. -/
  ne : Nonempty G

namespace Sig

variable {A : Api}

/-- **A signature morphism** `S ⟶ T`: `T` has every function of `S`, and its ghost state
projects onto `S`'s, surjectively. -/
structure Hom (S T : Sig A) : Type where
  /-- Every function of `S` is a function of `T`. -/
  le : S.F ⊆ T.F
  /-- What `S` sees of `T`'s ghost state. -/
  proj : T.G → S.G
  /-- Every ghost state of `S` is seen. -/
  surj : Function.Surjective proj

/-- Morphisms are determined by their projection. -/
theorem Hom.ext' {S T : Sig A} {σ τ : Hom S T} (h : σ.proj = τ.proj) : σ = τ := by
  cases σ; cases τ; cases h; rfl

/-- The identity morphism. -/
def Hom.id (S : Sig A) : Hom S S := ⟨fun _ h => h, fun g => g, Function.surjective_id⟩

/-- Composition: inclusions compose forwards, projections backwards. -/
def Hom.comp {S T U : Sig A} (σ : Hom S T) (τ : Hom T U) : Hom S U :=
  ⟨fun _ h => τ.le (σ.le h), fun g => σ.proj (τ.proj g), σ.surj.comp τ.surj⟩

instance : Category (Sig A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext' rfl
  comp_id _ := Hom.ext' rfl
  assoc _ _ _ := Hom.ext' rfl

/-- The signature of the functions `F` with the ghost state `G`. -/
def mk' (F : Set A.Fn) (G : Type) [h : Nonempty G] : Sig A := ⟨F, G, h⟩

/-- **An inclusion** of function sets over the same ghost state. -/
def incl {F F' : Set A.Fn} {G : Type} [Nonempty G] (h : F ⊆ F') : Hom (mk' F G) (mk' F' G) :=
  ⟨h, fun g => g, Function.surjective_id⟩

/-- **The tensor** of two signatures: both sets of functions, both ghost states. -/
def tensor (S T : Sig A) : Sig A :=
  ⟨S.F ∪ T.F, S.G × T.G, let ⟨g⟩ := S.ne; let ⟨h⟩ := T.ne; ⟨(g, h)⟩⟩

/-- The left injection `S ⟶ S ⊗ T`. -/
def inl (S T : Sig A) : Hom S (tensor S T) :=
  ⟨fun _ h => Or.inl h, Prod.fst, fun g => let ⟨h⟩ := T.ne; ⟨(g, h), rfl⟩⟩

/-- The right injection `T ⟶ S ⊗ T`. -/
def inr (S T : Sig A) : Hom T (tensor S T) :=
  ⟨fun _ h => Or.inr h, Prod.snd, fun h => let ⟨g⟩ := S.ne; ⟨(g, h), rfl⟩⟩

end Sig

end Silmaril.Libc.Contracts
