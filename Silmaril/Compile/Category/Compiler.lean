module

public import Silmaril.Compile.Category.Rel

@[expose] public section

/-!
# The category of compilers

A *compiler* `L ⟶ L'` is a convention `c` together with a partial function on programs whose
graph lies in `Valid c`: whenever compilation succeeds, the result is a valid compilation. This
is CompCert's correctness statement for a pass (`papers/compilers/leroy-2009-compcert-backend.pdf`,
§2.2.1, Definition 8, p. 6: "Comp(S) = OK(C) ⇒ S ≈ C"; monadic composition of passes is its
§2.3, Theorem 2, p. 9) stated through the behavioural institutions.

Compilers compose by Kleisli composition in `Option`, at the composite convention; the lax law
makes the composite sound. Taking graphs is a functor `graphFunctor : CompCat ⥤ RelCat`, so
composing compilers gives both a valid compiler and a valid compilation relation at the
composite convention (requirement (ii): `SSA ⇒ Wasm` then `Wasm ⇒ x86` is a valid `SSA ⇒ x86`
compiler and lies below the direct valid `SSA ⇒ x86` relation).

## Main definitions

* `Compiler L L'`, `Compiler.id`, `Compiler.comp`, the category `CompCat`.
* `Compiler.graph`, `graphFunctor : CompCat ⥤ RelCat`.

## Main results

* `Compiler.sound_beh`, `Compiler.transport`, `Compiler.refines`: what a compiler guarantees.
* `Compiler.compose_sound`: composites are valid at the composite convention.
* `Compiler.graph_comp_le_validRel`: composite compilers lie in the direct valid relation.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

/-- A compiler: a convention and a partial translation of programs whose graph is valid. -/
@[ext]
structure Compiler (L L' : Language.{u}) : Type u where
  /-- The convention the compiler is correct for. -/
  conv : L ⟶ L'
  /-- The translation; `none` is a compile-time failure. -/
  run : L.Prog → Option L'.Prog
  /-- Soundness: every successful compilation is valid. -/
  sound : ∀ p p', run p = some p' → Valid conv p p'

namespace Compiler

variable {L L' L'' L''' : Language.{u}}

/-- The identity compiler. -/
def id (L : Language.{u}) : Compiler L L where
  conv := 𝟙 L
  run := some
  sound p p' h := by
    cases Option.some.inj h
    exact valid_id_refl p

/-- Kleisli composition of compilers. -/
def comp (C : Compiler L L') (D : Compiler L' L'') : Compiler L L'' where
  conv := C.conv ≫ D.conv
  run p := (C.run p).bind D.run
  sound p p'' h := by
    cases hq : C.run p with
    | none => rw [hq] at h; exact absurd h (by simp)
    | some q =>
      rw [hq] at h
      exact valid_comp_le C.conv D.conv p p'' ⟨q, C.sound p q hq, D.sound q p'' h⟩

theorem id_comp (C : Compiler L L') : (id L).comp C = C :=
  Compiler.ext (Category.id_comp _) rfl

theorem comp_id (C : Compiler L L') : C.comp (id L') = C := by
  refine Compiler.ext (Category.comp_id _) (funext fun p => ?_)
  show (C.run p).bind some = C.run p
  cases C.run p <;> rfl

theorem assoc (C : Compiler L L') (D : Compiler L' L'') (E : Compiler L'' L''') :
    (C.comp D).comp E = C.comp (D.comp E) := by
  refine Compiler.ext (Category.assoc _ _ _) (funext fun p => ?_)
  show ((C.run p).bind D.run).bind E.run = (C.run p).bind fun q => (D.run q).bind E.run
  cases C.run p <;> rfl

/-- What a compiler guarantees: target behaviours realise source behaviours through the
convention. -/
theorem sound_beh (C : Compiler L L') {p : L.Prog} {p' : L'.Prog} (h : C.run p = some p') :
    L'.beh p' ⊆ C.conv.lift (L.beh p) :=
  (C.sound p p' h).transport (φ := L.beh p) subset_rfl

/-- Specifications transport through a compiler: `p ⊨ φ → compile p ⊨' α φ`. -/
theorem transport (C : Compiler L L') {p : L.Prog} {p' : L'.Prog} (h : C.run p = some p')
    {φ : Set L.Obs} (hp : L.Sat p φ) : L'.Sat p' (C.conv.lift φ) :=
  (C.sound p p' h).transport hp

/-- An endo-compiler at the identity convention refines programs. -/
theorem refines (C : Compiler L L) (hC : C.conv = 𝟙 L) {p q : L.Prog}
    (h : C.run p = some q) : L.Refines p q := by
  have hv := C.sound p q h
  rw [hC] at hv
  exact (valid_id_iff p q).1 hv

/-- Composites of compilers are valid at the composite convention. -/
theorem compose_sound (C : Compiler L L') (D : Compiler L' L'') {p : L.Prog} {p'' : L''.Prog}
    (h : (C.comp D).run p = some p'') : Valid (C.conv ≫ D.conv) p p'' :=
  (C.comp D).sound p p'' h

/-- The graph of a compiler, as a compilation relation. -/
def graph (C : Compiler L L') : CompRel L L' where
  conv := C.conv
  rel p p' := C.run p = some p'
  valid := C.sound

theorem graph_id (L : Language.{u}) : (id L).graph = CompRel.id L :=
  CompRel.ext rfl (funext fun _ => funext fun _ => propext Option.some_inj)

/-- The graph of a composite is the composite of the graphs. -/
theorem graph_comp (C : Compiler L L') (D : Compiler L' L'') :
    (C.comp D).graph = C.graph.comp D.graph := by
  refine CompRel.ext rfl (funext fun p => funext fun r => propext ?_)
  show (C.run p).bind D.run = some r ↔ ∃ q, C.run p = some q ∧ D.run q = some r
  cases C.run p <;> simp

/-- A composite compiler lies in the direct valid relation at the composite convention. -/
theorem graph_comp_le_validRel (C : Compiler L L') (D : Compiler L' L'') :
    (C.comp D).graph ≤ CompRel.validRel (C.conv ≫ D.conv) :=
  CompRel.le_validRel _

/-- Compilers are determined by their graphs. -/
theorem graph_injective : Function.Injective (graph : Compiler L L' → CompRel L L') := by
  intro C D h
  have hr := congrArg CompRel.rel h
  refine Compiler.ext (congrArg CompRel.conv h) (funext fun p => ?_)
  have key : ∀ x, C.run p = some x ↔ D.run p = some x :=
    fun x => Iff.of_eq (congrFun (congrFun hr p) x)
  cases hC : C.run p with
  | none =>
    cases hD : D.run p with
    | none => rfl
    | some x => exact absurd ((key x).2 hD) (by simp [hC])
  | some x => exact ((key x).1 hC).symm

end Compiler

/-- The category of languages and compilers. -/
structure CompCat : Type (u + 1) where of ::
  /-- The underlying language. -/
  lang : Language.{u}

instance CompCat.category : Category.{u} CompCat.{u} where
  Hom X Y := Compiler X.lang Y.lang
  id X := Compiler.id X.lang
  comp C D := Compiler.comp C D
  id_comp := Compiler.id_comp
  comp_id := Compiler.comp_id
  assoc := Compiler.assoc

/-- The graph functor from compilers to compilation relations. It is faithful
(`Compiler.graph_injective`). -/
def graphFunctor : CompCat.{u} ⥤ RelCat.{u} where
  obj X := RelCat.of X.lang
  map C := Compiler.graph C
  map_id X := Compiler.graph_id X.lang
  map_comp C D := Compiler.graph_comp C D

end Silmaril.Compile.Category
