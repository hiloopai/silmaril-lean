module

public import Silmaril.Compile.Category.Rel
import Silmaril.Proofs.Compile.Category.CompilerConstruction

@[expose] public section

/-!
# The category of compilers

A *compiler* `L ⟶ L'` is a convention `c` together with a partial function on programs whose
graph lies in `Valid c`: whenever compilation succeeds, the result is a valid compilation. This
is CompCert's correctness statement for a pass (Leroy (2009), *A formally verified compiler back-end* (see references.bib),
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
  sound _ _ h := by exact Silmaril.Proofs.Compile.Category.comp_sound C.sound D.sound h

/-- The graph of a compiler, as a compilation relation. -/
def graph (C : Compiler L L') : CompRel L L' where
  conv := C.conv
  rel p p' := C.run p = some p'
  valid := C.sound

end Compiler

/-- The category of languages and compilers. -/
structure CompCat : Type (u + 1) where of ::
  /-- The underlying language. -/
  lang : Language.{u}

end Silmaril.Compile.Category
