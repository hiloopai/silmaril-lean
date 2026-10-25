module

public import Silmaril.Compile.Category.Compiler.Defs
import Silmaril.Proofs.Compile.Category.Compiler

@[expose] public section

/-! # Compiler laws

Read `Compiler.Defs` for the partial translation and its correctness field.
The proofs of these laws live in `Silmaril.Proofs.Compile.Category.Compiler`.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

namespace Compiler

variable {L L' L'' L''' : Language.{u}}

theorem id_comp (C : Compiler L L') : (id L).comp C = C :=
  Silmaril.Proofs.Compile.Category.Compiler.id_comp C

theorem comp_id (C : Compiler L L') : C.comp (id L') = C :=
  Silmaril.Proofs.Compile.Category.Compiler.comp_id C

theorem assoc (C : Compiler L L') (D : Compiler L' L'') (E : Compiler L'' L''') :
    (C.comp D).comp E = C.comp (D.comp E) :=
  Silmaril.Proofs.Compile.Category.Compiler.assoc C D E

/-- Successful compilation transports the source behavior set through the convention. -/
theorem sound_beh (C : Compiler L L') {p : L.Prog} {p' : L'.Prog} (h : C.run p = some p') :
    L'.beh p' ⊆ C.conv.lift (L.beh p) :=
  Silmaril.Proofs.Compile.Category.Compiler.sound_beh C h

/-- Every specification of the source transports to a successful compilation. -/
theorem transport (C : Compiler L L') {p : L.Prog} {p' : L'.Prog} (h : C.run p = some p')
    {φ : Set L.Obs} (hp : L.Sat p φ) : L'.Sat p' (C.conv.lift φ) :=
  Silmaril.Proofs.Compile.Category.Compiler.transport C h hp

/-- A compiler at the identity convention refines the source program. -/
theorem refines (C : Compiler L L) (hC : C.conv = 𝟙 L) {p q : L.Prog}
    (h : C.run p = some q) : L.Refines p q :=
  Silmaril.Proofs.Compile.Category.Compiler.refines C hC h

/-- Successful composition is valid at the composed convention. -/
theorem compose_sound (C : Compiler L L') (D : Compiler L' L'') {p : L.Prog} {p'' : L''.Prog}
    (h : (C.comp D).run p = some p'') : Valid (C.conv ≫ D.conv) p p'' :=
  Silmaril.Proofs.Compile.Category.Compiler.compose_sound C D h

theorem graph_id (L : Language.{u}) : (id L).graph = CompRel.id L :=
  Silmaril.Proofs.Compile.Category.Compiler.graph_id L

/-- The graph construction preserves composition. -/
theorem graph_comp (C : Compiler L L') (D : Compiler L' L'') :
    (C.comp D).graph = C.graph.comp D.graph :=
  Silmaril.Proofs.Compile.Category.Compiler.graph_comp C D

/-- Composed compiler graphs lie in the direct valid-compilation relation. -/
theorem graph_comp_le_validRel (C : Compiler L L') (D : Compiler L' L'') :
    (C.comp D).graph ≤ CompRel.validRel (C.conv ≫ D.conv) :=
  Silmaril.Proofs.Compile.Category.Compiler.graph_comp_le_validRel C D

/-- The compilation graph determines the compiler. -/
theorem graph_injective : Function.Injective (graph : Compiler L L' → CompRel L L') :=
  Silmaril.Proofs.Compile.Category.Compiler.graph_injective

end Compiler

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
