module

public import Silmaril.Compile.Category.Compiler.Defs

@[expose] public section

namespace Silmaril.Proofs.Compile.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Compile.Category.Compiler

universe u

namespace Compiler

variable {L L' L'' L''' : Language.{u}}

theorem id_comp (C : Compiler L L') : (Silmaril.Compile.Category.Compiler.id L).comp C = C :=
  Compiler.ext (Category.id_comp _) rfl

theorem comp_id (C : Compiler L L') : C.comp (Silmaril.Compile.Category.Compiler.id L') = C := by
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

theorem graph_id (L : Language.{u}) : (Silmaril.Compile.Category.Compiler.id L).graph = CompRel.id L :=
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

end Silmaril.Proofs.Compile.Category
